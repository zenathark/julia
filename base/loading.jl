# This file is a part of Julia. License is MIT: https://julialang.org/license

# Base.require is the implementation for the `import` statement

# Cross-platform case-sensitive path canonicalization

if Sys.isunix() && !Sys.isapple()
    # assume case-sensitive filesystems, don't have to do anything
    isfile_casesensitive(path) = isfile(path)
elseif Sys.iswindows()
    # GetLongPathName Win32 function returns the case-preserved filename on NTFS.
    function isfile_casesensitive(path)
        isfile(path) || return false  # Fail fast
        basename(Filesystem.longpath(path)) == basename(path)
    end
elseif Sys.isapple()
    # HFS+ filesystem is case-preserving. The getattrlist API returns
    # a case-preserved filename. In the rare event that HFS+ is operating
    # in case-sensitive mode, this will still work but will be redundant.

    # Constants from <sys/attr.h>
    const ATRATTR_BIT_MAP_COUNT = 5
    const ATTR_CMN_NAME = 1
    const BITMAPCOUNT = 1
    const COMMONATTR = 5
    const FSOPT_NOFOLLOW = 1  # Don't follow symbolic links

    const attr_list = zeros(UInt8, 24)
    attr_list[BITMAPCOUNT] = ATRATTR_BIT_MAP_COUNT
    attr_list[COMMONATTR] = ATTR_CMN_NAME

    # This essentially corresponds to the following C code:
    # attrlist attr_list;
    # memset(&attr_list, 0, sizeof(attr_list));
    # attr_list.bitmapcount = ATTR_BIT_MAP_COUNT;
    # attr_list.commonattr = ATTR_CMN_NAME;
    # struct Buffer {
    #    u_int32_t total_length;
    #    u_int32_t filename_offset;
    #    u_int32_t filename_length;
    #    char filename[max_filename_length];
    # };
    # Buffer buf;
    # getattrpath(path, &attr_list, &buf, sizeof(buf), FSOPT_NOFOLLOW);
    function isfile_casesensitive(path)
        isfile(path) || return false
        path_basename = String(basename(path))
        local casepreserved_basename
        header_size = 12
        buf = Vector{UInt8}(uninitialized, length(path_basename) + header_size + 1)
        while true
            ret = ccall(:getattrlist, Cint,
                        (Cstring, Ptr{Cvoid}, Ptr{Cvoid}, Csize_t, Culong),
                        path, attr_list, buf, sizeof(buf), FSOPT_NOFOLLOW)
            systemerror(:getattrlist, ret ≠ 0)
            filename_length = @gc_preserve buf unsafe_load(
              convert(Ptr{UInt32}, pointer(buf) + 8))
            if (filename_length + header_size) > length(buf)
                resize!(buf, filename_length + header_size)
                continue
            end
            casepreserved_basename =
              view(buf, (header_size+1):(header_size+filename_length-1))
            break
        end
        # Hack to compensate for inability to create a string from a subarray with no allocations.
        codeunits(path_basename) == casepreserved_basename && return true

        # If there is no match, it's possible that the file does exist but HFS+
        # performed unicode normalization. See  https://developer.apple.com/library/mac/qa/qa1235/_index.html.
        isascii(path_basename) && return false
        codeunits(Unicode.normalize(path_basename, :NFD)) == casepreserved_basename
    end
else
    # Generic fallback that performs a slow directory listing.
    function isfile_casesensitive(path)
        isfile(path) || return false
        dir, filename = splitdir(path)
        any(readdir(dir) .== filename)
    end
end

## SHA1 ##

struct SHA1
    bytes::Vector{UInt8}
    function SHA1(bytes::Vector{UInt8})
        length(bytes) == 20 ||
            throw(ArgumentError("wrong number of bytes for SHA1 hash: $(length(bytes))"))
        return new(bytes)
    end
end
SHA1(s::Union{String,SubString{String}}) = SHA1(hex2bytes(s))

convert(::Type{String}, hash::SHA1) = bytes2hex(convert(Vector{UInt8}, hash))
convert(::Type{Vector{UInt8}}, hash::SHA1) = hash.bytes

string(hash::SHA1) = String(hash)
show(io::IO, hash::SHA1) = print(io, "SHA1(", convert(String, hash), ")")
isless(a::SHA1, b::SHA1) = lexless(a.bytes, b.bytes)
hash(a::SHA1, h::UInt) = hash((SHA1, a.bytes), h)
==(a::SHA1, b::SHA1) = a.bytes == b.bytes

## package path slugs: turning UUID + SHA1 into a pair of 4-byte "slugs" ##

import Base.Random: UUID

const SlugInt = UInt32 # max p = 4
const chars = String(['A':'Z'; 'a':'z'; '0':'9'])
const nchars = SlugInt(length(chars))
const max_p = floor(Int, log(nchars, typemax(SlugInt) >>> 8))

function slug(x::SlugInt, p::Int)
    1 ≤ p ≤ max_p || # otherwise previous steps are wrong
        error("invalid slug size: $p (need 1 ≤ p ≤ $max_p)")
    return sprint() do io
        for i = 1:p
            x, d = divrem(x, nchars)
            write(io, chars[1+d])
        end
    end
end
slug(x::Integer, p::Int) = slug(SlugInt(x), p)

function slug(bytes::Vector{UInt8}, p::Int)
    n = nchars^p
    x = zero(SlugInt)
    for (i, b) in enumerate(bytes)
        x = (x + b*powermod(2, 8(i-1), n)) % n
    end
    slug(x, p)
end

slug(uuid::UUID, p::Int=4) = slug(uuid.value % nchars^p, p)
slug(sha1::SHA1, p::Int=4) = slug(sha1.bytes, p)

version_slug(uuid::UUID, sha1::SHA1) = joinpath(slug(uuid), slug(sha1))

## load path expansion: turn LOAD_PATH entries into concrete paths ##

function find_env(envs::Vector)
    for env in envs
        path = find_env(env)
        path != nothing && return path
    end
end

function find_env(env::AbstractString)
    path = abspath(env)
    if isdir(path)
        # directory with a project file?
        for name in project_names
            file = abspath(path, name)
            isfile_casesensitive(file) && return file
        end
    end
    # package dir or path to project file
    return path
end

function find_env(env::NamedEnv)
    # look for named env in each depot
    for depot in DEPOT_PATH
        isdir(depot) || continue
        file = nothing
        for name in project_names
            file = abspath(depot, "environments", env.name, name)
            isfile_casesensitive(file) && return file
        end
        file != nothing && env.create && return file
    end
end

function find_env(env::CurrentEnv, dir::AbstractString = pwd())
    # look for project file in current dir and parents
    home = homedir()
    while true
        for name in project_names
            file = joinpath(dir, name)
            isfile_casesensitive(file) && return file
        end
        # bail at home directory or top of git repo
        (dir == home || ispath(joinpath(dir, ".git"))) && break
        old, dir = dir, dirname(dir)
        dir == old && break
    end
end

find_env(env::Function) = find_env(env())

load_path() = filter(env -> env ≠ nothing, map(find_env, LOAD_PATH))

## package identification: determine unique identity of package to be loaded ##

find_package(args...) = locate_package(identify_package(args...))

const uuid_sym = Symbol("##uuid")

struct PkgId
    uuid::Union{UUID,Nothing}
    name::String
end
PkgId(name::AbstractString) = PkgId(nothing, name)

function PkgId(m::Module)
    uuid = isdefined(m, uuid_sym) ? getfield(m, uuid_sym) : nothing
    PkgId(uuid, String(module_name(m)))
end

==(a::PkgId, b::PkgId) = a.uuid == b.uuid && a.name == b.name

function hash(pkg::PkgId, h::UInt)
    h += 0xc9f248583a0ca36c % UInt
    h = hash(pkg.uuid, h)
    h = hash(pkg.name, h)
end

show(io::IO, pkg::PkgId) =
    print(io, pkg.name, " [", pkg.uuid === nothing ? "top-level" : pkg.uuid, "]")

function identify_package(where::Module, name::String)::Union{Nothing,PkgId}
    identify_package(PkgId(where), name)
end

function identify_package(where::PkgId, name::String)::Union{Nothing,PkgId}
    where.uuid === nothing && return identify_package(name)
    for env in load_path()
        # `where` found, `name` in deps: return its `uuid`
        # `where` found, `name` not in deps: return `nothing`
        # `where` not found: continue
        found_or_uuid = manifest_deps_get(env, where, name)
        found_or_uuid isa UUID && return PkgId(found_or_uuid, name)
        found_or_uuid && return nothing
    end
    return nothing
end

function identify_package(name::String)::Union{Nothing,PkgId}
    for env in load_path()
        uuid_or_path = project_deps_get(env, name)
        uuid_or_path isa UUID && return PkgId(uuid_or_path, name)
        uuid_or_path isa String && return PkgId(name)
        uuid_or_path :: Nothing
    end
    return nothing
end

function identify_package(name::String, names::String...)
    pkg = identify_package(name)
    pkg      === nothing ? nothing :
    pkg.uuid === nothing ? identify_package(names...) :
                           identify_package(pkg, names...)
end

function identify_package(where::PkgId, name::String, names::String...)
    pkg = identify_package(where, name)
    pkg      === nothing ? nothing :
    pkg.uuid === nothing ? identify_package(names...) :
                           identify_package(pkg, names...)
end

## package location: given a package identity find file to load ##

function locate_package(pkg::PkgId)::Union{Nothing,String}
    if pkg.uuid === nothing
        for env in load_path()
            uuid_or_path = project_deps_get(env, pkg.name)
            uuid_or_path === nothing && continue
            uuid_or_path isa String && return uuid_or_path # path
            return locate_package(PkgId(uuid_or_path::UUID, name))
        end
    else
        for env in load_path()
            path = manifest_uuid_path(env, pkg)
            path isa String && return path
            path :: Nothing
        end
    end
end
locate_package(::Nothing) = nothing

## generic project & manifest API ##

const project_names = ("JuliaProject.toml", "Project.toml")
const manifest_names = ("JuliaManifest.toml", "Manifest.toml")

function project_deps_get(env::String, name::String)::Union{Nothing,UUID,String}
    if isdir(env)
        return implicit_project_deps_get(env, name)
    elseif basename(env) in project_names && isfile_casesensitive(env)
        return explicit_project_deps_get(env, name)
    end
    return nothing
end

function manifest_deps_get(env::String, where::PkgId, name::String)::Union{Bool,UUID}
    if isdir(env)
        return implicit_manifest_deps_get(env, where, name)
    elseif basename(env) in project_names && isfile_casesensitive(env)
        env = project_file_manifest_path(env)
        if isfile_casesensitive(env)
            return explicit_manifest_deps_get(env, where.uuid, name)
        end
    end
    return false
end

function manifest_uuid_path(env::String, pkg::PkgId)::Union{Nothing,String}
    if isdir(env)
        return implicit_manifest_uuid_path(env, pkg)
    elseif basename(env) in project_names && isfile_casesensitive(env)
        env = project_file_manifest_path(env)
        if isfile_casesensitive(env)
            return explicit_manifest_uuid_path(env, pkg)
        end
    end
    return nothing
end

# regular expressions for scanning project & manifest files

const re_section            = r"^\s*\["
const re_array_of_tables    = r"^\s*\[\s*\["
const re_section_deps       = r"^\s*\[\s*\"?deps\"?\s*\]\s*(?:#|$)"
const re_section_capture    = r"^\s*\[\s*\[\s*\"?(\w+)\"?\s*\]\s*\]\s*(?:#|$)"
const re_subsection_deps    = r"^\s*\[\s*\"?(\w+)\"?\s*\.\s*\"?deps\"?\s*\]\s*(?:#|$)"
const re_key_to_string      = r"^\s*(\w+)\s*=\s*\"(.*)\"\s*(?:#|$)"
const re_uuid_to_string     = r"^\s*uuid\s*=\s*\"(.*)\"\s*(?:#|$)"
const re_path_to_string     = r"^\s*path\s*=\s*\"(.*)\"\s*(?:#|$)"
const re_hash_to_string     = r"^\s*hash-sha1\s*=\s*\"(.*)\"\s*(?:#|$)"
const re_manifest_to_string = r"^\s*manifest\s*=\s*\"(.*)\"\s*(?:#|$)"
const re_deps_to_any        = r"^\s*deps\s*=\s*(.*?)\s*(?:#|$)"

# find project file's top-level UUID entry (or nothing)
function project_file_uuid(project_file::String)::Union{Nothing,UUID}
    open(project_file) do io
        for line in eachline(io)
            contains(line, re_section) && break
            if (m = match(re_uuid_to_string, line)) != nothing
                return UUID(m.captures[1])
            end
        end
    end
end

# find project file's corresponding manifest file
function project_file_manifest_path(project_file::String)::Union{Nothing,String}
    open(project_file) do io
        dir = abspath(dirname(project_file))
        for line in eachline(io)
            contains(line, re_section) && break
            if (m = match(re_manifest_to_string, line)) != nothing
                return normpath(joinpath(dir, m.captures[1]))
            end
        end
        local manifest_file
        for mfst in manifest_names
            manifest_file = joinpath(dir, mfst)
            isfile_casesensitive(manifest_file) && return manifest_file
        end
        return manifest_file
    end
end

# find manifest file's `where` stanza's deps
function manifest_file_deps(manifest_file::AbstractString, where::UUID, io::IO)::Union{Nothing,Vector{String},Dict{String,UUID}}
    deps = nothing
    found = in_deps = false
    for line in eachline(io)
        if !in_deps
            if contains(line, re_array_of_tables)
                found && break
                deps = nothing
                found = false
            elseif (m = match(re_uuid_to_string, line)) != nothing
                found = (where == UUID(m.captures[1]))
            elseif (m = match(re_deps_to_any, line)) != nothing
                deps = String(m.captures[1])
            elseif contains(line, re_subsection_deps)
                deps = Dict{String,UUID}()
                in_deps = true
            end
        else # in_deps
            if (m = match(re_key_to_string, line)) != nothing
                deps[m.captures[1]] = UUID(m.captures[2])
            elseif contains(line, re_section)
                found && break
                in_deps = false
            end
        end
    end
    found || return nothing
    deps isa String || return deps
    # TODO: handle inline table syntax
    if deps[1] != '[' || deps[end] != ']'
        @warn "Unexpected TOML deps format:\n$deps"
        return nothing
    end
    return map(m->String(m.captures[1]), eachmatch(r"\"(.*?)\"", deps))
end

# find `name` in a manifest file and return its UUID
function manifest_file_name_uuid(manifest_file::String, name::String, io::IO)::Union{Nothing,UUID}
    uuid = name′ = nothing
    for line in eachline(io)
        if (m = match(re_section_capture, line)) != nothing
            name′ == name && break
            name′ = String(m.captures[1])
        elseif (m = match(re_uuid_to_string, line)) != nothing
            uuid = UUID(m.captures[1])
        end
    end
    name′ == name ? uuid : nothing
end

# given package dir and name, find an entry point
# and project file if one exists (or nothing if not)
function entry_point_and_project_file(dir::String, name::String)::Union{Tuple{Nothing,Nothing},Tuple{String,Nothing},Tuple{String,String}}
    for entry in ("", joinpath(name, "src"), joinpath("$name.jl", "src"))
        path = joinpath(dir, entry, "$name.jl")
        isfile_casesensitive(path) || continue
        if !isempty(entry)
            for proj in project_names
                project_file = joinpath(dir, dirname(entry), proj)
                isfile_casesensitive(project_file) || continue
                return path, project_file
            end
        end
        return path, nothing
    end
    return nothing, nothing
end

# given a path and a name, return the entry point
function entry_path(path::String, name::String)::Union{Nothing,String}
    isfile_casesensitive(path) && return path
    path = joinpath(path, "src", "$name.jl")
    isfile_casesensitive(path) ? path : nothing
end
entry_path(::Nothing, name::String) = nothing

# given a project path (project directory or entry point)
# return the project file
function package_path_to_project_file(path::String)::Union{Nothing,String}
    if !isdir(path)
        dir = dirname(path)
        basename(dir) == "src" || return nothing
        path = dirname(dir)
    end
    for proj in project_names
        project_file = joinpath(path, proj)
        isfile_casesensitive(project_file) && return project_file
    end
end

## explicit project & manifest API ##

# find project file deps section's `name => uuid | path` mapping
function explicit_project_deps_get(project_file::String, name::String)::Union{Nothing,UUID,String}
    open(project_file) do io
        for line in eachline(io)
            contains(line, re_section_deps) && break
        end
        for line in eachline(io)
            contains(line, re_section) && break
            m = match(re_key_to_string, line)
            m.captures[1] != name && continue
            uuid_or_path = m.captures[2]
            if '/' in uuid_or_path || '\\' in uuid_or_path
                return normpath(joinpath(dirname(project_file), uuid_or_path))
            else
                return UUID(uuid_or_path)
            end
        end
    end
end

# find `where` stanza and `name` in its deps and return its UUID
#  - `false` means: did not find `where`
#  - `true` means: found `where` but not `name` in its deps
#  - `uuid` means: found `where` and `name` mapped to `uuid` in its deps

function explicit_manifest_deps_get(manifest_file::String, where::UUID, name::String)::Union{Bool,UUID}
    open(manifest_file) do io
        deps = manifest_file_deps(manifest_file, where, io)
        deps == nothing && return false
        if deps isa Dict
            haskey(deps, name) || return true
            return deps[name]::UUID
        end
        deps :: Vector
        name in deps || return true
        seekstart(io) # rewind IO handle
        return manifest_file_name_uuid(manifest_file, name, io)
    end
end

# find `uuid` stanza, return the corresponding path
function explicit_manifest_uuid_path(manifest_file::String, pkg::PkgId)::Union{Nothing,String}
    open(manifest_file) do io
        uuid = name = path = hash = nothing
        for line in eachline(io)
            if (m = match(re_section_capture, line)) != nothing
                uuid == pkg.uuid && break
                name = String(m.captures[1])
                path = hash = nothing
            elseif (m = match(re_uuid_to_string, line)) != nothing
                uuid = UUID(m.captures[1])
            elseif (m = match(re_path_to_string, line)) != nothing
                path = String(m.captures[1])
            elseif (m = match(re_hash_to_string, line)) != nothing
                hash = SHA1(m.captures[1])
            end
        end
        uuid == pkg.uuid || return nothing
        name == pkg.name || return nothing # TODO: allow a mismatch?
        if path != nothing
            path = normpath(abspath(dirname(manifest_file), path))
            return entry_path(path, name)
        end
        hash == nothing && return nothing
        slug = version_slug(uuid, hash)
        for depot in DEPOT_PATH
            path = abspath(depot, "packages", slug)
            ispath(path) && return path
        end
    end
end

## implicit project & manifest API ##

# look for an entry point for `name`
# if there's a project file with UUID, return the UUID
# otherwise, return the entry point
function implicit_project_deps_get(dir::String, name::String)::Union{Nothing,UUID,String}
    path, project_file = entry_point_and_project_file(dir, name)
    project_file === nothing && return path
    explicit_project_deps_get(project_file, name)
end

# look for an entry-point for `where` by name, check that UUID matches
# if there's a project file, look up `name` in its deps and return that
# if that returns a path to a project, return the UUID of that
#  - `false` means: did not find `where`
#  - `true` means: found `where` but not `name` in its deps
#  - `uuid` means: found `where` and `name` mapped to `uuid` in its deps

function implicit_manifest_deps_get(dir::String, where::PkgId, name::String)::Union{Bool,UUID}
    @assert where.uuid !== nothing
    path, project_file = entry_point_and_project_file(dir, where.name)
    project_file === nothing && return false
    uuid = project_file_uuid(project_file)
    uuid === where.uuid || return false
    uuid_or_path = explicit_project_deps_get(project_file, name)
    uuid_or_path === nothing && return true
    uuid_or_path isa UUID && return uuid_or_path
    # found `name => path`, see if we can figure out its UUID
    project_file = package_path_to_project_file(uuid_or_path::String)
    uuid = project_file_uuid(project_file)
    uuid isa UUID ? uuid : false
end

# look for an entry-point for `pkg` and return its path if UUID matches
function implicit_manifest_uuid_path(dir::String, pkg::PkgId)::Union{Nothing,String}
    path, project_file = entry_point_and_project_file(dir, pkg.name)
    pkg.uuid === nothing && return path
    project_file === nothing && return nothing
    uuid = project_file_uuid(project_file)
    uuid == pkg.uuid ? path : nothing
end

## other code loading functionality ##

function find_source_file(path::AbstractString)
    (isabspath(path) || isfile(path)) && return path
    base_path = joinpath(Sys.BINDIR, DATAROOTDIR, "julia", "base", path)
    return isfile(base_path) ? base_path : nothing
end

function find_all_in_cache_path(pkg::PkgId)
    paths = String[]
    suffix = "$(pkg.name).ji"
    pkg.uuid !== nothing && (suffix = joinpath(slug(pkg.uuid), suffix))
    for prefix in LOAD_CACHE_PATH
        path = joinpath(prefix, suffix)
        isfile_casesensitive(path) && push!(paths, path)
    end
    return paths
end

# these return either the array of modules loaded from the path / content given
# or an Exception that describes why it couldn't be loaded
# and it reconnects the Base.Docs.META
function _include_from_serialized(path::String, depmods::Vector{Any})
    restored = ccall(:jl_restore_incremental, Any, (Cstring, Any), path, depmods)
    if !isa(restored, Exception)
        for M in restored::Vector{Any}
            M = M::Module
            if isdefined(M, Base.Docs.META)
                push!(Base.Docs.modules, M)
            end
            if module_parent(M) === M
                register_root_module(PkgId(M), M)
            end
        end
    end
    return restored
end


function _require_from_serialized(path::String)
    # loads a precompile cache file, ignoring stale_cachfile tests
    # load all of the dependent modules first
    local depmodnames
    io = open(path, "r")
    try
        isvalid_cache_header(io) || return ArgumentError("Invalid header in cache file $path.")
        depmodnames = parse_cache_header(io)[3]
        isvalid_file_crc(io) || return ArgumentError("Invalid checksum in cache file $path.")
    finally
        close(io)
    end
    ndeps = length(depmodnames)
    depmods = Vector{Any}(uninitialized, ndeps)
    for i in 1:ndeps
        modkey, build_id = depmodnames[i]
        if root_module_exists(modkey)
            M = root_module(modkey)
            if module_name(M) === modkey && module_build_id(M) === build_id
                depmods[i] = M
            end
        else
            modpath = find_package(string(modkey))
            modpath === nothing && return ErrorException("Required dependency $modkey not found in current path.")
            mod = _require_search_from_serialized(modkey, String(modpath))
            if !isa(mod, Bool)
                for M in mod::Vector{Any}
                    if module_name(M) === modkey && module_build_id(M) === build_id
                        depmods[i] = M
                        break
                    end
                end
                for callback in package_callbacks
                    invokelatest(callback, modkey)
                end
            end
        end
        isassigned(depmods, i) || return ErrorException("Required dependency $modkey failed to load from a cache file.")
    end
    # then load the file
    return _include_from_serialized(path, depmods)
end

# returns `true` if require found a precompile cache for this sourcepath, but couldn't load it
# returns `false` if the module isn't known to be precompilable
# returns the set of modules restored if the cache load succeeded
function _require_search_from_serialized(pkg::PkgId, sourcepath::String)
    paths = find_all_in_cache_path(pkg)
    for path_to_try in paths::Vector{String}
        deps = stale_cachefile(sourcepath, path_to_try)
        if deps === true
            continue
        end
        # finish loading module graph into deps
        for i in 1:length(deps)
            dep = deps[i]
            dep isa Module && continue
            modpath, modkey, build_id = dep::Tuple{String, PkgId, UInt64}
            reqmod = _require_search_from_serialized(modkey, modpath)
            if !isa(reqmod, Bool)
                for M in reqmod::Vector{Any}
                    if PkgId(M) === modkey && module_build_id(M) === build_id
                        deps[i] = M
                        break
                    end
                end
                for callback in package_callbacks
                    invokelatest(callback, modkey)
                end
            end
            if !isa(deps[i], Module)
                @debug "Required dependency $modkey failed to load from cache file for $modpath."
                continue
            end
        end
        restored = _include_from_serialized(path_to_try, deps)
        if isa(restored, Exception)
            @debug "Deserialization checks failed while attempting to load cache from $path_to_try" exception=restored
        else
            return restored
        end
    end
    return !isempty(paths)
end

# to synchronize multiple tasks trying to import/using something
const package_locks = Dict{PkgId,Condition}()

# to notify downstream consumers that a module was successfully loaded
# Callbacks take the form (mod::Symbol) -> nothing.
# WARNING: This is an experimental feature and might change later, without deprecation.
const package_callbacks = Any[]
# to notify downstream consumers that a file has been included into a particular module
# Callbacks take the form (mod::Module, filename::String) -> nothing
# WARNING: This is an experimental feature and might change later, without deprecation.
const include_callbacks = Any[]

# used to optionally track dependencies when requiring a module:
const _concrete_dependencies = Pair{PkgId,UInt64}[] # these dependency versions are "set in stone", and the process should try to avoid invalidating them
const _require_dependencies = Any[] # a list of (mod, path, mtime) tuples that are the file dependencies of the module currently being precompiled
const _track_dependencies = Ref(false) # set this to true to track the list of file dependencies
function _include_dependency(mod::Module, _path::AbstractString)
    prev = source_path(nothing)
    if prev === nothing
        path = abspath(_path)
    else
        path = joinpath(dirname(prev), _path)
    end
    if _track_dependencies[]
        push!(_require_dependencies, (PkgId(mod), normpath(path), mtime(path)))
    end
    return path, prev
end

"""
    include_dependency(path::AbstractString)

In a module, declare that the file specified by `path` (relative or absolute) is a
dependency for precompilation; that is, the module will need to be recompiled if this file
changes.

This is only needed if your module depends on a file that is not used via `include`. It has
no effect outside of compilation.
"""
function include_dependency(path::AbstractString)
    _include_dependency(Main, path)
    return nothing
end

# We throw PrecompilableError(true) when a module wants to be precompiled but isn't,
# and PrecompilableError(false) when a module doesn't want to be precompiled but is
struct PrecompilableError <: Exception
    isprecompilable::Bool
end
function show(io::IO, ex::PrecompilableError)
    if ex.isprecompilable
        print(io, "Declaring __precompile__(true) is only allowed in module files being imported.")
    else
        print(io, "Declaring __precompile__(false) is not allowed in files that are being precompiled.")
    end
end
precompilableerror(ex::PrecompilableError, c) = ex.isprecompilable == c
precompilableerror(ex::WrappedException, c) = precompilableerror(ex.error, c)
precompilableerror(ex, c) = false

# Call __precompile__ at the top of a file to force it to be precompiled (true), or
# to be prevent it from being precompiled (false).  __precompile__(true) is
# ignored except within "require" call.
"""
    __precompile__(isprecompilable::Bool=true)

Specify whether the file calling this function is precompilable. If `isprecompilable` is
`true`, then `__precompile__` throws an exception when the file is loaded by
`using`/`import`/`require` *unless* the file is being precompiled, and in a module file it
causes the module to be automatically precompiled when it is imported. Typically,
`__precompile__()` should occur before the `module` declaration in the file.

If a module or file is *not* safely precompilable, it should call `__precompile__(false)` in
order to throw an error if Julia attempts to precompile it.

`__precompile__()` should *not* be used in a module unless all of its dependencies are also
using `__precompile__()`. Failure to do so can result in a runtime error when loading the module.
"""
function __precompile__(isprecompilable::Bool=true)
    if (JLOptions().use_compiled_modules != 0 &&
        isprecompilable != (0 != ccall(:jl_generating_output, Cint, ())) &&
        !(isprecompilable && toplevel_load[]))
        throw(PrecompilableError(isprecompilable))
    end
end

# require always works in Main scope and loads files from node 1
const toplevel_load = Ref(true)

"""
    require(module::Symbol)

This function is part of the implementation of `using` / `import`, if a module is not
already defined in `Main`. It can also be called directly to force reloading a module,
regardless of whether it has been loaded before (for example, when interactively developing
libraries).

Loads a source file, in the context of the `Main` module, on every active node, searching
standard locations for files. `require` is considered a top-level operation, so it sets the
current `include` path but does not use it to search for files (see help for `include`).
This function is typically used to load library code, and is implicitly called by `using` to
load packages.

When searching for files, `require` first looks for package code under `Pkg.dir()`,
then tries paths in the global array `LOAD_PATH`. `require` is case-sensitive on
all platforms, including those with case-insensitive filesystems like macOS and
Windows.
"""
function require(into::Module, mod::Symbol)
    uuidkey = identify_package(into, String(mod))
    uuidkey === nothing &&
        throw(ArgumentError("Module $mod not found in current path.\nRun `Pkg.add(\"$mod\")` to install the $mod package."))
    if _track_dependencies[]
        push!(_require_dependencies, (into, uuidkey, 0.0))
    end
    if !root_module_exists(uuidkey)
        _require(uuidkey)
        # After successfully loading, notify downstream consumers
        for callback in package_callbacks
            invokelatest(callback, mod)
        end
    end
    return root_module(uuidkey)
end

const loaded_modules = Dict{PkgId,Module}()
const module_keys = ObjectIdDict() # the reverse

function register_root_module(key::PkgId, m::Module)
    if haskey(loaded_modules, key)
        oldm = loaded_modules[key]
        if oldm !== m
            name = module_name(oldm)
            @warn "Replacing module `$name`"
        end
    end
    loaded_modules[key] = m
    module_keys[m] = key
    nothing
end

function register_root_module(uuid::Union{Nothing,UUID}, name::Symbol, m::Module)
    register_root_module(PkgId(uuid, String(name)), m)
end

register_root_module(PkgId("Core"), Core)
register_root_module(PkgId("Base"), Base)
register_root_module(PkgId("Main"), Main)

is_root_module(m::Module) = haskey(module_keys, m)
root_module_key(m::Module) = module_keys[m]

# This is used as the current module when loading top-level modules.
# It has the special behavior that modules evaluated in it get added
# to the loaded_modules table instead of getting bindings.
baremodule __toplevel__
using Base
end

# get a top-level Module from the given key
# for now keys can only be Symbols, but that will change
root_module(key::PkgId) = loaded_modules[key]
root_module(where::Module, name::Symbol) =
    root_module(identify_package(where, String(name)))

root_module_exists(key::PkgId) = haskey(loaded_modules, key)
loaded_modules_array() = collect(values(loaded_modules))

function unreference_module(key::PkgId)
    if haskey(loaded_modules, key)
        m = pop!(loaded_modules, key)
        # need to ensure all modules are GC rooted; will still be referenced
        # in module_keys
    end
end

function _require(pkg::PkgId)
    # handle recursive calls to require
    loading = get(package_locks, pkg, false)
    if loading !== false
        # load already in progress for this module
        wait(loading)
        return
    end
    package_locks[pkg] = Condition()

    last = toplevel_load[]
    try
        toplevel_load[] = false
        # perform the search operation to select the module file require intends to load
        name = pkg.name
        path = locate_package(pkg)
        if path === nothing
            throw(ArgumentError("Module $name not found in current path.\nRun `Pkg.add(\"$name\")` to install the $name package."))
        end

        # attempt to load the module file via the precompile cache locations
        doneprecompile = false
        if JLOptions().use_compiled_modules != 0
            doneprecompile = _require_search_from_serialized(pkg, path)
            if !isa(doneprecompile, Bool)
                return
            end
        end

        # if the module being required was supposed to have a particular version
        # but it was not handled by the precompile loader, complain
        for (concrete_pkg, concrete_build_id) in _concrete_dependencies
            if pkg === concrete_pkg
                @warn """Module $name with build ID $concrete_build_id is missing from the cache.
                     This may mean module $name does not support precompilation but is imported by a module that does."""
                if JLOptions().incremental != 0
                    # during incremental precompilation, this should be fail-fast
                    throw(PrecompilableError(false))
                end
            end
        end

        if doneprecompile === true || JLOptions().incremental != 0
            # spawn off a new incremental pre-compile task for recursive `require` calls
            # or if the require search declared it was pre-compiled before (and therefore is expected to still be pre-compilable)
            cachefile = compilecache(pkg)
            m = _require_from_serialized(cachefile)
            if isa(m, Exception)
                @warn "The call to compilecache failed to create a usable precompiled cache file for module $name" exception=m
                # fall-through, TODO: disable __precompile__(true) error so that the normal include will succeed
            else
                return
            end
        end

        # just load the file normally via include
        # for unknown dependencies
        try
            Base.include_relative(__toplevel__, path, pkg.uuid)
            return
        catch ex
            if doneprecompile === true || JLOptions().use_compiled_modules == 0 || !precompilableerror(ex, true)
                rethrow() # rethrow non-precompilable=true errors
            end
            # the file requested `__precompile__`, so try to build a cache file and use that
            cachefile = compilecache(pkg)
            m = _require_from_serialized(cachefile)
            if isa(m, Exception)
                @warn """Module `$name` declares `__precompile__(true)` but `require` failed
                         to create a usable precompiled cache file""" exception=m
                # TODO: disable __precompile__(true) error and do normal include instead of error
                error("Module $name declares __precompile__(true) but require failed to create a usable precompiled cache file.")
            end
        end
    finally
        toplevel_load[] = last
        loading = pop!(package_locks, pkg)
        notify(loading, all=true)
    end
    nothing
end

# relative-path load

"""
    include_string(m::Module, code::AbstractString, filename::AbstractString="string")

Like `include`, except reads code from the given string rather than from a file.
"""
include_string(m::Module, txt::String, fname::String) =
    ccall(:jl_load_file_string, Any, (Ptr{UInt8}, Csize_t, Cstring, Any),
          txt, sizeof(txt), fname, m)

include_string(m::Module, txt::AbstractString, fname::AbstractString="string") =
    include_string(m, String(txt), String(fname))

function source_path(default::Union{AbstractString,Nothing}="")
    t = current_task()
    while true
        s = t.storage
        if s !== nothing && haskey(s, :SOURCE_PATH)
            return s[:SOURCE_PATH]
        end
        if t === t.parent
            return default
        end
        t = t.parent
    end
end

function source_dir()
    p = source_path(nothing)
    p === nothing ? pwd() : dirname(p)
end

include_relative(mod::Module, path::AbstractString, uuid::Union{Nothing,UUID}=nothing) = include_relative(mod, String(path), uuid)
function include_relative(mod::Module, _path::String, uuid::Union{Nothing,UUID}=nothing)
    path, prev = _include_dependency(mod, _path)
    for callback in include_callbacks # to preserve order, must come before Core.include
        invokelatest(callback, mod, path)
    end
    tls = task_local_storage()
    tls[:SOURCE_PATH] = path
    old_uuid = isdefined(__toplevel__, uuid_sym) ? getfield(__toplevel__, uuid_sym) : nothing
    uuid !== old_uuid &&
        ccall(:jl_set_global, Cvoid, (Any, Any, Any), __toplevel__, uuid_sym, uuid)
    local result
    try
        result = Core.include(mod, path)
    finally
        uuid !== old_uuid &&
            ccall(:jl_set_global, Cvoid, (Any, Any, Any), __toplevel__, uuid_sym, old_uuid)
        if prev === nothing
            delete!(tls, :SOURCE_PATH)
        else
            tls[:SOURCE_PATH] = prev
        end
    end
    return result
end

"""
    include(m::Module, path::AbstractString)

Evaluate the contents of the input source file into module `m`. Returns the result
of the last evaluated expression of the input file. During including, a task-local include
path is set to the directory containing the file. Nested calls to `include` will search
relative to that path. This function is typically used to load source
interactively, or to combine files in packages that are broken into multiple source files.
"""
include # defined in sysimg.jl

"""
    evalfile(path::AbstractString, args::Vector{String}=String[])

Load the file using [`include`](@ref), evaluate all expressions,
and return the value of the last one.
"""
function evalfile(path::AbstractString, args::Vector{String}=String[])
    return eval(Module(:__anon__),
                Expr(:toplevel,
                     :(const ARGS = $args),
                     :(eval(x) = $(Expr(:core, :eval))(__anon__, x)),
                     :(eval(m, x) = $(Expr(:core, :eval))(m, x)),
                     :(include(x) = $(Expr(:top, :include))(__anon__, x)),
                     :(include($path))))
end
evalfile(path::AbstractString, args::Vector) = evalfile(path, String[args...])

function create_expr_cache(input::String, output::String, concrete_deps::typeof(_concrete_dependencies), uuid::Union{Nothing,UUID})
    rm(output, force=true)   # Remove file if it exists
    code_object = """
        while !eof(STDIN)
            eval(Main, deserialize(STDIN))
        end
        """
    io = open(pipeline(detach(`$(julia_cmd()) -O0
                              --output-ji $output --output-incremental=yes
                              --startup-file=no --history-file=no --warn-overwrite=yes
                              --color=$(have_color ? "yes" : "no")
                              --eval $code_object`), stderr=STDERR),
              "w", STDOUT)
    in = io.in
    try
        serialize(in, quote
                  empty!(Base.LOAD_PATH)
                  append!(Base.LOAD_PATH, $LOAD_PATH)
                  empty!(Base.DEPOT_PATH)
                  append!(Base.DEPOT_PATH, $DEPOT_PATH)
                  empty!(Base.LOAD_CACHE_PATH)
                  append!(Base.LOAD_CACHE_PATH, $LOAD_CACHE_PATH)
                  empty!(Base.DL_LOAD_PATH)
                  append!(Base.DL_LOAD_PATH, $DL_LOAD_PATH)
                  empty!(Base._concrete_dependencies)
                  append!(Base._concrete_dependencies, $concrete_deps)
                  Base._track_dependencies[] = true
                  end)
        uuid !== nothing && serialize(in, quote
            ccall(:jl_set_global, Cvoid, (Any, Any, Any),
                  Base.__toplevel__, $(Meta.quot(uuid_sym)), $uuid)
            end)
        source = source_path(nothing)
        if source !== nothing
            serialize(in, quote
                      task_local_storage()[:SOURCE_PATH] = $(source)
                      end)
        end
        serialize(in, :(Base.include(Base.__toplevel__, $(abspath(input)))))
        # TODO: cleanup is probably unnecessary here
        if source !== nothing
            serialize(in, :(delete!(task_local_storage(), :SOURCE_PATH)))
        end
        uuid !== nothing && serialize(in, quote
            ccall(:jl_set_global, Cvoid, (Any, Any, Any),
                  Base.__toplevel__, $(Meta.quot(uuid_sym)), nothing)
            end)
        close(in)
    catch ex
        close(in)
        process_running(io) && Timer(t -> kill(io), 5.0) # wait a short time before killing the process to give it a chance to clean up on its own first
        rethrow(ex)
    end
    return io
end

compilecache(mod::Symbol) = compilecache(string(mod))

"""
    Base.compilecache(module::String)

Creates a precompiled cache file for
a module and all of its dependencies.
This can be used to reduce package load times. Cache files are stored in
`LOAD_CACHE_PATH[1]`, which defaults to `~/.julia/lib/VERSION`. See
[Module initialization and precompilation](@ref)
for important notes.
"""
function compilecache(pkg::PkgId)
    # decide where to get the source file from
    name = pkg.name
    path = locate_package(pkg)
    path === nothing && throw(ArgumentError("$name not found in path"))
    # decide where to put the resulting cache file
    cachepath = LOAD_CACHE_PATH[1]
    if !isdir(cachepath)
        mkpath(cachepath)
    end
    suffix = "$(pkg.name).ji"
    pkg.uuid !== nothing && (suffix = joinpath(slug(pkg.uuid), suffix))
    cachefile::String = abspath(cachepath, suffix)
    # build up the list of modules that we want the precompile process to preserve
    concrete_deps = copy(_concrete_dependencies)
    for (key, mod) in loaded_modules
        if !(mod === Main || mod === Core || mod === Base)
            push!(concrete_deps, key => module_build_id(mod))
        end
    end
    # run the expression and cache the result
    verbosity = isinteractive() ? CoreLogging.Info : CoreLogging.Debug
    if isfile(cachefile)
        @logmsg verbosity "Recompiling stale cache file $cachefile for module $name"
    else
        @logmsg verbosity "Precompiling module $name"
    end
    if success(create_expr_cache(path, cachefile, concrete_deps, pkg.uuid))
        # append checksum to the end of the .ji file:
        open(cachefile, "a+") do f
            write(f, hton(_crc32c(seekstart(f))))
        end
    else
        error("Failed to precompile $name to $cachefile.")
    end
    return cachefile
end

module_build_id(m::Module) = ccall(:jl_module_build_id, UInt64, (Any,), m)

isvalid_cache_header(f::IOStream) = (0 != ccall(:jl_read_verify_header, Cint, (Ptr{Cvoid},), f.ios))
isvalid_file_crc(f::IOStream) = (_crc32c(seekstart(f), filesize(f) - 4) == ntoh(read(f, UInt32)))

function parse_cache_header(f::IO)
    modules = Vector{Pair{Symbol, UInt64}}()
    while true
        n = ntoh(read(f, Int32))
        n == 0 && break
        sym = Symbol(read(f, n)) # module symbol
        uuid = ntoh(read(f, UInt64)) # module UUID (mostly just a timestamp)
        push!(modules, sym => uuid)
    end
    totbytes = ntoh(read(f, Int64)) # total bytes for file dependencies
    # read the list of requirements
    # and split the list into include and requires statements
    includes = Tuple{String, String, Float64}[]
    requires = Pair{String, String}[]
    while true
        n2 = ntoh(read(f, Int32))
        n2 == 0 && break
        depname = String(read(f, n2))
        mtime = ntoh(read(f, Float64))
        n1 = ntoh(read(f, Int32))
        if n1 == 0
            modkey = "Main" # remap anything loaded outside this cache files modules to have occurred in `Main`
        else
            modkey = String(modules[n1][1])
            while true
                n1 = ntoh(read(f, Int32))
                totbytes -= 4
                n1 == 0 && break
                modkey = string(modkey, ".", String(read(f, n1)))
                totbytes -= n1
            end
        end
        if depname[1] == '\0'
            push!(requires, modkey => depname[2:end])
        else
            push!(includes, (modkey, depname, mtime))
        end
        totbytes -= 4 + 4 + n2 + 8
    end
    @assert totbytes == 12 "header of cache file appears to be corrupt"
    srctextpos = ntoh(read(f, Int64))
    # read the list of modules that are required to be present during loading
    required_modules = Vector{Pair{Symbol, UInt64}}()
    while true
        n = ntoh(read(f, Int32))
        n == 0 && break
        sym = Symbol(read(f, n)) # module symbol
        uuid = ntoh(read(f, UInt64)) # module UUID
        push!(required_modules, sym => uuid)
    end
    return modules, (includes, requires), required_modules, srctextpos
end

function parse_cache_header(cachefile::String)
    io = open(cachefile, "r")
    try
        !isvalid_cache_header(io) && throw(ArgumentError("Invalid header in cache file $cachefile."))
        return parse_cache_header(io)
    finally
        close(io)
    end
end

function cache_dependencies(f::IO)
    defs, (includes, requires), modules = parse_cache_header(f)
    return modules, map(mod_fl_mt -> (mod_fl_mt[2], mod_fl_mt[3]), includes)  # discard the module
end

function cache_dependencies(cachefile::String)
    io = open(cachefile, "r")
    try
        !isvalid_cache_header(io) && throw(ArgumentError("Invalid header in cache file $cachefile."))
        return cache_dependencies(io)
    finally
        close(io)
    end
end

function read_dependency_src(io::IO, filename::AbstractString)
    modules, (includes, requires), required_modules, srctextpos = parse_cache_header(io)
    srctextpos == 0 && error("no source-text stored in cache file")
    seek(io, srctextpos)
    return _read_dependency_src(io, filename)
end

function _read_dependency_src(io::IO, filename::AbstractString)
    while !eof(io)
        filenamelen = ntoh(read(io, Int32))
        filenamelen == 0 && break
        fn = String(read(io, filenamelen))
        len = ntoh(read(io, UInt64))
        if fn == filename
            return String(read(io, len))
        end
        seek(io, position(io) + len)
    end
    error(filename, " is not stored in the source-text cache")
end

function read_dependency_src(cachefile::String, filename::AbstractString)
    io = open(cachefile, "r")
    try
        !isvalid_cache_header(io) && throw(ArgumentError("Invalid header in cache file $cachefile."))
        return read_dependency_src(io, filename)
    finally
        close(io)
    end
end

# returns true if it "cachefile.ji" is stale relative to "modpath.jl"
# otherwise returns the list of dependencies to also check
function stale_cachefile(modpath::String, cachefile::String)
    io = open(cachefile, "r")
    try
        if !isvalid_cache_header(io)
            @debug "Rejecting cache file $cachefile due to it containing an invalid cache header"
            return true # invalid cache file
        end
        (modules, (includes, requires), required_modules) = parse_cache_header(io)
        modules = Dict{Symbol, UInt64}(modules)

        # Check if transitive dependencies can be fullfilled
        ndeps = length(required_modules)
        depmods = Vector{Any}(uninitialized, ndeps)
        for i in 1:ndeps
            req_key, req_build_id = required_modules[i]
            # Module is already loaded
            if root_module_exists(req_key)
                M = root_module(req_key)
                if PkgId(M) === req_key && module_build_id(M) === req_build_id
                    depmods[i] = M
                else
                    @debug "Rejecting cache file $cachefile because module $req_key is already loaded and incompatible."
                    return true # Won't be able to fulfill dependency
                end
            else
                path = locate_package(req_key)
                if path === nothing
                    @debug "Rejecting cache file $cachefile because dependency $req_key not found."
                    return true # Won't be able to fulfill dependency
                end
                depmods[i] = (path, req_key, req_build_id)
            end
        end

        # check if this file is going to provide one of our concrete dependencies
        # or if it provides a version that conflicts with our concrete dependencies
        # or neither
        skip_timecheck = false
        for (req_key, req_build_id) in _concrete_dependencies
            build_id = get(modules, req_key, UInt64(0))
            if build_id !== UInt64(0)
                if build_id === req_build_id
                    skip_timecheck = true
                    break
                end
                @debug "Rejecting cache file $cachefile because it provides the wrong uuid (got $build_id) for $mod (want $req_build_id)"
                return true # cachefile doesn't provide the required version of the dependency
            end
        end

        # now check if this file is fresh relative to its source files
        if !skip_timecheck
            if !samefile(includes[1][2], modpath)
                @debug "Rejecting cache file $cachefile because it is for file $(includes[1][2])) not file $modpath"
                return true # cache file was compiled from a different path
            end
            for (modkey, req_modkey) in requires
                # TODO: verify `require(modkey, name(req_modkey))` ==> `req_modkey`
            end
            for (_, f, ftime_req) in includes
                # Issue #13606: compensate for Docker images rounding mtimes
                # Issue #20837: compensate for GlusterFS truncating mtimes to microseconds
                ftime = mtime(f)
                if ftime != ftime_req && ftime != floor(ftime_req) && ftime != trunc(ftime_req, 6)
                    @debug "Rejecting stale cache file $cachefile (mtime $ftime_req) because file $f (mtime $ftime) has changed"
                    return true
                end
            end
            for (modkey, req_modkey) in requires
                # TODO: verify `require(modkey, name(req_modkey))` ==> `req_modkey`
            end
            for (_, f, ftime_req) in includes
                # Issue #13606: compensate for Docker images rounding mtimes
                # Issue #20837: compensate for GlusterFS truncating mtimes to microseconds
                ftime = mtime(f)
                if ftime != ftime_req && ftime != floor(ftime_req) && ftime != trunc(ftime_req, 6)
                    @debug "Rejecting stale cache file $cachefile (mtime $ftime_req) because file $f (mtime $ftime) has changed"
                    return true
                end
            end
        end

        if !isvalid_file_crc(io)
            @debug "Rejecting cache file $cachefile because it has an invalid checksum"
            return true
        end

        return depmods # fresh cachefile
    finally
        close(io)
    end
end

"""
    @__LINE__ -> Int

`@__LINE__` expands to the line number of the location of the macrocall.
Returns `0` if the line number could not be determined.
"""
macro __LINE__()
    return __source__.line
end

"""
    @__FILE__ -> AbstractString

`@__FILE__` expands to a string with the path to the file containing the
macrocall, or an empty string if evaluated by `julia -e <expr>`.
Returns `nothing` if the macro was missing parser source information.
Alternatively see [`PROGRAM_FILE`](@ref).
"""
macro __FILE__()
    __source__.file === nothing && return nothing
    return String(__source__.file)
end

"""
    @__DIR__ -> AbstractString

`@__DIR__` expands to a string with the absolute path to the directory of the file
containing the macrocall.
Returns the current working directory if run from a REPL or if evaluated by `julia -e <expr>`.
"""
macro __DIR__()
    __source__.file === nothing && return nothing
    return abspath(dirname(String(__source__.file)))
end
