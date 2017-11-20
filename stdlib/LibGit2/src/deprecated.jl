# 0.7 deprecations

# PR #23640
# when this deprecation is deleted, remove all calls to it, and replace all keywords of:
# `payload::Union{CredentialPayload,Nullable{<:AbstractCredentials}}` with
# `payload::CredentialPayload` from base/libgit2/libgit2.jl
@eval LibGit2 function deprecate_nullable_creds(f, sig, payload)
    if isa(payload, Nullable{<:AbstractCredentials})
        # Note: Be careful not to show the contents of the credentials as it could reveal a
        # password.
        if isnull(payload)
            msg = "LibGit2.$f($sig; payload=Nullable()) is deprecated, use "
            msg *= "LibGit2.$f($sig; payload=LibGit2.CredentialPayload()) instead."
            p = CredentialPayload()
        else
            cred = unsafe_get(payload)
            C = typeof(cred)
            msg = "LibGit2.$f($sig; payload=Nullable($C(...))) is deprecated, use "
            msg *= "LibGit2.$f($sig; payload=LibGit2.CredentialPayload($C(...))) instead."
            p = CredentialPayload(cred)
        end
        Base.depwarn(msg, f)
    else
        p = payload::CredentialPayload
    end
    return p
end

# PR #23690
# `SSHCredentials` and `UserPasswordCredentials` constructors using `prompt_if_incorrect`
# are deprecated in base/libgit2/types.jl.

# PR #23711
@eval LibGit2 begin
    @deprecate get_creds!(cache::CachedCredentials, credid, default) get!(cache, credid, default)
end
