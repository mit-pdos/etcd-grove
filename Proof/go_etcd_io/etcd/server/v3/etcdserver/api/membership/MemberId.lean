/- Lean-first (no Rocq counterpart).

# `membership`: the member id as etcd computes it

`memberIdOf peerURLs token`: `computeMemberID`'s id (`member.go`) of a member whose peer URL strings,
sorted and joined with no separator, are `peerURLs`, in the cluster `token`, with no time (`now == nil`,
as at bootstrap): the first 8 bytes, big-endian, of the SHA-1 (Perennial's `crypto.sha1.sha1`, FIPS
180-4) of the URLs followed by the token. Part of the statement of `etcd_safe` (`TopLevelDefs`'s
`memberId`); the one definition shared by the proofs that compute member ids (`membership.NewMember`'s
spec, putgetK's).
-/
module

public import Perennial.Proof.crypto.sha1.Fips180
public import Perennial.Std.ByteString

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace membership

/-- **etcd's member id** of the joined peer URLs `peerURLs` in the cluster `token` (no time): the first 8
bytes of `SHA-1(peerURLs ++ token)`, read big-endian. -/
def memberIdOf (peerURLs token : GoString) : w64 :=
  W64 (((crypto.sha1.sha1 (peerURLs ++ token)).take 8).foldl (fun acc b => acc * 256 + b.toNat) 0)

end membership
end EtcdGrove
end Perennial

end
