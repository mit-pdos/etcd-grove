/-
**The revocation's level count** (revoke-open review round 1, S4, 2026-11-06): the number of levels
of a thread token the revocation's goroutines use (`RevokeCtx.lean`'s header: levels 0–3), named
once for its two users, the owner's `srvRevokeLevels` (`RevokeCtx.lean`) and the etcd examples'
adequacy lemmas (`etcdstart/Adequacy.lean`, the thread bound `max (n + 2) srvRevokeK`), so that a
new level changes one number. A module of its own: the adequacy lemmas import nothing else of the
server. Lean-first.
-/
module

public import Perennial.Std.Attrs

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- **The levels of a thread token the revocation uses** (levels `0 … srvRevokeK - 1`; see the file
header). -/
@[word_unfold] def srvRevokeK : Nat := 4

/-- **The levels of a thread token a serving member uses** (per-type stage B, r5 §3.3): the
revocation's levels `0 … 3`, which a gRPC run shares (level 1 `raftPool`, level 2 the inner pool
`I`, level 3 the run pool), and (k8s 7f-4, Freeze addendum T-f') level 4, which a stream run lends
its handler for a weak context's `Err()` (`v3rpc.ctxErrLvl`). The etcd examples' adequacy lemmas
are written with it, so a new level changes one number. -/
@[word_unfold] def srvLevelK : Nat := srvRevokeK + 1

end EtcdGrove
end Perennial
