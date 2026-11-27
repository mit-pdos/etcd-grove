/-
**The server's consistent-index pair predicate** (keepfix-d, 2026-11-27, row 7a of
`~/coordinator-notes/plans/keepfix-d-design.md`, approved): the predicate the server's consistent index
keeps of every stored non-zero pair (`isCI ci γ (srvCIPair cl)`, `InvCindex.lean`), and the image
certificate's term row (`srvImage`, `InvImage.lean`). Lean-first (no Rocq counterpart).

The pair `(k, t)` a backend commit saves is one the apply thread applied (or loaded from a backend whose
image carries the row), so the boot step's snapshot label `(ci, t)` (the fork's `catchUpWithBackend`) is a
committed entry.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The server's consistent-index pair predicate** (keepfix-d): `t` is the term of the committed entry at
index `k` of the cluster `cl`'s log (persistent). The pair `(k, t)` a backend commit saves is one the apply
thread applied, so the boot step's snapshot label `(ci, t)` is a committed entry. -/
def srvCIPair (cl : Cluster) (k t : w64) : IProp GF :=
  iprop(∃ (l : List LogEntry) (e : LogEntry), isCommittedLogLb cl l ∗
    ⌜0 < uint.nat k ∧ l[uint.nat k - 1]? = some e ∧ e.term = t⌝)

instance srvCIPair_persistent (cl : Cluster) (k t : w64) :
    Persistent (srvCIPair (GF := GF) cl k t) := by
  unfold srvCIPair; infer_instance

end defs

end EtcdGrove
end Perennial
