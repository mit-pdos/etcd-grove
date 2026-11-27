/-
**The server's consistent-index pair predicate** (keepfix-d, 2026-11-27, row 7a of
`~/coordinator-notes/plans/keepfix-d-design.md`, approved): the predicate the server's consistent index
keeps of every stored non-zero pair, and the image certificate's term row (`srvImage`, `InvImage.lean`).
(keepfix (c), 2026-11-28, `keepfix-c-design.md` rev 2 §1b, approved) The consistent index keeps the triple
predicate `srvCITriple` (`isCI ci γ (srvCITriple cl)`): the pair's, the raft term saved with it non-zero and
certified (`srvRtCert`). Lean-first (no Rocq counterpart).

The pair `(k, t)` a backend commit saves is one the apply thread applied (or loaded from a backend whose
image carries the row), so the boot step's snapshot label `(ci, t)` (the fork's `catchUpWithBackend`) is a
committed entry.
-/
module

public import Spec.go_etcd_io.raft.v3.Api
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog

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

/-- (keepfix (c)) **A raft term certified for an index**: raft had committed the log through some `c ≥ k` at a
term `≤ rt` (`committedAtTerm`, which with N1 also says `rt` is within the term budget). What the raft-term key's
value `(k, rt)` and the cindex's `(k, rt)` say. Monotone in `rt` given a certificate at the larger term
(`committedAtTerm_mono_term`). -/
def srvRtCert (cl : Cluster) (k rt : w64) : IProp GF :=
  iprop(∃ c : w64, committedAtTerm cl srvClusterN rt c ∗ ⌜uint.Z k ≤ uint.Z c⌝)

instance srvRtCert_persistent (cl : Cluster) (k rt : w64) :
    Persistent (srvRtCert (GF := GF) cl k rt) := by
  unfold srvRtCert; infer_instance

/-- **The server's consistent-index triple predicate** (keepfix (c)): `(k, t)` is a committed entry
(`srvCIPair`); `rt`, the member's raft term when it applied `k`, which the boot step raises the hard state's term
to, is not 0 and is certified for `k`. Held of the cindex's fields whenever the index is not 0 (`ciPairInv`). -/
def srvCITriple (cl : Cluster) (k t rt : w64) : IProp GF :=
  iprop(srvCIPair cl k t ∗ ⌜rt ≠ W64 0⌝ ∗ srvRtCert cl k rt)

instance srvCITriple_persistent (cl : Cluster) (k t rt : w64) :
    Persistent (srvCITriple (GF := GF) cl k t rt) := by
  unfold srvCITriple; infer_instance

end defs

end EtcdGrove
end Perennial
