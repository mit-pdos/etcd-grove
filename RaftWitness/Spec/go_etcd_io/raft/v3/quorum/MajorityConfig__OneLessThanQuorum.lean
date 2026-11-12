/-
New in etcd-io/raft#168 (share witness), Lean-first (`notes/pr-verify/raft-168.md`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- `N` is the largest value at least `k` voters of `s` have reached (`IsQuorumIndex` with
"a quorum" replaced by "at least `k`"): one of the values, reached by `k` voters, and no
larger value is. -/
def IsCountIndex (s : GSet w64) (f : w64 → w64) (k : Nat) (N : w64) : Prop :=
  (∃ v, v ∈ s ∧ f v = N) ∧
  k ≤ GMap.size (GMap.filter (fun v _ => decide (uint.Z N ≤ uint.Z (f v))) s) ∧
  (∀ N' : w64, uint.Z N < uint.Z N' →
    GMap.size (GMap.filter (fun v _ => decide (uint.Z N' ≤ uint.Z (f v))) s) < k)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.OneLessThanQuorum(l)` (raft#168, majority.go): `CommittedIndex` read one slot further
right, `pos := n - n/2` instead of `n - (n/2 + 1)`: the largest index acknowledged by
`quorum - 1 = n/2` voters (what `ProgressTracker.OneLessThanQuorumInReplicationSet` hands the
leader, which then sends that entry to the witness, whose acknowledgement would make a quorum).

At one voter it returns 0: `quorum - 1 = 0` voters "acknowledge" every index, and the function
reports none (until the fork's fix it read `srt[1]` of a one-slot slice and panicked,
`TestOneLessThanQuorumSingleVoter`, `notes/pr-verify/raft-168.md`). The other premises are
`CommittedIndex`'s. -/
abbrev quorum.MajorityConfig.OneLessThanQuorum.spec : Prop :=
  ∀ (s : GSet w64) (cref mref : Loc) (l : GoInterface) (P : IProp GF)
    (acked : w64 → Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗
      ⌜(GMap.size s : Int) ≤ 2 ^ 62⌝ ∗
      cref ↦ mref ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) ∗
      isAckedIndexer l P acked ∗ P }}
    (App (Val (cref @!! go.GoType.PointerType quorum.MajorityConfig.ty
      @!! go!"OneLessThanQuorum")) (Val #l))
  {{ (N : w64), RET #N;
      cref ↦ mref ∗
      (⌜mref = map.nil ∧ s = ∅⌝ ∨
       ∃ (ids : GMap w64 Unit), ⌜domSet ids = s⌝ ∗ mref ↦$ ids) ∗
      P ∗
      ⌜s = ∅ → N = W64 (2 ^ 64 - 1)⌝ ∗
      ⌜GMap.size s = 1 → N = W64 0⌝ ∗
      ⌜s ≠ ∅ → GMap.size s ≠ 1 →
        IsCountIndex s (fun v => (acked v).getD (W64 0)) (GMap.size s / 2) N⌝ }}

end spec

end EtcdGrove
end Perennial
