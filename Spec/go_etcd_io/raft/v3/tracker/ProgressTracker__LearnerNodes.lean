/-
`tracker.ProgressTracker.LearnerNodes`, Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.LearnerNodes()` (`tracker.ProgressTracker.LearnerNodes.impl`,
`Code/go_etcd_io/raft/v3/tracker.lean`; tracker.go:232):

    if len(p.Learners) == 0 { return nil }
    nodes := make([]uint64, 0, len(p.Learners))
    for id := range p.Learners { nodes = append(nodes, id) }
    slices.Sort(nodes)
    return nodes

For a general configuration: the learner set is `nil` or a map (`ownIdsetQ`), read at a
fraction, as is the tracker struct. The result is the learner ids, sorted, and `nil`
when there are none. The premise `size ls ≤ 2^62` is `slices.Sort`'s (`Spec/slices/Sort.lean`). -/
abbrev tracker.ProgressTracker.LearnerNodes.spec : Prop :=
  ∀ (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) (dql : DFrac)
    (ls : GMap w64 Unit),
  (GMap.size ls : Int) ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownIdsetQ tv.Config'.Learners' dql ls }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"LearnerNodes"))
      (Val #()))
  {{ (sl : GoSlice) (xs : List w64), RET #sl;
      trk ↦{dq} tv ∗ ownIdsetQ tv.Config'.Learners' dql ls ∗
      sl ↦* xs ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
      ⌜xs ≡ₚ GMap.elements ls⌝ ∗
      ⌜∀ (i j : Nat) (xi xj : w64), xs[i]? = some xi → xs[j]? = some xj →
          i < j → uint.Z xi ≤ uint.Z xj⌝ ∗
      ⌜ls = ∅ → sl = slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial
