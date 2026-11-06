/-
`node.removeChild` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U8 (`node.rebalance`). Proof:
`Proof/go_etcd_io/bbolt/node__removeChild.lean` (a `sorry` until U8).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.removeChild(target)`: the first occurrence of `target` removed from `n.children` (in
place: a new slice header); nothing if it is not there. -/
abbrev node.removeChild.spec : Prop :=
  ∀ (n : Loc) (nv : node) (cs : List Loc) (target : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦ nv ∗ nv.children' ↦* cs ∗
      ownSliceCap Loc nv.children' (DFrac.own 1) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"removeChild")) (Val #target))
  {{ RET #(); ∃ s : GoSlice, n ↦ ({ nv with children' := s } : node) ∗ s ↦* cs.erase target ∗
      ownSliceCap Loc s (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
