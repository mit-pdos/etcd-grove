/-
`node.numChildren` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U8 (`node.rebalance`, siblings). Proof:
`Proof/go_etcd_io/bbolt/node__numChildren.lean` (a `sorry` until U8).
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

/-- `n.numChildren()`: the number of its inodes (the slice's length). -/
abbrev node.numChildren.spec : Prop :=
  ∀ (n : Loc) (nv : node) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"numChildren")) (Val #()))
  {{ RET #nv.inodes'.len; n ↦{dq} nv }}

end spec

end bbolt
end EtcdGrove
end Perennial
