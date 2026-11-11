/-
`node.root` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U8; used by U9b (`Bucket.spill`, `Bucket.dereference`). Proof:
`Proof/go_etcd_io/bbolt/node__root.lean` (a `sorry` until U8).
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

/-- `n.root()`: the top of `n`'s chain of parents within its bucket's nodes (`nodeRootIn`), read
through the writer's heap at any fraction. -/
abbrev node.root.spec : Prop :=
  ∀ (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (n rt : Loc),
  X.t.bs !! bl = some B → nodeRootIn B n rt →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ wtxHeap tx dq X }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"root")) (Val #()))
  {{ RET #rt; wtxHeap tx dq X }}

end spec

end bbolt
end EtcdGrove
end Perennial
