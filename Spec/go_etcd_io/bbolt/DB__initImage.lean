/-
`DB.initImage` (bbolt, internal; the fork's crash-safe `init`, `issues/bbolt-init-not-crash-safe.md`):
the four pages `init` writes, as a new slice (`Open/InitImage.initImg`). `init` writes them and
`needsInit` compares a file with them. Proof: `Proof/go_etcd_io/bbolt/DB__initImage.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Open.InitImage
public import Proof.go_etcd_io.bbolt.Inv.FileHolds
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.initImage()`**, the page size `4096` held at any fraction (`Open`'s owned phase:
`needsInit` runs before the page size is final): a new slice holding `initImg`, with its
capacity. -/
abbrev DB.initImage.spec : Prop :=
  ∀ (db : Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"pageSize"] ↦{dq} W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"initImage")) (Val #()))
  {{ (sl : GoSlice), RET #sl; db.[DB, go!"pageSize"] ↦{dq} W64 4096 ∗ sl ↦* initImg ∗
      ownSliceCap w8 sl (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
