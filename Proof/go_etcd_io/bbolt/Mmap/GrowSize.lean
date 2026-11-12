/-
`DB.growSize` (U4c, `notes/bbolt-proof-plan.md`): `db.growSize(mmapSize, growSize)` is
`mmapSize` up to `AllocSize` (`dbFixed`: 16 MiB), else `growSize + AllocSize`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section growSize
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The size `db.growSize(ms, gs)` returns (`AllocSize` 16 MiB). -/
def growSizeOf (ms gs : w64) : w64 :=
  if sint.Z ms ≤ sint.Z (W64 0x1000000) then ms else gs + W64 0x1000000

/-- **`db.growSize(ms, gs)`**: `growSizeOf ms gs`. -/
abbrev DB.growSize.spec : Prop :=
  ∀ (db : Loc) (ms gs : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      db.[DB, go!"AllocSize"] ↦□ W64 0x1000000 }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"growSize")) (Val #ms)) (Val #gs))
  {{ RET #(growSizeOf ms gs); True }}

theorem DB.growSize.wp_proof : DB.growSize.spec (GF := GF) (hG := hG) := by
  intro db ms gs
  wp_start as #Hal
  wp_auto
  unfold growSizeOf
  by_cases h : sint.Z ms ≤ sint.Z (W64 0x1000000)
  · simp only [h, decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h, decide_false, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end growSize

end bbolt
end EtcdGrove
end Perennial
