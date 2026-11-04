/-
The proof of `Spec/go_etcd_io/bbolt/DB__page.lean` (U4, `notes/bbolt-proof-plan.md`).

`DB.page.wp_proof'` is the spec with the mapping's base at a positive address (`0 < data.addr`)
in place of `data ≠ null`: `&db.data[i]` is `data + i` only at a positive base
(`arrayIndexRef_plain`), so the frozen premise does not determine the result (U4 finding).
`DB.page.wp_proof` waits for that premise (and `mapFields`' `base ≠ null` for `0 < base.addr`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__page
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem DB.page.wp_proof' (db data : Loc) (id : w64) (dq : DFrac)
    (Hpos : 0 < data.addr) (Hlt : id.toNat * 4096 < 0xFFFFFFFFFFFF) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"data"] ↦{dq} data ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"page")) (Val #id))
  {{ RET #(data +ₗ ((id.toNat * 4096 : Nat) : Int)); db.[DB, go!"data"] ↦{dq} data }} := by
  wp_start as ⟨Hd, Hps⟩
  wp_auto
  have hz : sint.Z (id * W64 4096) = ((id.toNat * 4096 : Nat) : Int) := by word
  rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (⟨by omega, by omega⟩ : _ ∧ _)),
    arrayIndexRef_byte _ _ Hpos (by omega)]
  wp_auto
  iapply HΦ; iframe

omit hos in
theorem DB.page.wp_proof : DB.page.spec (GF := GF) (hG := hG) := DB.page.wp_proof'

end proof

end bbolt
end EtcdGrove
end Perennial
