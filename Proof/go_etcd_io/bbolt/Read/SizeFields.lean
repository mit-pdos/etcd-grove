/-
`tx.Size()` over the fields it reads (session S4, for `Tx.WriteTo`'s proof, which needs the size's
value). Internal: not a spec of `Spec/`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.Size()` over the fields it reads** (session S4, for `Tx.WriteTo`, which needs the size's
value: the meta's high-water mark's pages). Internal (not a spec of `Spec/`). -/
theorem Tx.Size.wp_fields (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (tx m db : Loc) (mv : internal.common.Meta) (dq dq' : DFrac) :
    {{ tx.[Tx, go!"meta"] ↦{dq} m ∗ m ↦{dq} mv ∗ tx.[Tx, go!"db"] ↦{dq'} db ∗
        db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Size")) (Val #()))
    {{ RET #(mv.pgid' * W64 4096); tx.[Tx, go!"meta"] ↦{dq} m ∗ m ↦{dq} mv ∗
        tx.[Tx, go!"db"] ↦{dq'} db }} := by
  wp_start as ⟨Hm, Hmv, Hdb, #Hps, #Hpk⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Pgid $$ [$Hpkg $Hmv] as Hmv
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
