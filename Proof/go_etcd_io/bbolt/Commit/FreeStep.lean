/-
**`Commit`'s free of the synced freelist page over `wdbW`** (U10n): the fields `db.data` and
`db.freelist` out of `wdbW` for the call's arguments (`wdbW_free_acc`), and the free itself from
`wdbW` to the flagged `wdbW' true` of `w.freeFl f n` (`cm_free_flW`, over `Commit/FreeFl`'s
`cm_free_fl` and `Commit/FreeFlPure`'s `freeFl_ok`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.FreeFl

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

omit package_sem in
/-- **`db.data` and `db.freelist`** out of `wdbW` (the mapping's base, positive), and back. -/
theorem wdbW_free_acc (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜0 < v.base.addr ∧ mapLen w.ms ≤ 0xFFFFFFFFFFFF⌝ ∗
      K.db.[DB, go!"data"] ↦{DFrac.own (1 : Qp).half.half} v.base ∗
      K.db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli ∗
      (K.db.[DB, go!"data"] ↦{DFrac.own (1 : Qp).half.half} v.base -∗
        K.db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli -∗ wdbW K tx v w) := by
  unfold wdbW wdbLive wdbCoreG
  iintro ⟨⟨⟨H1, H2, H3, H4, H5, Hfli, H7, H8, H9, H10, H11, H12, Hmf, Hrest⟩, Hfl, Hrd, Hrc⟩,
    %Hok⟩
  have hms := Hok.2.1
  generalize hL : mapLen w.ms = L at hms
  ihave Hmf : mapFields (GF := GF) K.db (DFrac.own (1 : Qp).half.half) (some (v.base, L)) $$ [Hmf]
  · rw [← hms]; iexact Hmf
  isimp only [mapFields] at Hmf
  icases Hmf with ⟨Hdr, Hdata, Hm0, Hm1, %hmf⟩
  iframe Hdata Hfli
  isplitr
  · ipureintro
    exact ⟨hmf.2.1, hmf.1⟩
  iintro Hdata Hfli
  ihave Hmf : mapFields (GF := GF) K.db (DFrac.own (1 : Qp).half.half) w.ms $$ [Hdr Hdata Hm0 Hm1]
  · rw [hms]; simp only [mapFields]; iframe; ipureintro; exact hmf
  iframe
  ipureintro; subst hL; exact Hok

/-- **The free of the synced freelist page `f`** from `wdbW` to the flagged `wdbW' true` of the
freed writer side (see the file header). -/
theorem cm_free_flW (wp_FlFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (v : View) (w : WDb) (f : Nat)
    (hok : wdbOK w) (hms : w.ms = some (v.base, mapLen w.ms)) (hv : v = View.ofC v.base w.C)
    (hf : w.C.flpg = some f)
    (hlen : w.fl.allIds.length < 2 ^ 48)
    (hal : (w.fl.allocs !! W64 (f : Int)).getD 0 ≠ w.wtxid)
    (hid : pageId (w.wb f) = f) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ K.core ∗
        wdbW K tx v w }}
      (App (App (ifaceCall w.fli go!"Free") (Val #w.wtxid))
        (Val #(v.base +ₗ ((f * 4096 : Nat) : Int))))
    {{ RET #(); wdbW' true K tx v (w.freeFl f (1 + pageOverflow (w.wb f))) }} := by
  obtain ⟨-, -, -, -, -, -, hok', hfb, -⟩ := freeFl_ok w f hok hf hlen
  unfold wdbW
  wp_start as ⟨#Hcore, Hl, -⟩
  wp_apply cm_free_fl wp_FlFree K tx v w f v.base (mapLen w.ms) hok hms hf hlen hal hid
    $$ [Hl] as ⟨Hl, Htok⟩
  · iframe; iframe #
  iapply HΦ
  unfold wdbW'
  simp only [WDb.freeFl.proj_C, WDb.freeFl.proj_ms]
  iframe Hl
  isplitr
  · ipureintro; exact ⟨hok', hms, hv⟩
  iexists fbRec (W64 (f : Int)) (1 + pageOverflow (w.wb f)) w.wb
  isplitl [Htok]
  · simp only [WDb.freeFl.proj_fl]; iexact Htok
  · ipureintro; exact hfb

end proof

end bbolt
end EtcdGrove
end Perennial
