/-
Access lemmas of the writer's shared predicates for `Tx.commitFreelist` (U10c's need, decided by
the coordinator, 2026-11-04): the writer side's freelist object out of `wdbW` and back
(`wdbW_fl_acc`: `EstimatedWritePageSize`, `Write`), and the new freelist page's buffer with the
meta copy out of `wtxW` and back as `WX.setFlPage` (`wtxW_flpage_acc`: `SetFreelist`, `Id`, the
page's write).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- `X` with the freelist page `bs` in the buffer of page `id` and `tx.meta.freelist = id`
(moved from `Tx__commitFreelist.lean`). -/
def WX.setFlPage (X : WX) (id : w64) (bs : List w8) : WX :=
  { X with t := { X.t with
      bufs := X.t.bufs.insert id bs,
      mv := { X.t.mv with freelist' := id } } }

end pure

section access
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer side's freelist** (`db.freelist`'s half and `flPgOwn`) out of `wdbW`, and back
unchanged. -/
theorem wdbW_fl_acc (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ∃ dq : DFrac, K.db.[DB, go!"freelist"] ↦{dq} w.fli ∗
      flPgOwn w.fli w.fl ∗
      (K.db.[DB, go!"freelist"] ↦{dq} w.fli -∗ flPgOwn w.fli w.fl -∗ wdbW K tx v w) := by
  unfold wdbW wdbLive wdbCoreG
  iintro ⟨⟨⟨H1, H2, H3, H4, H5, Hfli, Hrest⟩, Hfl, Hrd, Hrc⟩, %Hok⟩
  iexists DFrac.own (1 : Qp).half
  iframe Hfli Hfl
  iintro Hfli Hfl
  iframe
  ipureintro; exact Hok

/-- **The new freelist page's buffer and the meta copy** out of the writer's heap (`tx.db`'s and
`tx.meta`'s fields with them), and back with the buffer's new bytes and `tx.meta.freelist = id`
(`WX.setFlPage`). -/
theorem wtxW_flpage_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (id : w64) (p : Loc)
    (bs : List w8) (hp : X.t.pm !! id = some p) (hb : X.t.bufs !! id = some bs) :
    wtxW (GF := GF) K tx r m X ⊢ ∃ (mp : Loc) (dq : DFrac),
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ tx.[Tx, go!"meta"] ↦{dq} mp ∗
      mp ↦ X.t.mv ∗ bytesPointsto p (DFrac.own 1) bs ∗
      (∀ bs' : List w8, ⌜bs'.length = bs.length⌝ -∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ tx.[Tx, go!"meta"] ↦{dq} mp -∗
        mp ↦ ({ X.t.mv with freelist' := id } : Meta) -∗ bytesPointsto p (DFrac.own 1) bs' -∗
        wtxW K tx r m (X.setFlPage id bs')) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨#Hpkg, #Hcore, %Hc, #Hreg, ⟨%Hh, ⟨Hwr, Hmg, Hme, Hpg, Hch, Hwf, Hmv, Hpm, Hbufs⟩,
    Hrf, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hvc, Hmap⟩
  icases (BigSepM.bigSepM_delete hp).1 $$ Hbufs with ⟨⟨%bs0, %hb0, Hp⟩, Hbufs⟩
  rw [hb] at hb0
  cases hb0
  have hdb : r.db = K.db := Hc.1
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db $$ [Hdb]
  · rw [← hdb]; iexact Hdb
  iexists X.t.t.meta', DFrac.own 1
  iframe Hdb Hme Hmv Hp
  iintro %bs' %_ Hdb Hme Hmv Hp
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db $$ [Hdb]
  · rw [hdb]; iexact Hdb
  ihave Hbufs' : [∗map] k ↦ pl ∈ X.t.pm, ∃ bs0, ⌜(X.t.bufs.insert id bs') !! k = some bs0⌝ ∗
      bytesPointsto pl (DFrac.own 1) bs0 $$ [Hbufs Hp]
  · iapply (BigSepM.bigSepM_delete (m := X.t.pm) hp).2
    isplitl [Hp]
    · iexists bs'; iframe; ipureintro; exact GMap.lookup_insert _ _ _
    iapply (BigSepM.bigSepM_mono ?_) $$ Hbufs
    intro k pl hk
    iintro ⟨%bk, %hbk, Hk⟩
    iexists bk; iframe
    ipureintro
    have hne : id ≠ k := by
      intro e; subst e
      have h0 := GMap.lookup_delete X.t.pm id
      exact absurd hk (by rw [show Std.get? (Std.delete X.t.pm id) id = (GMap.delete id X.t.pm) !! id from rfl, h0]; simp)
    rw [GMap.lookup_insert_ne _ _ hne]; exact hbk
  simp only [WX.setFlPage]
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact Hh

end access

end bbolt
end EtcdGrove
end Perennial
