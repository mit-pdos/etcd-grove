/-
A read transaction ends: the database's state without the reader (`DBState.removeReader`), its
facts kept (`dbOK_removeReader`), and the reader's pages and fields given back (`end_give`).
-/
module

public import Proof.go_etcd_io.bbolt.DBBegin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database without the reader `r` (key `k`): its fractions back, and the freelist's
read-only transactions `ro` (`r`'s txid removed, in some order). -/
def DBState.removeReader (σ : DBState) (k : Nat) (r : Reader) (ro : List w64) : DBState :=
  { σ with
    readers := GMap.delete k σ.readers
    rem := fun s => if r.sees s then σ.rem s + r.q else σ.rem s
    frem := σ.frem + r.q
    fl := { σ.fl with readonly := ro } }
proj_simps DBState.removeReader

theorem dbOK_removeReader (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (k : Nat) (r : Reader) (hk : σ.readers !! k = some r) (ro : List w64)
    (hro : ro.Perm (σ.fl.readonly.erase r.txid)) :
    dbOK (σ.removeReader k r ro) v0 v1 := by
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hroP, hrs⟩ := h
  refine ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k' r' hk'
    rw [DBState.removeReader.proj_readers, GMap.lookup_delete_Some] at hk'
    exact hrd k' r' hk'.2
  · intro k' r' s hk' hs
    rw [DBState.removeReader.proj_readers, GMap.lookup_delete_Some] at hk'
    exact hmv k' r' s hk'.2 hs
  · intro s hs
    have H := hsl s hs
    rw [readersQ_delete _ _ k r hk] at H
    unfold readersStep at H
    show fracSum (if r.sees s then σ.rem s + r.q else σ.rem s)
      (readersQ (GMap.delete k σ.readers) (fun r => r.sees s)) halfQ
    cases hrs' : r.sees s
    · simp only [hrs', Bool.false_eq_true, ↓reduceIte] at H ⊢; exact H
    · simp only [hrs', ↓reduceIte] at H ⊢; exact fracSum_give _ _ _ _ H
  · have H := hfl
    unfold fieldsOK at H
    rw [readersQ_delete _ _ k r hk] at H
    unfold readersStep at H
    simp only [↓reduceIte] at H
    exact fracSum_give _ _ _ _ H
  · show ro.Perm ((GMap.toList (GMap.delete k σ.readers)).map (·.2.txid))
    have hp := (GMap.mapToList_delete σ.readers k r hk).map (fun kr => kr.2.txid)
    have h2 : σ.fl.readonly.Perm (r.txid :: (GMap.toList (GMap.delete k σ.readers)).map (·.2.txid)) :=
      hroP.trans hp
    refine hro.trans ?_
    have h3 := h2.erase r.txid
    simp only [List.erase_cons_head] at h3
    exact h3
  · show (GMap.delete k σ.readers).size < Int.toNat sync.rwmutex.actualMaxReaders
    rw [GMap.map_size_delete_Some _ _ _ hk]; omega

open Iris.ProofMode in
/-- An ending reader gives back its pages and its part of the fields. -/
theorem end_give (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (k : Nat) (r : Reader) (hk : σ.readers !! k = some r) (ro : List w64) (dbl : Loc) :
    slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own σ.frem} σ.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{DFrac.own σ.frem} W64 σ.ps ∗
      pagesView σ.data σ.ps r.q r.pages ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own r.q} σ.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{DFrac.own r.q} W64 σ.ps ⊢
    slotsView σ.data σ.bs σ.ps (σ.removeReader k r ro).rem (List.range σ.nslots) ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own (σ.removeReader k r ro).frem} σ.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{DFrac.own (σ.removeReader k r ro).frem} W64 σ.ps := by
  have h' := h
  obtain ⟨hps, _, _, _, _, _, _, _, _, hrd, _⟩ := h'
  obtain ⟨_, rdisj, rin⟩ := hrd k r hk
  have Hcarve := slots_carve (GF := GF) σ.data σ.bs σ.ps (σ.removeReader k r ro).rem σ.rem r.q
    σ.nslots r.pages (by omega) (nslots_mul_le σ)
    (fun id pg hid => ⟨(rin id pg hid).1.symm, (rin id pg hid).2⟩) rdisj
    (fun s _ hc => by
      show (if r.sees s then σ.rem s + r.q else σ.rem s) = σ.rem s + r.q
      rw [show r.sees s = true by unfold Reader.sees; simp only [decide_eq_true_eq]; exact hc]
      rfl)
    (fun s _ hc => by
      show (if r.sees s then σ.rem s + r.q else σ.rem s) = σ.rem s
      rw [show r.sees s = false by unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hc]
      rfl)
  rw [DBState.removeReader.proj_frem]
  iintro ⟨Hs, Hd, Hp, Hpg, Hd', Hp'⟩
  iframe
  isplitl [Hs Hpg]
  · iapply Hcarve.2; iframe
  isplitl [Hd Hd']
  · iapply (pointsto_split _ _ _ _).2; iframe
  · iapply (pointsto_split _ _ _ _).2; iframe

end defs

end bbolt
end EtcdGrove
end Perennial
