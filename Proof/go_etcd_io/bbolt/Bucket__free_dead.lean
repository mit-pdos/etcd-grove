/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__free_dead.lean` (U7n, `notes/bbolt-proof-plan.md`):
`RootPage`, the dead walk (`Write/WalkDead.forEachPageNode_dead` over the view's page tree), its
callback freeing each page (`Free`, a `store_free` step: `Bucket.free`'s page case, the records
unchanged) over the invariant `freeID`, and `SetRootPage(0)` (`wtxW_dead_acc`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__free_dead
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__SetRootPage
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free
public import Proof.go_etcd_io.bbolt.Write.WalkDead
public import Proof.go_etcd_io.bbolt.Write.Free
public import Proof.go_etcd_io.bbolt.Rebalance.Free

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

/-- The dead free walk's invariant: the records unchanged, the freelist with the positions `ps`'
extents freed, and the callback's `tx` variable. -/
def freeID (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (txp : Loc)
    (ps : List w64) : IProp GF :=
  iprop(∃ (w' : WDb), wtxW K tx r m X ∗ wdbW K tx X.v w' ∗ txp ↦ tx ∗
    ⌜w' = w.withFl (w.fl.freeAll w.wtxid (ps.filterMap (pExt X.v)))⌝)

omit package_sem in
theorem freeID_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (txp : Loc) :
    ⊢ Write.walkAccD K tx r m X (freeID (GF := GF) K tx r m X w txp) := by
  unfold Write.walkAccD
  iintro !> %ps HI
  unfold freeID
  icases HI with ⟨%w', Hw, Hdb, Htx, %Hf⟩
  iframe Hw
  iintro Hw
  iexists w'
  iframe
  ipureintro; exact Hf

theorem Bucket.free_dead.wp_proof (hpnd : Bucket.pageNode_d.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hSRP : internal.common.InBucket.SetRootPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG)) :
    Bucket.free_dead.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w bl B t hbs hd hlive hbtx hnil hpre
  wp_start as ⟨Hw, Hdb⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases Write.wtxW_dead_obj_acc K tx r m X bl B hbs hd $$ Hw with ⟨Ho, Hwb⟩
  rw [decide_eq_false hlive]
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iframe
  by_cases h0 : B.ib.root' = W64 0
  · rw [decide_eq_true h0]
    wp_auto
    ihave Hw := Hwb $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
    · simp only [objOwn]; iframe
    iapply HΦ
    iexists X, w
    iframe
    ipureintro; exact Or.inl ⟨h0, rfl, rfl⟩
  rw [decide_eq_false h0]
  obtain ⟨hpg0, hvw, ht, htp, hpmall, hcan, htxid⟩ := hpre h0
  wp_auto
  ihave Htxf : (∃ dqb : DFrac, bl.[Bucket, go!"tx"] ↦{dqb} tx ∗
      (bl.[Bucket, go!"tx"] ↦{dqb} tx -∗
        if bl = B.bv.tx'.[Tx, go!"root"] then bl.[Bucket, go!"tx"] ↦ B.bv.tx'
        else bl.[Bucket, go!"tx"] ↦□ B.bv.tx') : IProp GF) $$ [Htx]
  · rw [hbtx]
    by_cases hroot : bl = tx.[Tx, go!"root"]
    · rw [if_pos hroot]
      iexists DFrac.own 1
      iframe
      iintro H; iexact H
    · rw [if_neg hroot]
      icases Htx with #Htx
      iexists DFrac.discard
      isplitr
      · iexact Htx
      · iintro _; iexact Htx
  icases Htxf with ⟨%dqb, Htx, Htxb⟩
  wp_auto
  ihave Htx := Htxb $$ Htx
  ihave Hw := Hwb $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · simp only [objOwn]; iframe
  ihave #Hacc := freeID_acc K tx r m X w tx_ptr
  rw [recv_eq_func_mk]
  wp_apply (Write.forEachPageNode_dead hpnd hRP hIB hCnt hBE hBP K tx r m X bl B
    (freeID K tx r m X w tx_ptr) t.pos _ t hbs hd hlive hbtx hnil h0 hpg0 hvw hpmall ht htp
    (List.prefix_refl _)) $$ Hacc [] [Hw Hdb tx]
  · unfold Write.walkCbD
    iintro !> %ps %pid %pg %d
    wp_start as ⟨HI, %Hc⟩
    obtain ⟨hpq, hpg⟩ := Hc
    unfold freeID
    icases HI with ⟨%w', Hw, Hdb, Htx, %Hf⟩
    subst Hf
    obtain ⟨h2, hid, h4096, hfl⟩ := Read.viewWF_page X.v hvw _ pg hpg
    have he : pExt X.v pid = some (pid, 1 + pageOverflow pg) := by simp [pExt, hpg]
    have hcf := Write.canFree_at w.fl w.wtxid _ t.pos ps pid _ hpq he hcan
    unfold wtxW wtxCore
    icases Hw with ⟨⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
    unfold wtxHeap
    icases Hh with ⟨%Hok', Hf, Hrf, Hm, Hbk'⟩
    unfold txFields
    icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
    icases viewCells_page_acc _ _ pid.toNat pg hpg $$ Hcells with ⟨Hpg, Hcells⟩
    have hpgne : pg ≠ [] := by intro h; rw [h] at h4096; simp at h4096
    ihave %Hpos := bytesPointsto_pos _ _ _ hpgne $$ Hpg
    have hpnn : pageLoc X.v pid.toNat ≠ null := by intro e; rw [e] at Hpos; simp [null] at Hpos
    obtain ⟨w0, hw0e⟩ : ∃ w0, w0 = w.withFl (w.fl.freeAll w.wtxid (ps.filterMap (pExt X.v))) :=
      ⟨_, rfl⟩
    rw [← hw0e]
    have hfl0 : w0.fl = w.fl.freeAll w.wtxid (ps.filterMap (pExt X.v)) := by subst hw0e; rfl
    have hwt0 : w0.wtxid = w.wtxid := by subst hw0e; rfl
    unfold wdbW wdbLive wdbCoreG
    icases Hdb with ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok⟩
    rw [Hr.1]
    wp_auto
    rw [decide_eq_false hpnn]
    wp_auto
    wp_apply hTxid $$ [Hmv] as Hmv
    · iframe
    wp_auto
    icases bytesPointsto_view_read (V := Page) (pageLoc X.v pid.toNat) (DFrac.own wq) pg 0
      (pageLoc X.v pid.toNat) (by simp [loc_add_0]) (by omega) Hpos $$ Hpg with ⟨Hhdr, Hclose⟩
    rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl]
    have hhid : (pageHdr pg).id' = pid := by
      apply BitVec.eq_of_toNat_eq; exact hid
    have hcan0 : w0.fl.canFree w0.wtxid pid (1 + pageOverflow pg) := by
      rw [hfl0, hwt0]; exact hcf
    have hcan' : w0.fl.canFree X.t.mv.txid' (pageHdr pg).id' (1 + (pageHdr pg).overflow'.toNat) := by
      rw [htxid, hhid, ← hwt0]; exact hcan0
    ihave #Hpinv : (inv (pagesN K.N) (pagesInv (GF := GF) K.B K.p) : IProp GF) $$ []
    · unfold BC.core isBoltCoreP
      icases Hcore with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
      iexact Hpi
    have hCpg : w0.C.pages = X.v.pages := by rw [Hwok.2.2]; rfl
    imod (store_free K.B K.N K.p ⊤ CoPset.subseteq_top w0.C w0.fl w0.ms (wLive X.v w0.C)
      (w0.C.txid + 1) pid (1 + pageOverflow pg) (fun _ => []) rfl rfl (by exact hcan0))
      $$ [Hpinv Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv⟩
    · iframe; iframe #
      ileft
      ipureintro
      exact ⟨pg, by rw [hCpg]; exact hpg, rfl⟩
    wp_apply hFree w0.fli w0.fl X.t.mv.txid' _ (pageHdr pg) (DFrac.own wq) hcan' $$ [Hflo Hhdr]
      as ⟨Hflo, Hhdr⟩
    · iframe
    ihave Hpg := Hclose $$ Hhdr
    ihave Hcells := Hcells $$ Hpg
    iapply HΦ
    iexists w0.withFl (w0.fl.freePages w0.wtxid pid (1 + pageOverflow pg))
    simp only [WDb.withFl]
    rw [htxid, ← hwt0]
    iframe; iframe #
    isplitr
    · ipureintro; exact ⟨⟨trivial, Hr.2.1, Hr.2.2.1, Hr.2.2.2.1, Hr.2.2.2.2⟩, Hok'⟩
    isplitl [Hflo]
    · isplitl [Hflo]
      · rw [← hhid]; simp only [pageHdr, pageOverflow]; iexact Hflo
      · ipureintro
        exact ⟨wdbOK_free w0 pid pg Hwok.1 (by rw [hCpg]; exact hpg) hcan0, Hwok.2.1, Hwok.2.2⟩
    ipureintro
    subst hw0e
    simp only [WDb.withFl, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he,
      Write.freeAll_append, Write.freeAll_cons]
    rfl
  · unfold freeID
    iexists w
    iframe
    ipureintro
    rfl
  iintro HI
  unfold freeID
  icases HI with ⟨%w', Hw, Hdb, Htx, %Hf⟩
  icases Write.wtxW_dead_acc K tx r m X bl B hbs hd $$ Hw with ⟨Ho, Hwb⟩
  rw [decide_eq_false hlive]
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply hSRP $$ [Hib] as Hib
  · iframe
  ihave Hw := Hwb $$ %({ B with ib := { B.ib with root' := W64 0 } } : BRec)
    [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · simp only [objOwn]; iframe
  iapply HΦ
  iexists _, _
  iframe
  ipureintro
  exact Or.inr ⟨h0, rfl, Hf⟩

end proof

end bbolt
end EtcdGrove
end Perennial
