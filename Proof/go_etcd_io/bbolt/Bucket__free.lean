/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__free.lean` (U7e, `notes/bbolt-proof-plan.md`; the
spec is U7e's variant since batch 35): `RootPage`, the walk (`Write/Walk`'s `walk_aux` over the
bucket's finite tree, `rtOK`), its callback freeing each position's page (`Free`, a `store_free`
step) or node (`node.free`) over the invariant `freeI` (`Write/Free`'s `freedAt`), and
`SetRootPage(0)`.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__free
public import Spec.go_etcd_io.bbolt.node__free
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__SetRootPage
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free
public import Proof.go_etcd_io.bbolt.Write.Free
public import Proof.go_etcd_io.bbolt.Rebalance.Free
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap

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

/-- The free walk's invariant: the records with the positions `ps` freed, the freelist with
their extents freed, and the callback's `tx` variable. -/
def freeI (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec)
    (txp : Loc) (ps : List w64) : IProp GF :=
  iprop(∃ (Y : WX) (w' : WDb), wtxW K tx r m Y ∗ wdbW K tx X.v w' ∗ txp ↦ tx ∗
    ⌜Write.freedAt X Y bl B ps ∧
      w' = w.withFl (w.fl.freeAll w.wtxid (ps.filterMap (X.posExtent bl)))⌝)

theorem freeI_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc)
    (B : BRec) (txp : Loc) (hB : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB)
    (hlive : ∀ l r, B.ns !! l = some r → l ∈ X.live) :
    ⊢ Write.walkAcc K tx r m X bl B (freeI (GF := GF) K tx r m X w bl B txp) := by
  unfold Write.walkAcc
  iintro !> %ps HI
  unfold freeI
  icases HI with ⟨%Y, %w', Hw, Hdb, Htx, %Hf⟩
  iexists Y
  iframe Hw
  isplitl []
  · ipureintro; exact Write.freedAt_walkSame X Y bl B ps hB hl hlive Hf.1
  iintro Hw
  iexists Y, w'
  iframe
  ipureintro; exact Hf

/-- **`b.forEachPageNode(fn)` of a bucket with a root page**: its page field nil, the walk from
its root, over a finite tree `t` of its logical tree. -/
theorem forEachPageNode_tree (hpn : Bucket.pageNode_w.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hIP : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc) (t : RTree)
    (hB : X.t.bs !! bl = some B) (hloc : bktLocalOK X bl) (h0 : B.ib.root' ≠ W64 0)
    (hpm : ∀ pid ∈ Q, X.t.pm !! pid = none) (ht : ltIs (ltree X) bl t)
    (htp : t.pid = B.ib.root') (hQ : t.pos <+: Q) :
    ⊢ Write.walkAcc K tx r m X bl B I -∗ Write.walkCb X B I Q fn -∗
      ∀ Φ, I [] -∗ ▷ (I t.pos -∗ Φ #()) -∗
      WP (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"forEachPageNode")) (Val #fn))
        {{ Φ }} := by
  obtain ⟨-, B0, hB0, hclean, -⟩ := id hloc
  rw [hB] at hB0; cases hB0
  have hpg0 : B.bv.page' = null := hclean.2.2.2.2.2.1 h0
  iintro #Hacc #Hcb %Φ HI HΦ
  wp_method_call; wp_call
  wp_auto
  icases Write.walk_open K tx r m X bl B I [] $$ Hacc HI with ⟨%Y, Hw, %Hs, Hback⟩
  obtain ⟨-, -, hlY, B', hB', hib', hbv', -⟩ := Hs
  icases wtxW_pkgInit K tx r m Y $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxW_bkt_acc K tx r m Y bl B' hB' $$ Hw with ⟨Ho, Hwb⟩
  rw [decide_eq_true hlY]
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  rw [hbv', hib']
  wp_auto
  rw [decide_eq_true hpg0]
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iframe
  ihave Hw := Hwb $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · simp only [objOwn]; rw [hbv', hib']; iframe
  ihave HI := Hback $$ Hw
  have hh : ltIs (ltree X) bl t ∧ ([] ++ t.pos) <+: Q := ⟨ht, by simpa using hQ⟩
  ihave #Hwk := Write.walk_aux hpn hIB hCnt hBE hBP hIP K tx r m X bl B I Q fn hB hloc h0 hpm
    $$ Hacc Hcb
  rw [← htp]
  wp_apply Hwk $$ %t %([] : List w64) %(W64 0) %hh [HI] as HI
  · iexact HI
  iapply HΦ
  simp only [List.nil_append]
  iexact HI

theorem wtxW_heapOK' (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜heapOK (GF := GF) tx X⌝ ∗ wtxW K tx r m X := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hrest⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  isplitr
  · ipureintro; exact Hok
  · iframe
    ipureintro; exact Hr

theorem Bucket.free.wp_proof (hpn : Bucket.pageNode_w.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hSRP : internal.common.InBucket.SetRootPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hIP : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (hnf : node.free.spec (GF := GF) (hG := hG)) :
    Bucket.free.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w bl B hB hlive hpre
  wp_start as ⟨Hw, Hdb⟩
  icases wtxW_heapOK' K tx r m X $$ Hw with ⟨%Hok, Hw⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  have hbtx : B.bv.tx' = tx := Hok.2.2.1 bl B hB
  icases wtxW_bkt_acc K tx r m X bl B hB $$ Hw with ⟨Ho, Hwb⟩
  rw [decide_eq_true hlive]
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
  obtain ⟨hloc, hpmall, hcan, hrt, htxid⟩ := hpre h0
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
  obtain ⟨t, ht, htp, hht, -⟩ := hrt
  have hrp : X.rootPid bl = B.ib.root' := by simp only [WX.rootPid, hB, Option.map_some, Option.getD_some]
  have hpos : X.positions bl = t.pos := positions_rt X bl t ht htp hht
  obtain ⟨-, B0, hB0, hclean, -, -, hnsl, hvw⟩ := id hloc
  rw [hB] at hB0; cases hB0
  ihave #Hacc := freeI_acc K tx r m X w bl B tx_ptr hB hlive hnsl
  rw [recv_eq_func_mk]
  wp_apply (forEachPageNode_tree hpn hRP hIB hCnt hBE hBP hIP K tx r m X bl B
    (freeI K tx r m X w bl B tx_ptr) (X.positions bl) _ t hB hloc h0 hpmall ht (htp.trans hrp)
    (by rw [hpos]; exact List.prefix_refl _)) $$ Hacc [] [Hw Hdb tx]
  · unfold Write.walkCb
    iintro !> %ps %pid %p %n %d
    wp_start as ⟨HI, %Hc⟩
    obtain ⟨hpq, hpr⟩ := Hc
    have hpidm : pid ∈ X.positions bl := hpq.subset (by simp)
    unfold freeI
    icases HI with ⟨%Y, %w', Hw, Hdb, Htx, %Hf⟩
    obtain ⟨hfr, rfl⟩ := Hf
    have hcanP : w.fl.canFreeAll w.wtxid ((X.positions bl).filterMap (X.posExtent bl)) := hcan
    unfold Write.posRef at hpr
    cases hres : resolve B pid with
    | some l =>
      rw [hres] at hpr
      obtain ⟨rfl, rfl⟩ := hpr
      have hnm : B.nm !! pid = some n := by unfold resolve at hres; rwa [if_neg h0] at hres
      obtain ⟨hlnn, rn, hrn, hrpid⟩ := hclean.2.2.2.2.1 pid n hnm
      have hnc := hclean.2.2.2.2.2.2.2.1 n rn hrn
      have htw : treeWF X.v.pages X.t.mv.pgid'.toNat pid.toNat := by
        have := hnc.2.2.2.2.2.2.2.2.2.1 h0; rwa [hrpid] at this
      obtain ⟨pg, hpg⟩ : ∃ pg, X.v.pages !! pid.toNat = some pg := by
        cases htw with | page _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩
      obtain ⟨h2, -, hid, hlen, hfl⟩ := Read.treeWF_page _ _ _ htw pg hpg
      have hp0 : pid ≠ W64 0 := by intro h; rw [h] at h2; simp at h2
      have he := Write.posExtent_node X bl B pid n rn pg hB hres hrn hrpid hp0 hpg
      have hnot := Write.node_once w.fl w.wtxid X bl B (X.positions bl) ps pid n _ hB (by simp)
        hpq hres he hcanP
      obtain ⟨hYn, hfr'⟩ := Write.freedAt_node X Y bl B ps pid n rn hres hrn hnot hfr
      have hcf := Write.canFree_at w.fl w.wtxid _ (X.positions bl) ps pid _ hpq he hcanP
      obtain ⟨ns', rfl, -⟩ := hfr
      wp_auto
      have hbk : rn.nv.bucket' = bl := hnc.1
      wp_apply hnf K tx r m _ (w.withFl (w.fl.freeAll w.wtxid (ps.filterMap (X.posExtent bl)))) bl n rn hYn hbk
        (fun _ => ⟨by rw [hrpid]; exact hpmall pid hpidm, by exact htxid, pg, by rw [hrpid]; exact hpg,
          by omega, by rw [hrpid]; exact hid, hfl, by rw [hrpid]; exact hcf⟩) $$ [Hw Hdb]
        as ⟨%X', %w'', Hw, Hdb, %Hpost⟩
      · iframe
      iapply HΦ
      iexists X', w''
      iframe
      ipureintro
      rcases Hpost with ⟨h, -⟩ | ⟨pg', -, hpg', rfl, rfl⟩
      · exact absurd (hrpid ▸ h) hp0
      rw [hrpid] at hpg' ⊢
      have : X.v.pages !! pid.toNat = some pg' := hpg'
      rw [hpg] at this; cases this
      refine ⟨hfr', ?_⟩
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he,
        Write.freeAll_append, Write.freeAll_cons]
      rfl
    | none =>
      rw [hres] at hpr
      obtain ⟨rfl, pg0, hw0⟩ := hpr
      have hw0' := hw0
      unfold wpageAt at hw0'
      rw [if_neg h0] at hw0'
      obtain ⟨pg, hpg, hpe⟩ := Option.map_eq_some_iff.mp hw0'
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      obtain ⟨h2, hid, h4096, hfl⟩ := Read.viewWF_page X.v hvw _ pg hpg
      have hp0 : pid ≠ W64 0 := by intro h; rw [h] at h2; simp at h2
      have he := Write.posExtent_page X bl B pid pg hB hres hp0 hpg
      have hcf := Write.canFree_at w.fl w.wtxid _ (X.positions bl) ps pid _ hpq he hcanP
      have hfr' := Write.freedAt_page X Y bl B ps pid hres hfr
      obtain ⟨ns', rfl, -⟩ := hfr
      rw [show (X.v.base +ₗ ((pid.toNat * 4096 : Nat) : Int)) = pageLoc X.v pid.toNat from rfl]
      unfold wtxW wtxCore
      icases Hw with ⟨⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
      unfold wtxHeap
      icases Hh with ⟨%Hok', Hf, Hrf, Hm, Hbk'⟩
      unfold txFields
      icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
      have hv : (X.setBkt bl { B with ns := ns' }).v = X.v := rfl
      have ht : (X.setBkt bl { B with ns := ns' }).t.t = X.t.t := rfl
      have hmv' : (X.setBkt bl { B with ns := ns' }).t.mv = X.t.mv := rfl
      rw [hv, ht, hmv']
      icases viewCells_page_acc _ _ pid.toNat pg hpg $$ Hcells with ⟨Hpg, Hcells⟩
      have hpgne : pg ≠ [] := by intro h; rw [h] at h4096; simp at h4096
      ihave %Hpos := bytesPointsto_pos _ _ _ hpgne $$ Hpg
      have hpnn : pageLoc X.v pid.toNat ≠ null := by intro e; rw [e] at Hpos; simp [null] at Hpos
      obtain ⟨w0, hw0e⟩ : ∃ w0, w0 = w.withFl (w.fl.freeAll w.wtxid (ps.filterMap (X.posExtent bl))) :=
        ⟨_, rfl⟩
      rw [← hw0e]
      have hfl0 : w0.fl = w.fl.freeAll w.wtxid (ps.filterMap (X.posExtent bl)) := by subst hw0e; rfl
      have hwt0 : w0.wtxid = w.wtxid := by subst hw0e; rfl
      unfold wdbW wdbLive wdbCoreG
      icases Hdb with ⟨⟨⟨%wa, Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok⟩
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
      iexists X.setBkt bl { B with ns := ns' }, w0.withFl (w0.fl.freePages w0.wtxid pid (1 + pageOverflow pg))
      rw [hv, ht, hmv']
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
      refine ⟨hfr', ?_⟩
      subst hw0e
      simp only [WDb.withFl, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, he,
        Write.freeAll_append, Write.freeAll_cons]
      rfl
  · unfold freeI
    iexists X, w
    iframe
    ipureintro
    exact ⟨Write.freedAt_nil X bl B hB, rfl⟩
  iintro HI
  unfold freeI
  icases HI with ⟨%Y, %w', Hw, Hdb, Htx, %Hf⟩
  obtain ⟨⟨ns', rfl, hns⟩, rfl⟩ := Hf
  icases wtxW_open K tx r m _ $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hwback⟩
  have hlY : bl ∈ (X.setBkt bl { B with ns := ns' }).liveB := hlive
  icases wtxHeap_bkt_acc tx (DFrac.own 1) _ bl _ (Write.setBkt_lookup X bl _) hlY $$ Hh
    with ⟨Ho, Hhb⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply hSRP $$ [Hib] as Hib
  · iframe
  ihave Hh := Hhb $$ %({ B with ns := ns', ib := { B.ib with root' := W64 0 } } : BRec) %hbtx
    [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · simp only [objOwn]; iframe
  ihave Hw := Hwback $$ %_ [] Hh Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iapply HΦ
  iexists _, _
  iframe
  ipureintro
  refine Or.inr ⟨h0, ⟨B, ns', hB, by rw [Write.setBkt_setBkt], ?_⟩, by rw [WX.extents, hpos]⟩
  rw [hpos]
  exact Write.freedAt_ns B t.pos ns' hns

end proof

end bbolt
end EtcdGrove
end Perennial
