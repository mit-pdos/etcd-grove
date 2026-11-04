/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__free.lean` (U7e, `notes/bbolt-proof-plan.md`), of the
variant `Bucket.free.spec'` (premises the shared spec lacks, see its doc): `RootPage`, the walk
(`Write/Walk`'s `walk_aux` over the bucket's finite tree, `rtOK`), its callback freeing each
position's page (`Free`, a `store_free` step) or node (`node.free`) over the invariant `freeI`
(`Write/Free`'s `freedAt`), and `SetRootPage(0)`.
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

/-- **`Bucket.free.spec` with the premises its proof needs** (U7e): in the tree case, the bucket's
logical tree finite (`rtOK`: the walk visits `X.positions bl`), the writer's txid the one `Free`
is given (`tx.meta.Txid()`), and no position (a page's or a node's) in `tx.pages` (`node.free`'s
`Tx.page` premise); `DeleteBucket` has all three from `wOK` (`rtOK_init`, `txClean`), `spill`
from `wOKR`. -/
abbrev Bucket.free.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl : Loc) (B : BRec),
  X.t.bs !! bl = some B → bl ∈ X.liveB →
  (B.ib.root' ≠ W64 0 → bktLocalOK X bl ∧
    (∀ pid ∈ X.positions bl, X.t.pm !! pid = none) ∧
    w.fl.canFreeAll w.wtxid (X.extents bl) ∧ rtOK X bl ∧ X.t.mv.txid' = w.wtxid) →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X.v w' ∗
      ⌜(B.ib.root' = W64 0 ∧ X' = X ∧ w' = w) ∨
       (B.ib.root' ≠ W64 0 ∧ bktFreed X X' bl ∧
         w' = w.withFl (w.fl.freeAll w.wtxid (X.extents bl)))⌝ }}

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

theorem Bucket.free.wp_proof' (hpn : Bucket.pageNode_w.spec (GF := GF) (hG := hG))
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
    Bucket.free.spec' (GF := GF) (hG := hG) := by
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
      -- a page position: `tx.db.freelist.Free(tx.meta.Txid(), p)` (node__free.lean's `Free`
      -- part without `Tx.page`: the header from the view cells, `store_free`, `wdbOK_free`); the
      -- pure facts are `Write.posExtent_page`, `Write.canFree_at`, `Write.freedAt_page`. U7e WIP.
      sorry
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

/-- The shared statement: its premises do not give `rtOK`, the txid, or `tx.pages` at the node
positions (`Bucket.free.spec'`); a `sorry` until the shared spec takes them. -/
theorem Bucket.free.wp_proof : Bucket.free.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
