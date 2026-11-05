/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__pageNode_d.lean` (U7n, `notes/bbolt-proof-plan.md`):
the dead bucket's record out of the writer's heap (a `bobjs` entry), its header's root
(`InBucket.RootPage`), its nil node cache, and U4's `Tx.page` over the view.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__pageNode_d
public import Spec.go_etcd_io.bbolt.Tx__page
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Proof.go_etcd_io.bbolt.Write.WalkDeadDefs

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

theorem Bucket.pageNode_d.wp_proofQ (hpage : Tx.page.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc) (B : BRec) (id : w64)
    (pg : List w8) (hbs : X.t.bs !! bl = none) (hd : X.t.deadB !! bl = some B)
    (hlive : bl ∉ X.liveB) (htx : B.bv.tx' = tx) (hnil : B.bv.nodes' = null)
    (h0 : B.ib.root' ≠ W64 0) (hpg : X.v.pages !! id.toNat = some pg)
    (hpmn : X.t.pm !! id = none) (h16 : 16 ≤ pg.length) (hpid : pageId pg = id.toNat)
    (hfl : pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) :
  {{ wtxWQ (GF := GF) K tx r m q X }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ RET (PairV #(pageLoc X.v id.toNat) #null); wtxWQ K tx r m q X }} := by
  unfold wtxWQ wtxCoreQ wtxHeap
  wp_start as ⟨⟨#Hpk, #Hcore, %Hr, #Hreg, ⟨%Hok, Htf, Hrf, Hnobjs, Hobjs⟩, Hfills, Hbk, Hnl, Hdb, #Hvo, Hst⟩,
    Hcells, ⟨%l, Hmf⟩⟩
  have hobj := bobjs_dead X.t bl B hbs hd
  icases (BigSepM.bigSepM_lookup_acc hobj).1 $$ Hobjs with ⟨Hb, Hobjs⟩
  rw [show decide (bl ∈ X.liveB) = false from decide_eq_false hlive]
  simp only [objOwn]
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iexact Hib
  rw [decide_eq_false h0]
  wp_auto
  rw [show decide (B.bv.nodes' = map.nil) = true from decide_eq_true hnil]
  wp_auto
  icases Hmf with ⟨Hmf, %Hl⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  simp only [mapFields]
  icases Hmf with ⟨Hdref, Hdata, Hm0, Hm1, %Hlen⟩
  have hb : id.toNat * 4096 < 0xFFFFFFFFFFFF := pageIdx_lt_maxMap id.toNat l (Hl id.toNat pg hpg) Hlen.1
  icases viewCells_page_acc _ X.v id.toNat pg hpg $$ Hcells with ⟨Hpg, Hcells⟩
  simp only [pageLoc]
  simp only [txFields]
  icases Htf with ⟨Hw, Hm, Hmeta, Hpgs, Hch, Hwf, Hmv, Hpm, Hbufs⟩
  ihave %Hpmnn := ownMap_not_nil _ _ _ $$ Hpm
  have Hsp := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"pages"]) X.t.t.pages'
    (QpMul q (1 : Qp).half) (QpMul q (1 : Qp).half)
  rw [qpMul_half_add] at Hsp
  icases Hsp.1 $$ Hpgs with ⟨Hp1, Hp2⟩
  have Hsd := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"db"]) r.db
    (QpMul q (1 : Qp).half) (QpMul q (1 : Qp).half.half)
  rw [← txDbQ_eq] at Hsd
  icases Hsd.1 $$ Hdb with ⟨Hd1, Hd2⟩
  ihave #Hps := BC.core_pageSize K $$ Hcore
  rw [Hr.1] at Hsd ⊢
  by_cases hbr : bl = B.bv.tx'.[Tx, go!"root"]
  all_goals first | rw [if_pos hbr] | rw [if_neg hbr]
  all_goals
    wp_auto
    rw [htx]
    wp_apply (hpage tx K.db X.t.t.pages' X.t.pm X.v.base id
      (X.v.base +ₗ ((id.toNat * 4096 : Nat) : Int)) pg (DFrac.own (QpMul q (1 : Qp).half))
      (DFrac.own q) (DFrac.own (QpMul q (Qp.half 1).half)) (DFrac.own (QpMul q wq))
      (Or.inr ⟨hpmn, Hnn, hb, rfl⟩) h16 hpid (by rcases hfl with h | h <;> simp [h]))
      $$ [Hp1 Hpm Hd1 Hdata Hpg] as ⟨Hp1, Hpm, Hd1, Hdata, Hpg⟩
    · iframe; iframe #; rw [if_neg (show ¬ X.t.t.pages' = null from Hpmnn)]; iframe
    rw [if_neg (show ¬ X.t.t.pages' = null from Hpmnn)]
    ihave Hcells := Hcells $$ Hpg
    ihave Hobjs := Hobjs $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
    · iframe
    ihave Hpgs := Hsp.2 $$ [Hp1 Hp2]
    · iframe
    ihave Hdb := Hsd.2 $$ [Hd1 Hd2]
    · iframe
    iapply HΦ
    iframe; iframe #
    ipureintro
    exact ⟨⟨⟨rfl, Hr.2⟩, Hok⟩, ⟨Hlen, Hl⟩⟩

theorem Bucket.pageNode_d.wp_proof (hpage : Tx.page.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Bucket.pageNode_d.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B id pg hbs hd hlive htx hnil h0 hpg hpmn h16 hpid hfl
  have h := Bucket.pageNode_d.wp_proofQ hpage hRP K tx r m 1 X bl B id pg hbs hd hlive htx hnil h0
    hpg hpmn h16 hpid hfl
  simp only [wtxWQ_one] at h
  exact h

end proof

end bbolt
end EtcdGrove
end Perennial
