/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__pageNode_w.lean` (U6, `notes/bbolt-proof-plan.md`):
the bucket's record out of the writer's heap (`objs_bkt`), its header's root (`InBucket.RootPage`),
its node cache, else U4's `Tx.page` over the transaction's page cache and the view.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.Tx__page
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

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

theorem Bucket.pageNode_w.wp_proof (hpage : Tx.page.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Bucket.pageNode_w.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B id hB hlive hinl hnodes hnn hres
  unfold wtxW wtxCore wtxHeap
  wp_start as ⟨⟨#Hpk, #Hcore, %Hr, #Hreg, ⟨%Hok, Htf, Hrf, Hnobjs, Hobjs⟩, Hfills, Hbk, Hnl, Hdb, #Hvo, Hst⟩,
    Hcells, ⟨%l, Hmf⟩⟩
  have hobj := bobjs_bkt X.t bl B hB
  icases (BigSepM.bigSepM_lookup_acc hobj).1 $$ Hobjs with ⟨Hb, Hobjs⟩
  rw [show decide (bl ∈ X.liveB) = true from decide_eq_true hlive]
  simp only [objOwn]
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iexact Hib
  ihave %Hnmnn := ownMap_not_nil _ _ _ $$ Hnm
  -- what the post asks, once the heap is back
  wp_if_destruct
  · -- an inline bucket: position 0, its root node or its page
    obtain rfl := hinl (by assumption)
    wp_auto
    wp_if_destruct
    · ihave Hobjs := Hobjs $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
      · iframe
      iapply HΦ
      iframe; iframe #
      ipureintro
      simp [resolve, wpageAt, *]
    · ihave Hobjs := Hobjs $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
      · iframe
      iapply HΦ
      iframe; iframe #
      ipureintro
      simp [resolve, *]
  · rw [show decide (B.bv.nodes' = map.nil) = false from decide_eq_false Hnmnn]
    wp_auto
    wp_apply wp_map_lookup1 $$ [Hnm] as Hnm
    · iexact Hnm
    wp_if_destruct
    · -- not materialized: the page, through `tx.page`
      have Hroot0 : ¬ B.ib.root' = W64 0 := by assumption
      have htx : B.bv.tx' = tx := Hok.2.2.1 bl B hB
      have hnm : B.nm !! id = none := by
        cases hl : B.nm !! id with
        | none => rfl
        | some l =>
          -- a cached node is never nil (the spec's premise, `bktClean`'s `B.nm` facts)
          exfalso
          exact hnn id l hl (by simp_all)
      have hrn : resolve B id = none := by simp only [resolve, hnm]; rw [if_neg Hroot0]
      obtain ⟨pa, pg, hwp, -, hpgf⟩ := hres hrn
      obtain ⟨hpmn, h16, hpid, hfl, hb⟩ := hpgf Hroot0
      unfold wpageAt at hwp
      rw [if_neg Hroot0] at hwp
      obtain ⟨pg', hpg', hpe⟩ := Option.map_eq_some_iff.mp hwp
      simp only [Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      icases Hmf with ⟨Hmf, %Hl⟩
      ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
      simp only [mapFields]
      icases Hmf with ⟨Hdref, Hdata, Hm0, Hm1, %Hlen⟩
      have hbound := Hl id.toNat pg' hpg'
      icases viewCells_page_acc _ X.v id.toNat pg' hpg' $$ Hcells with ⟨Hpg, Hcells⟩
      simp only [pageLoc]
      simp only [txFields]
      icases Htf with ⟨Hw, Hm, Hmeta, Hpgs, Hch, Hwf, Hmv, Hpm, Hbufs⟩
      ihave %Hpmnn := ownMap_not_nil _ _ _ $$ Hpm
      have Hsp := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"pages"]) X.t.t.pages'
        (QpMul 1 (1 : Qp).half) (QpMul 1 (1 : Qp).half)
      rw [qpMul_half_add] at Hsp
      icases Hsp.1 $$ Hpgs with ⟨Hp1, Hp2⟩
      have Hsd := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"db"]) r.db
        (QpMul 1 (1 : Qp).half) (QpMul 1 (1 : Qp).half.half)
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
          (X.v.base +ₗ ((id.toNat * 4096 : Nat) : Int)) pg' (DFrac.own (QpMul 1 (1 : Qp).half))
          (DFrac.own 1) (DFrac.own (Qp.half 1).half) (DFrac.own wq)
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
        refine ⟨⟨⟨⟨rfl, Hr.2⟩, Hok⟩, ⟨Hlen, Hl⟩⟩, ?_⟩
        rw [hrn]
        exact ⟨rfl, pg', by unfold wpageAt; rw [if_neg Hroot0, hpg']; rfl⟩
    · -- a materialized node
      ihave Hobjs := Hobjs $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
      · iframe
      iapply HΦ
      iframe; iframe #
      ipureintro
      refine ⟨⟨Hr, Hok⟩, ?_⟩
      cases hl : B.nm !! id with
      | none => rw [hl] at Hif; exact absurd rfl Hif
      | some l =>
        have Hroot0 : ¬ B.ib.root' = W64 0 := by assumption
        rw [hl] at Hif
        simp only [Option.getD_some] at Hif
        simp only [resolve, hl]; rw [if_neg Hroot0]; simp

end proof

end bbolt
end EtcdGrove
end Perennial
