/-
U7p (`notes/bbolt-proof-plan.md`): **`DeleteBucket`'s child opened** (`dbk_opened`, for
`Write/DelBktWp`): `b.Bucket(newKey)`'s post, the name present, as `DeleteBucket` uses it: the root's
record `R1` caches the child at `n`, its tree that of `R`, the writer's facts kept (the cached case
trivially, the opened case by `gensOK_bktOpened`, `PubW.wrFacts_bktOpened`,
`PubW.flViewU_bktOpened_root'` and `txShape_bktOpened`, as `CreateBucketIfNotExists`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktPath
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsGens
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsOpen
public import Proof.go_etcd_io.bbolt.Read.PubWBkt
public import Proof.go_etcd_io.bbolt.Read.PubWBktFl
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The child opened** (`b.Bucket(newKey)`'s post, the name present): the root's record `R1`
caches it at `n`, its tree that of `R`; the writer's facts kept. -/
theorem dbk_opened (T : TxView) (X X1 : WX) (R : BRec) (c : Loc) (n : GoString) (fl : FLPg)
    (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X) (hwr : wrFacts X)
    (hfl : flViewU X fl) (hR : X.t.bs !! X.rl = some R) (hcn : c ≠ null)
    (hcase : (R.bm !! n = some c ∧ X1 = X) ∨ bktOpened X X1 X.rl c n (T.gen n))
    (hok1 : wOK X1) :
    ∃ R1 C, X1.t.bs !! X.rl = some R1 ∧ R1.bm !! n = some c ∧ sameTreeB R R1 ∧
      X1.t.bs !! c = some C ∧ c ≠ X.rl ∧ X1.rl = X.rl ∧ X1.v = X.v ∧ X1.t.mv = X.t.mv ∧
      gensOK T X1 ∧ wrFacts X1 ∧ flViewU X1 fl ∧
      ∀ γ extra, txShape (GF := GF) γ X extra ⊢ txShape γ X1 extra := by
  rcases hcase with ⟨hbm, hXX⟩ | hop
  · subst X1
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 ((hok.1.2.2.2.2.2 X.rl R hR).2 n c hbm)
    exact ⟨R, C, hR, hbm, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hC, hwr.2.2 R hR n c hbm, rfl, rfl, rfl,
      hgens, hwr, hfl, fun _ _ => .rfl⟩
  · obtain ⟨B, C, w, hB, -, -, -, -, -, hcf, -, -, -, -, -, -, -, -, hX'⟩ := id hop
    rw [hR] at hB; cases hB
    have hcr : c ≠ X.rl := by
      intro e
      rw [e] at hcf
      have := bobjs_bkt X.t X.rl R hR
      rw [Option.isNone_iff_eq_none] at hcf; rw [hcf] at this; cases this
    refine ⟨{ R with bm := R.bm.insert n c }, C, ?_, GMap.lookup_insert _ _ _, sameTreeB_bm _ _, ?_,
      hcr, by rw [hX'], by rw [hX'], by rw [hX'], ?_, ?_, ?_, ?_⟩
    · rw [hX']; simp only
      rw [GMap.lookup_insert_ne _ _ hcr]; exact GMap.lookup_insert _ _ _
    · rw [hX']; exact GMap.lookup_insert _ _ _
    · exact gensOK_bktOpened T X X1 X.rl c n (T.gen n) hop hok.2.2.2.2.1 (Nat.le_refl _)
        (fun _ => rfl) (fun h => absurd rfl h) hgens
    · exact PubW.wrFacts_bktOpened X X1 X.rl c n (T.gen n) hop hok.2.2.2.2.2.1.1
        (by rw [hR]; rfl) hwr
    · exact PubW.flViewU_bktOpened_root' X X1 c n (T.gen n) fl hok hok1 hop hfl
    · exact fun γ extra => txShape_bktOpened γ X X1 X.rl c n (T.gen n) extra hok1 hop

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
