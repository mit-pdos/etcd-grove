/-
A bucket of the writer's heap, out and back (U5 of `notes/bbolt-proof-plan.md`):
`wtxHeap_bkt_acc'`, `Inv/Ctx.lean`'s `wtxHeap_bkt_acc` with the premise it needs: the new
record's `tx` field is the transaction (`heapOK`'s third clause; nothing ties the caller's new
record to it otherwise, and the root bucket's `tx` field is not persistent, so the heap cannot keep
a copy to compare with). Over U8's `objs_bkt`/`objs_node`/`objs_other` (`Rebalance/Objs.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Rebalance.Objs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The transaction with bucket `bl`'s record replaced by `B'`, its nodes `B`'s. -/
theorem setBkt_t_bs (X : WX) (bl : Loc) (B B' : BRec) (k : Loc) :
    (X.setBkt bl { B' with ns := B.ns }).t.bs !! k =
      if k = bl then some { B' with ns := B.ns } else X.t.bs !! k := by
  unfold WX.setBkt
  by_cases h : k = bl
  · subst h; simp
  · simp only [h, ↓reduceIte]; exact GMap.lookup_insert_ne _ _ (Ne.symm h)

/-- The nodes of every bucket are unchanged by replacing a bucket's record, its nodes kept. -/
theorem setBkt_ns (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B) (k : Loc)
    (C : BRec) (hC : (X.setBkt bl { B' with ns := B.ns }).t.bs !! k = some C) :
    ∃ C0, X.t.bs !! k = some C0 ∧ C.ns = C0.ns ∧ (k ≠ bl → C = C0) := by
  rw [setBkt_t_bs] at hC
  by_cases h : k = bl
  · subst h; simp only [↓reduceIte, Option.some.injEq] at hC; subst hC
    exact ⟨B, hb, rfl, fun h => absurd rfl h⟩
  · simp only [h, ↓reduceIte] at hC
    exact ⟨C, hC, rfl, fun _ => rfl⟩

theorem objsDisj_setBkt (X : WX) (bl : Loc) (B B' : BRec) (hd : objsDisj X.t)
    (hb : X.t.bs !! bl = some B) : objsDisj (X.setBkt bl { B' with ns := B.ns }).t := by
  intro c C hC n hn c' C' hC' hne
  obtain ⟨C0, hC0, hns, -⟩ := setBkt_ns X bl B B' hb c C hC
  rw [hns] at hn
  obtain ⟨C0', hC0', hns', -⟩ := setBkt_ns X bl B B' hb c' C' hC'
  rw [hns']; exact hd c C0 hC0 n hn c' C0' hC0' hne

/-- **The nodes are unchanged by replacing a bucket's record, its nodes kept.** -/
theorem objs_setBkt (X : WX) (bl : Loc) (B B' : BRec) (hd : objsDisj X.t)
    (hb : X.t.bs !! bl = some B) :
    (X.setBkt bl { B' with ns := B.ns }).t.objs = X.t.objs := by
  have hd' := objsDisj_setBkt X bl B B' hd hb
  apply GMap.map_eq
  intro k
  by_cases hkn : ∃ c C rk, X.t.bs !! c = some C ∧ C.ns !! k = some rk
  · obtain ⟨c, C, rk, hC, hrk⟩ := hkn
    rw [objs_node X.t c C k rk hd hC hrk]
    by_cases hcb : c = bl
    · subst hcb
      rw [hb] at hC; cases hC
      exact objs_node _ c { B' with ns := B.ns } k rk hd' (by rw [setBkt_t_bs]; simp) hrk
    · exact objs_node _ c C k rk hd' (by rw [setBkt_t_bs]; simp [hcb, hC]) hrk
  · have hno : ∀ c C, X.t.bs !! c = some C → C.ns !! k = none := by
      intro c C hC
      cases h : C.ns !! k with
      | none => rfl
      | some rk => exact absurd ⟨c, C, rk, hC, h⟩ hkn
    rw [objs_other X.t k hno, objs_other]
    · rfl
    intro c C hC
    obtain ⟨C0, hC0, hns, -⟩ := setBkt_ns X bl B B' hb c C hC
    rw [hns]; exact hno c C0 hC0

/-- The buckets after replacing a bucket's record. -/
theorem bobjs_setBkt (X : WX) (bl : Loc) (B' : BRec) :
    (X.setBkt bl B').t.bobjs = X.t.bobjs.insert bl B' := by
  apply GMap.map_eq
  intro k
  by_cases hk : k = bl
  · subst hk; simp [WX.setBkt, WTx.bobjs, GMap.lookup_insert]
  · have hk' : bl ≠ k := Ne.symm hk
    simp [WX.setBkt, WTx.bobjs, GMap.lookup_insert_ne _ _ hk', hk']

/-- **A bucket of the writer's heap, out and back** (`wtxHeap_bkt_acc` with its premise: the new
record's `tx` field is the transaction's, its node cache not nil). -/
theorem wtxHeap_bkt_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v bl dq true (WObj.bkt B) ∗
      (∀ B', ⌜B'.bv.tx' = tx ∧ B'.bv.nodes' ≠ null⌝ -∗ objOwn X.v bl dq true (WObj.bkt B') -∗
        wtxHeap tx dq (X.setBkt bl { B' with ns := B.ns })) := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, Hm, Hbk⟩
  have Hd := Hok.2.1
  have Ho := bobjs_bkt X.t bl B hb
  have hlv : decide (bl ∈ X.liveB) = true := by simp [hl]
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hbk with ⟨Hb, Hbk⟩
  rw [hlv]
  iframe Hb
  iintro %B' %Htx Hb
  isplitr
  · ipureintro
    refine ⟨Hok.1, objsDisj_setBkt X bl B B' Hd hb, ?_, ?_, fun m y hm => ?_, ?_⟩
    · intro c C hc
      rw [setBkt_t_bs] at hc
      by_cases hcb : c = bl
      · simp only [hcb, ↓reduceIte, Option.some.injEq] at hc; subst hc; exact Htx
      · simp only [hcb, ↓reduceIte] at hc; exact Hok.2.2.1 c C hc
    · intro c C k rk hc hk
      obtain ⟨C0, hC0, hns, -⟩ := setBkt_ns X bl B B' hb c C hc
      rw [hns] at hk
      exact Hok.2.2.2.1 c C0 k rk hC0 hk
    · show ((X.setBkt bl { B' with ns := B.ns }).t.objs !! m).isSome
      rw [objs_setBkt X bl B B' Hd hb]
      exact Hok.2.2.2.2.1 m y hm
    · intro c C hc
      obtain ⟨C0, hC0, -, -⟩ := setBkt_ns X bl B B' hb c C hc
      exact Hok.2.2.2.2.2 c C0 hC0
  isplitl [Hf]
  · unfold txFields WX.setBkt; iexact Hf
  isplitl [Hrf]
  · iexact Hrf
  rw [objs_setBkt X bl B B' Hd hb, bobjs_setBkt X bl]
  have hv : (X.setBkt bl { B' with ns := B.ns }).v = X.v := rfl
  have hlive : (X.setBkt bl { B' with ns := B.ns }).live = X.live := rfl
  have hliveB : (X.setBkt bl { B' with ns := B.ns }).liveB = X.liveB := rfl
  simp only [hv, hlive, hliveB]
  isplitl [Hm]
  · iexact Hm
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)).2
  simp only [hl, decide_true]
  isplitl [Hb]
  · unfold objOwn pageOwn; iexact Hb
  · iexact Hbk

end heap
end bbolt
end EtcdGrove
end Perennial
