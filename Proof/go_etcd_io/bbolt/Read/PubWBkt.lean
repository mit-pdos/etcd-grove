/-
U6x (`notes/bbolt-proof-plan.md`, "Writer reads at a fraction"): what a writer's `Tx.Bucket`
needs. Pure: the data's lookup of a top-level bucket from the root's entries
(`wtxData_none_of`, `wtxData_some_of`), and what `Bucket.Bucket_w`'s open of a top-level bucket
keeps (`wrFacts_bktOpened`; `flViewU`'s is `Read/PubWBktFl.flViewU_bktOpened_root'`). Separation: an opened child's `tx`
field (persistent).
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubWGet
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Proof.go_etcd_io.bbolt.Read.WOpen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace PubW

section pure
variable [GooseExts]

theorem mem_rootEnts (X : WX) (k v : List w8) (h : (k, v) ∈ rootEnts X) :
    ∃ w ∈ X.allEnts X.rl, isBktFlag w.flags ∧ w.key = k ∧ w.value = v := by
  unfold rootEnts at h
  unfold WX.allEnts
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_flatten] at h ⊢
  obtain ⟨ws, hws, w, hw, he⟩ := h
  by_cases hf : isBktFlag w.flags
  · simp only [hf, decide_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at he
    exact ⟨w, ⟨ws, hws, hw⟩, hf, he.1, he.2⟩
  · simp [hf] at he

/-- **No bucket entry `n` in the root, no bucket `n`.** -/
theorem wtxData_none_of (X : WX) (n : GoString)
    (h : ¬ ∃ w ∈ X.allEnts X.rl, w.key = n ∧ isBktFlag w.flags) : (wtxData X) !! n = none := by
  rw [Write.wtxData_lookup]
  unfold bktData
  cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
  | none => rfl
  | some e =>
    exfalso
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp only [decide_eq_true_eq] at he
    obtain ⟨w, hw, hf', hk, -⟩ := mem_rootEnts X e.1 e.2 hm
    exact h ⟨w, hw, hk.trans he, hf'⟩

/-- **An opened top-level bucket `n` is a bucket of the data.** -/
theorem wtxData_some_of (X : WX) (hok : wOK X) (n : GoString) (c : Loc)
    (hb : bktLoc X n = some c) : (wtxData X) !! n ≠ none := by
  rw [Write.wtxData_lookup]
  unfold bktData
  obtain ⟨v0, hv0⟩ := Write.bktLoc_rootEnt X hok n c hb
  cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
  | none =>
    have := List.find?_eq_none.1 hf (n, v0) hv0
    simp at this
  | some e => simp

theorem nodeRootIn_congr {B B' : BRec} (hns : B'.ns = B.ns) {a b : Loc} (h : nodeRootIn B a b) :
    nodeRootIn B' a b := by
  induction h with
  | top n r hr hp => exact .top n r (hns ▸ hr) hp
  | up n rt r hr hp _ ih => exact .up n rt r (hns ▸ hr) hp ih

theorem descIn_congr {B B' : BRec} (hns : B'.ns = B.ns) {a b : Loc} (h : descIn B a b) :
    descIn B' a b := by
  induction h with
  | self n => exact .self n
  | child n c d r hr hc _ ih => exact .child n c d r (hns ▸ hr) hc ih

/-- **A bucket's open keeps the writer's carried facts** (`wrFacts`), from a live bucket. -/
theorem wrFacts_bktOpened (X X' : WX) (bl c : Loc) (name : List w8) (g : Nat)
    (h : bktOpened X X' bl c name g) (hl : bl ∈ X.liveB) (hrs : (X.t.bs !! X.rl).isSome)
    (hw : wrFacts X) : wrFacts X' := by
  obtain ⟨B, C, w, hB, -, -, -, hbm, -, hcfresh, -, -, -, -, -, hCns, -, -, hX'⟩ := h
  have hbsc : X.t.bs !! c = none := by
    cases e : X.t.bs !! c with
    | none => rfl
    | some D =>
      have := bobjs_bkt X.t c D e
      rw [Option.isNone_iff_eq_none] at hcfresh; rw [hcfresh] at this; cases this
  have hcbl : c ≠ bl := by intro e; subst e; rw [hB] at hbsc; cases hbsc
  have hcrl : c ≠ X.rl := by intro e; rw [e] at hbsc; rw [hbsc] at hrs; cases hrs
  obtain ⟨⟨hrb, hrn⟩, hch, hroot⟩ := hw
  have hlk : ∀ d, X'.t.bs !! d =
      if c = d then some C else if bl = d then some { B with bm := B.bm.insert name c }
      else X.t.bs !! d := by
    intro d; rw [hX']; simp only [GMap.lookup_insert_eq_iff]
  have hrl' : X'.rl = X.rl := by rw [hX']
  have hlive' : X'.live = X.live := by rw [hX']
  have hliveB' : X'.liveB = X.liveB.insert c () := by rw [hX']
  have htt : X'.t.t = X.t.t := by rw [hX']
  have hreach : ∀ d, bktReach X d → bktReach X' d := by
    intro d hd
    induction hd with
    | root => rw [← hrl']; exact .root
    | child d0 d1 D n hD hn _ ih =>
      by_cases h0 : bl = d0
      · subst h0
        rw [hB] at hD; cases hD
        refine .child bl d1 { B with bm := B.bm.insert name c } n ?_ ?_ ih
        · rw [hlk, if_neg hcbl, if_pos rfl]
        · simp only [GMap.lookup_insert_eq_iff]
          split
          · rename_i he; subst he; rw [hbm] at hn; cases hn
          · exact hn
      · have hc0 : c ≠ d0 := by intro e; subst e; rw [hbsc] at hD; cases hD
        exact .child d0 d1 D n (by rw [hlk, if_neg hc0, if_neg h0]; exact hD) hn ih
  have hlv' : ∀ d, c ≠ d → d ∈ X.liveB.insert c () → d ∈ X.liveB := by
    intro d hd h
    rw [GMap.mem_iff, GMap.lookup_insert_eq_iff, if_neg hd] at h
    exact h
  refine ⟨⟨?_, ?_⟩, htt ▸ hch, ?_⟩
  · intro d D hD hlv
    rw [hliveB'] at hlv
    rw [hlk] at hD
    split at hD
    · rename_i he; subst he
      refine .child bl c { B with bm := B.bm.insert name c } name ?_ ?_ (hreach bl (hrb bl B hB hl))
      · rw [hlk, if_neg hcbl, if_pos rfl]
      · simp only [GMap.lookup_insert_eq_iff, ↓reduceIte]
    · rename_i hcd
      split at hD
      · rename_i he; subst he
        exact hreach bl (hrb bl B hB hl)
      · exact hreach d (hrb d D hD (hlv' d hcd hlv))
  · intro d D l r hD hr hlv
    rw [hlive'] at hlv
    rw [hlk] at hD
    split at hD
    · cases hD
      rw [hCns] at hr; cases hr
    · split at hD
      · rename_i he; subst he
        cases hD
        obtain ⟨rt, h1, h2⟩ := hrn bl B l r hB hr hlv
        exact ⟨rt, nodeRootIn_congr (B := B) (B' := { B with bm := B.bm.insert name c }) rfl h1, descIn_congr (B := B) (B' := { B with bm := B.bm.insert name c }) rfl h2⟩
      · exact hrn d D l r hD hr hlv
  · intro B0 hB0 k c' hk
    rw [hrl'] at hB0 ⊢
    rw [hlk] at hB0
    split at hB0
    · rename_i he; exact absurd he hcrl
    · split at hB0
      · rename_i he
        cases hB0
        simp only [GMap.lookup_insert_eq_iff] at hk
        split at hk
        · cases hk; exact hcrl
        · exact hroot B (he ▸ hB) k c' hk
      · exact hroot B0 hB0 k c' hk

end pure

end PubW

section wq
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's registration** (persistent, a writer's) out of `wtxWQ`. -/
theorem wtxWQ_reg_rw (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ reg tx K.B r ∗ ⌜r.rw = true⌝ := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  iframe; iframe #
  isplitr
  · ipureintro; exact Hr
  ipureintro; exact Hr.2.1

/-- **A child bucket's `tx` field** (persistent: it is not the root), out of `wtxWQ`. -/
theorem wtxWQ_child_tx (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (c : Loc)
    (C : BRec) (hb : X.t.bs !! c = some C) (hc : c ≠ X.rl) (hok : heapOK (GF := GF) tx X) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ c.[Bucket, go!"tx"] ↦□ tx := by
  have htx : C.bv.tx' = tx := (hok.2.2.1 c C hb).1
  have hne : ¬ c = C.bv.tx'.[Tx, go!"root"] := by
    rw [htx]; intro e; exact hc (e.trans hok.1.symm)
  iintro Hw
  icases wtxWQ_bkt_acc K tx r m q X c C hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  rw [if_neg hne]
  icases H2 with #H2
  ihave Hw := Hback $$ [H1 H3 H4 H5 H6 H7 H8 H9 H10]
  · isimp only [objOwn]; rw [if_neg hne]; iframe; iframe #
  iframe
  rw [← htx]; iexact H2

end wq

end bbolt
end EtcdGrove
end Perennial
