/-
Lean-first (no Rocq counterpart).

# `computeFirstUnk`'s lemmas (2026-11-02)

What `chains.computeFirstUnk`'s proof needs besides the shared definitions: `Check`'s answer as
`Prec` (`linOrder_hb_iff`, `prec_iff_linOrder`), the chains' lengths (`chain_length_le`), the
state after the head operation is visited (`ChSt.visit`: its `visited` flag set and its
`firstUnk` slice's new contents) with the laws of `ShapeOk`, `FuOk` and `clientOwn` on it, and
the bookkeeping of the head operation's `firstUnk` points-to.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.Consistency__Check

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- Resolve the bounds checks (`if 0 ≤ i ∧ i < len then … else Panic …`) of the index expressions
with the given facts, then step (`wp_auto`); repeated while it makes progress. -/
syntax "idx_auto" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| idx_auto [$ts,*]) =>
    `(tactic| repeat (simp only [$ts,*, _root_.and_self, ↓reduceIte]; wp_auto))

namespace github_com.anishathalye.porcupine

open Theory

section pure
variable [GooseExts]

theorem linOrder_hb_iff (a b : Operation) :
    linOrder a b = W64 (-2) ↔ sint.Z a.Return' < sint.Z b.Call' := by
  unfold linOrder
  by_cases h1 : sint.Z a.Return' < sint.Z b.Call'
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    repeat (first | decide | split)

theorem chain_length_le {α : Type} {h : List (Op α)} {cs : List (List Nat)} (hok : ChainsOk h cs)
    (d : Nat) : (chain cs d).length ≤ h.length := by
  have := List.Nodup.length_le_of_subset (l₂ := List.range h.length) (hok.1 d).1
    (fun y hy => List.mem_range.mpr (lt_length_of_mem hok hy))
  simpa using this

theorem coOk_get {h : List (Op OpV)} {ch : List Nat} {vs : List Bool} {cos : List clientOperation}
    (hco : CoOk h ch vs cos) {k : Nat} (hk : k < ch.length) :
    ∃ (co : clientOperation) (o : Op OpV), cos[k]? = some co ∧ h[ch[k]]? = some o ∧
      sint.Z co.Op'.Call' = o.call ∧ sint.Z co.Op'.Return' = o.ret ∧
      co.visited' = vs.getD k false := by
  have hk' : k < cos.length := by rw [hco.1]; exact hk
  obtain ⟨y, o, hy, ho, -, -, -, hc, hr, hv⟩ := hco.2 k cos[k] (List.getElem?_eq_getElem hk')
  rw [List.getElem?_eq_getElem hk] at hy
  cases hy
  exact ⟨cos[k], o, List.getElem?_eq_getElem hk', ho, hc, hr, hv⟩

/-- `Check`'s answer on client `d`'s `j`-th operation and client `c`'s `k`-th is `HardBefore`
exactly when the first precedes the second. -/
theorem prec_iff_linOrder {h : List (Op OpV)} {cs : List (List Nat)} {c d j k : Nat}
    {va vb : List Bool} {cosa cosb : List clientOperation} {a b : clientOperation}
    (hcoa : CoOk h (chain cs d) va cosa) (hcob : CoOk h (chain cs c) vb cosb)
    (hj : j < (chain cs d).length) (hk : k < (chain cs c).length)
    (ha : cosa[j]? = some a) (hb : cosb[k]? = some b) :
    linOrder a.Op' b.Op' = W64 (-2) ↔ Prec h (chain cs d)[j] (opAt cs c k) := by
  obtain ⟨a', oa, ha', hoa, -, hra, -⟩ := coOk_get hcoa hj
  obtain ⟨b', ob, hb', hob, hcb, -, -⟩ := coOk_get hcob hk
  rw [ha] at ha'; cases ha'
  rw [hb] at hb'; cases hb'
  rw [linOrder_hb_iff, opAt_eq hk, hra, hcb]
  constructor
  · intro hlt; exact ⟨oa, ob, hoa, hob, hlt⟩
  · rintro ⟨oa', ob', h1, h2, hlt⟩
    rw [hoa] at h1; cases h1
    rw [hob] at h2; cases h2
    exact hlt

theorem linOrder_ne_conc (a b : Operation) : linOrder a b ≠ W64 3 := by
  unfold linOrder
  repeat (first | decide | split)

/-- Client `d`'s `j`-th operation precedes client `c`'s `k`-th (the searches' test). -/
abbrev PAt {α : Type} (h : List (Op α)) (cs : List (List Nat)) (c k d j : Nat) : Prop :=
  Prec h (opAt cs d j) (opAt cs c k)

/-- The test is downward closed along the chain. -/
theorem pAt_down {α : Type} {h : List (Op α)} {cs : List (List Nat)} (hok : ChainsOk h cs)
    {c k d j j' : Nat} (hj : j < (chain cs d).length) (hj' : j' ≤ j) (hP : PAt h cs c k d j) :
    PAt h cs c k d j' := by
  unfold PAt at *
  rw [opAt_eq hj, ← fu_prefix hok hj] at hP
  rw [opAt_eq (by omega), ← fu_prefix hok (by omega)]
  omega

/-- `Check`'s answer, with the operations by position. -/
theorem pAt_iff_linOrder {h : List (Op OpV)} {cs : List (List Nat)} {c d j k : Nat}
    {va vb : List Bool} {cosa cosb : List clientOperation} {a b : clientOperation}
    (hcoa : CoOk h (chain cs d) va cosa) (hcob : CoOk h (chain cs c) vb cosb)
    (hj : j < (chain cs d).length) (hk : k < (chain cs c).length)
    (ha : cosa[j]? = some a) (hb : cosb[k]? = some b) :
    linOrder a.Op' b.Op' = W64 (-2) ↔ PAt h cs c k d j := by
  unfold PAt
  rw [opAt_eq hj]
  exact prec_iff_linOrder hcoa hcob hj hk ha hb

/-- The searches' result: from `start`, the first index whose operation does not precede, is
`FUe` at `k` (`start` the previous operation's `FUe`, or `0` at the chain's first). -/
theorem fue_of_search {α : Type} {h : List (Op α)} {cs : List (List Nat)} (hok : ChainsOk h cs)
    {c k d r : Nat}
    (hsr : (if 0 < k then FUe h cs c d (k - 1) else 0) ≤ r) (hrl : r ≤ (chain cs d).length)
    (hpre : ∀ j, (if 0 < k then FUe h cs c d (k - 1) else 0) ≤ j → j < r → PAt h cs c k d j)
    (hstop : r < (chain cs d).length → ¬ PAt h cs c k d r) :
    r = FUe h cs c d k := by
  have := fue_search hok hsr hrl
    (fun j hj h1 h2 => by have := hpre j h1 h2; unfold PAt at this; rwa [opAt_eq hj] at this)
    (fun hr hp => hstop hr (by unfold PAt; rwa [opAt_eq hr]))
  rw [this]
  cases k with
  | zero => simp [FUe]
  | succ k => simp [fue_succ]

/-- The head operation's `visited` set, keeping the rest of a client's operation. -/
theorem coOk_set_visited {h : List (Op OpV)} {ch : List Nat} {vs : List Bool}
    {cos : List clientOperation} {k : Nat} {co : clientOperation}
    (hco : CoOk h ch vs cos) (hk : cos[k]? = some co) (hkv : k < vs.length) :
    CoOk h ch (vs.set k true) (cos.set k { co with visited' := true }) := by
  refine ⟨by rw [List.length_set]; exact hco.1, fun k' co' hk' => ?_⟩
  rw [List.getElem?_set] at hk'
  by_cases hkk : k = k'
  · subst hkk
    have hlt : k < cos.length := (List.getElem?_eq_some_iff.mp hk).1
    simp only [hlt, ↓reduceIte, Option.some.injEq] at hk'
    subst hk'
    obtain ⟨y, o, hy, ho, hid, hi, hout, hc, hr, -⟩ := hco.2 k co hk
    refine ⟨y, o, hy, ho, hid, hi, hout, hc, hr, ?_⟩
    simp [List.getD_eq_getElem?_getD, hkv]
  · simp only [hkk, ↓reduceIte] at hk'
    obtain ⟨y, o, hy, ho, hid, hi, hout, hc, hr, hv⟩ := hco.2 k' co' hk'
    refine ⟨y, o, hy, ho, hid, hi, hout, hc, hr, ?_⟩
    rw [hv]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hkk, ↓reduceIte]

end pure

/-! ## The state after a visit -/

/-- Client `c`'s `k`-th operation visited, its `firstUnk` slice holding `fl`. -/
def ChSt.visit (st : ChSt) (c k : Nat) (fl : List w64) : ChSt :=
  { st with vis := st.vis.set c ((st.vis.getD c []).set k true),
            fu := st.fu.set c ((st.fu.getD c []).set k fl) }

theorem getD_set_ne' {β : Type} {l : List β} {c d : Nat} {v d0 : β} (h : d ≠ c) :
    (l.set c v).getD d d0 = l.getD d d0 := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem getD_set_eq' {β : Type} {l : List β} {c : Nat} {v d0 : β} (hc : c < l.length) :
    (l.set c v).getD c d0 = v := by
  simp [List.getD_eq_getElem?_getD, hc]

section visit
variable {α : Type} {h : List (Op α)} {cs : List (List Nat)} {st : ChSt} {c k : Nat} {fl : List w64}

theorem visit_heads : (st.visit c k fl).heads = st.heads := rfl
theorem visit_nDeps : (st.visit c k fl).nDeps = st.nDeps := rfl
theorem visit_frontier : (st.visit c k fl).frontier = st.frontier := rfl
theorem visit_head (c' : Nat) : (st.visit c k fl).head c' = st.head c' := rfl

theorem visit_vis_ne {d : Nat} (hd : d ≠ c) : (st.visit c k fl).vis.getD d [] = st.vis.getD d [] :=
  getD_set_ne' hd

theorem visit_fuAt_ne {d k' : Nat} (hd : d ≠ c) : (st.visit c k fl).fuAt d k' = st.fuAt d k' := by
  unfold ChSt.fuAt ChSt.visit
  simp only
  rw [getD_set_ne' hd]

theorem visit_vis_eq (hshape : ShapeOk cs st) (hc : c < cs.length) :
    (st.visit c k fl).vis.getD c [] = (st.vis.getD c []).set k true := by
  unfold ChSt.visit; simp only
  rw [getD_set_eq' (by rw [hshape.2.2.1]; exact hc)]

theorem visit_visAt (hshape : ShapeOk cs st) (hc : c < cs.length) (hk : k < (chain cs c).length)
    (c' k' : Nat) :
    (st.visit c k fl).visAt c' k' = (st.visAt c' k' || decide (c' = c ∧ k' = k)) := by
  by_cases hcc : c' = c
  · subst hcc
    unfold ChSt.visAt
    rw [visit_vis_eq hshape hc]
    have hkl : k < (st.vis.getD c' []).length := by
      rw [((hshape.2.2.2.2) c' k hk).1]; exact hk
    by_cases hkk : k' = k
    · subst hkk
      simp only [List.getD_eq_getElem?_getD] at hkl
      simp [List.getD_eq_getElem?_getD, hkl]
    · simp [List.getD_eq_getElem?_getD, Ne.symm hkk, hkk]
  · unfold ChSt.visAt
    rw [visit_vis_ne hcc]
    simp [hcc]

theorem visit_fuAt (hshape : ShapeOk cs st) (hc : c < cs.length) (hk : k < (chain cs c).length)
    (c' k' : Nat) :
    (st.visit c k fl).fuAt c' k' = if c' = c ∧ k' = k then fl else st.fuAt c' k' := by
  by_cases hcc : c' = c
  · subst hcc
    unfold ChSt.fuAt ChSt.visit
    simp only
    rw [getD_set_eq' (by rw [hshape.2.2.2.1]; exact hc)]
    have hkl : k < (st.fu.getD c' []).length := by
      rw [((hshape.2.2.2.2) c' k hk).2.1]; exact hk
    by_cases hkk : k' = k
    · subst hkk
      simp only [List.getD_eq_getElem?_getD] at hkl
      simp [List.getD_eq_getElem?_getD, hkl]
    · simp [List.getD_eq_getElem?_getD, Ne.symm hkk, hkk]
  · rw [visit_fuAt_ne hcc]; simp [hcc]

theorem visit_shape (hshape : ShapeOk cs st) (hc : c < cs.length) (hk : k < (chain cs c).length)
    (hfl : fl.length = cs.length) : ShapeOk cs (st.visit c k fl) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hshape
  refine ⟨h1, h2, by simp [ChSt.visit, h3], by simp [ChSt.visit, h4], fun c' k' hk' => ?_⟩
  have hs : ShapeOk cs st := ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨e1, e2, e3⟩ := h5 c' k' hk'
  refine ⟨?_, ?_, ?_⟩
  · by_cases hcc : c' = c
    · subst hcc; rw [visit_vis_eq hs hc, List.length_set]; exact e1
    · rw [visit_vis_ne hcc]; exact e1
  · by_cases hcc : c' = c
    · subst hcc
      unfold ChSt.visit; simp only
      rw [getD_set_eq' (by rw [h4]; exact hc), List.length_set]; exact e2
    · unfold ChSt.visit; simp only
      rw [getD_set_ne' hcc]; exact e2
  · rw [visit_fuAt hs hc hk]
    split
    · exact hfl
    · exact e3

theorem visit_fuOk (hfu : FuOk h cs st) (hshape : ShapeOk cs st) (hc : c < cs.length)
    (hk : k < (chain cs c).length)
    (hfl : ∀ d, d < cs.length → d ≠ c → sint.Z (fl.getD d 0) = FUe h cs c d k) :
    FuOk h cs (st.visit c k fl) := by
  intro c' k' hv d hd hdc
  rw [visit_fuAt hshape hc hk]
  rw [visit_visAt hshape hc hk] at hv
  split
  · rename_i hck
    obtain ⟨rfl, rfl⟩ := hck
    exact hfl d hd hdc
  · rename_i hck
    have : st.visAt c' k' = true := by
      cases hst : st.visAt c' k'
      · rw [hst] at hv; simp only [Bool.false_or, decide_eq_true_eq] at hv; exact absurd hv hck
      · rfl
    exact hfu c' k' this d hd hdc

end visit

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- A client's struct reads the state only at its own entries. -/
theorem clientOwn_congr {h : List (Op OpV)} {cs : List (List Nat)} {st st' : ChSt} {c : Nat}
    {cv : client} (hh : st'.head c = st.head c) (hn : st'.nDeps.getD c 0 = st.nDeps.getD c 0)
    (hv : st'.vis.getD c [] = st.vis.getD c []) (hf : ∀ k, st'.fuAt c k = st.fuAt c k) :
    clientOwn (GF := GF) h cs st' c cv = clientOwn h cs st c cv := by
  unfold clientOwn
  simp only [hh, hn, hv, hf]

/-- The `firstUnk` points-tos of a client's operations, but at index `i`, depend only on the
slices, and on the contents off `i`. -/
theorem fus_rebuild {cos cos' : List clientOperation} {i : Nat} {F F' : Nat → List w64}
    (hmap : cos'.map (·.firstUnk') = cos.map (·.firstUnk')) (hF : ∀ k, k ≠ i → F' k = F k) :
    ([∗list] k ↦ co ∈ cos, if k = i then emp else co.firstUnk' ↦* F k : IProp GF) ⊢
      [∗list] k ↦ co ∈ cos', if k = i then emp else co.firstUnk' ↦* F' k := by
  have e1 := BigSepL.bigSepL_map (PROP := IProp GF) (·.firstUnk') (l := cos)
    (Φ := fun k s => if k = i then emp else s ↦* F k)
  have e2 := BigSepL.bigSepL_map (PROP := IProp GF) (·.firstUnk') (l := cos')
    (Φ := fun k s => if k = i then emp else s ↦* F' k)
  rw [← e1, ← e2, hmap]
  refine BigSepL.bigSepL_mono fun {k _} _ => ?_
  by_cases hk : k = i
  · simp only [hk, ↓reduceIte]; exact .rfl
  · simp only [hk, ↓reduceIte, hF k hk]; exact .rfl

theorem ite_emp_neg {p : Prop} [Decidable p] {P : IProp GF} (hp : ¬ p) :
    (if p then emp else P) ⊣⊢ P := by
  rw [ite_cond_eq_false _ _ (eq_false hp)]
  exact .rfl

/-- A read-only slice as two halves. -/
theorem ownSlice_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (vs : List V) :
    (s ↦* vs : IProp GF) ⊣⊢ s ↦*{DFrac.own (1 : Qp).half} vs ∗ s ↦*{DFrac.own (1 : Qp).half} vs := by
  have := (ownSlice_dfractional (GF := GF) s vs).dfractional (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half)
  rw [← dfrac_own_half_half] at this
  exact this

/-- The chains put back together, client `c` (taken out, with half of the clients slice) with
the new state `st'`, the other clients unchanged. -/
theorem chains_restore (ch : Loc) (chV : chains) (h : List (Op OpV)) (cs : List (List Nat))
    (st st' : ChSt) (cvs : List client) (c : Nat) (cvc : client) (hcvc : cvs[c]? = some cvc)
    (hlen : cvs.length = cs.length ∧ sint.Z chV.numOps' = h.length)
    (hother : ∀ k, k ≠ c → ∀ cv, clientOwn (GF := GF) h cs st' k cv = clientOwn h cs st k cv) :
    (ch ↦ chV : IProp GF) ∗ chV.frontier' ↦* st'.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64)) ∗
      ownSliceCap w64 chV.frontier' (DFrac.own 1) ∗
      chV.clients' ↦*{DFrac.own (1 : Qp).half} cvs ∗
      (∀ v', sliceIndexRef client (c : Int) chV.clients' ↦{DFrac.own (1 : Qp).half} v' -∗
        chV.clients' ↦*{DFrac.own (1 : Qp).half} cvs.set c v') ∗
      sliceIndexRef client (c : Int) chV.clients' ↦{DFrac.own (1 : Qp).half} cvc ∗
      ([∗list] k ↦ y ∈ cvs, if k = c then emp else clientOwn h cs st k y) ∗
      clientOwn h cs st' c cvc ⊢ chainsOwn ch h cs st' := by
  iintro ⟨Hch, Hfr, Hcap, HclB, HclA, Hcvc, Hrest, Hc⟩
  ihave HclA := HclA $$ %cvc Hcvc
  rw [list_set_lookup_self _ _ _ hcvc]
  ihave Hcl := (ownSlice_halves chV.clients' cvs).2 $$ [HclA HclB]
  · iframe
  unfold chainsOwn chainsRepr
  iexists chV
  iframe Hch
  iexists cvs
  iframe Hcl Hfr Hcap
  isplitr
  · ipureintro; exact hlen
  iapply (BigSepL.bigSepL_delete_cond (PROP := IProp GF)
    (Φ := fun k cv => clientOwn h cs st' k cv) hcvc).2
  iframe Hc
  iapply BigSepL.bigSepL_mono ?_ $$ Hrest
  intro k y _
  by_cases hk : k = c
  · simp only [hk, ↓reduceIte]; exact .rfl
  · simp only [hk, ↓reduceIte, hother k hk y]; exact .rfl

end heap

end github_com.anishathalye.porcupine

namespace EtcdGrove
namespace porcupine

open github_com.anishathalye.porcupine

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- `Check` on two operations held in slices of `clientOperation`s. -/
theorem wp_check_elems (wp_Check : Consistency.Check.spec (GF := GF) (hG := hG)) (cp : Loc)
    (cons : Consistency) (sla slb : GoSlice) (cosa cosb : List clientOperation) (i j : Int)
    (a b : clientOperation) (dqa dqb : DFrac) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (ha : cosa[i.toNat]? = some a) (hb : cosb[j.toNat]? = some b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ cp ↦ cons ∗
        isLinearizability cons ∗ sla ↦*{dqa} cosa ∗ slb ↦*{dqb} cosb }}
      (App (App (Val (cp @!! go.GoType.PointerType Consistency.ty @!! go!"Check"))
        (Val #(sliceIndexRef clientOperation i sla))) (Val #(sliceIndexRef clientOperation j slb)))
    {{ RET (PairV #(linOrder a.Op' b.Op') #interface.nil);
        cp ↦ cons ∗ sla ↦*{dqa} cosa ∗ slb ↦*{dqb} cosb }} := by
  iintro %Φ ⟨#Hpkg, Hcp, #Hlin, Ha, Hb⟩ HΦ
  icases ownSlice_elem_acc i a sla dqa cosa hi ha $$ Ha with ⟨Hae, Ha⟩
  icases ownSlice_elem_acc j b slb dqb cosb hj hb $$ Hb with ⟨Hbe, Hb⟩
  wp_apply (wp_Check cp cons (DFrac.own 1) _ _ a b dqa dqb) $$ [$Hcp $Hae $Hbe] as ⟨Hcp, Hae, Hbe⟩
  · iframe #
  ihave Ha := Ha $$ %a Hae
  ihave Hb := Hb $$ %b Hbe
  rw [list_set_lookup_self _ _ _ ha, list_set_lookup_self _ _ _ hb]
  iapply HΦ
  iframe

end heap

end porcupine
end EtcdGrove

end Perennial
