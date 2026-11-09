/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AdvanceCommitIndex`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AdvanceCommitIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__commitTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsQuorum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem State.AdvanceCommitIndex.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_commitTo : State.commitTo.spec (GF := GF) (hG := hG))
    (wp_GetConfig : State.GetConfig.spec (GF := GF) (hG := hG))
    (wp_IsQuorum : IsQuorum.spec (GF := GF) (hG := hG)) :
    State.AdvanceCommitIndex.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %hcl, %hll⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
  rw [decide_strRel Hf.2.1 strRel_leader]
  by_cases h1 : (st.s (uint.nat i)).state = leader
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    imodintro
    iapply HΦ
    have : st.advanceCommitIndex (uint.nat i) = none := by
      unfold State.advanceCommitIndex; simp [h1]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true h1]
  wp_auto
  wp_apply wp_GetConfig p st i $$ [Hst] as %sl2 #Hsl2
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  obtain ⟨FF, hFF⟩ : ∃ FF : Nat → Nat → Nat, FF = (fun acc n => if isQuorum ((fun (idx : Nat) => (st.getConfig (uint.nat i)).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ idx))) (n + 1)) (st.getConfig (uint.nat i)) then n + 1 else acc) := ⟨_, rfl⟩
  ipersist cfg
  ipersist v
  ipersist s
  ipersist i
  ipersist agree
  irename i => Hip
  irename v => Hvp
  irename s => Hsp
  irename cfg => Hcfgp
  irename agree => Hagp
  ihave IH : iprop(∃ (idx ma : w64),
      "index" ∷ index_ptr ↦ idx ∗ "maxAgree" ∷ maxAgree_ptr ↦ ma ∗
      "%Hn" ∷ ⌜1 ≤ sint.Z idx ∧ sint.Z idx ≤ ((st.s (uint.nat i)).log.length : Int) + 1 ∧
        sint.Z ma = ((List.range (sint.nat idx - 1)).foldl FF 0 : Nat)⌝) $$ [index maxAgree]
  · iexists _, _
    iframe
    ipureintro
    rw [show sint.Z (W64 1) = 1 from rfl, show sint.nat (W64 1) = 1 from rfl]
    refine ⟨Int.le_refl _, by omega, by simp⟩
  wp_for IH
  obtain ⟨hi1, hi2, hma⟩ := Hn
  wp_if_destruct
  · try wp_auto
    rename_i r0p ip0 idxp
    irename : (idxp ↦ idx : IProp GF) => Hidx
    irename : (r0p ↦ (zero_val Loc : Loc) : IProp GF) => Hres0
    iunfold setRO at Hsl2
    icases Hsl2 with ⟨%xs, #Hxs, %Hxm⟩
    ihave %Hxl := ownSlice_len $$ Hxs
    ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List w64) $$ []
    · iapply ownSlice_nil
    ihave Hcap0 : ownSliceCap w64 (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave IH2 : iprop(∃ (n kv : w64) (sl : GoSlice) (ys : List w64),
        "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗ "a" ∷ a_ptr ↦ sl ∗ "Ha" ∷ sl ↦* ys ∗
        "Hcapa" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
        "%Hn2" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl2.len ∧
          ys.map (fun x => uint.nat x) = ((st.getConfig (uint.nat i)).take (sint.nat n)).filter
            (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int)))⌝)
        $$ [i k a Hnil Hcap0]
    · iexists _, _, _, []
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IH2
    obtain ⟨hn0, hn1, hna⟩ := Hn2
    have hcfgl : sint.Z sl2.len = ((st.getConfig (uint.nat i)).length : Int) := by rw [← Hxm, List.length_map, Hxl.1]; word
    by_cases hc : sint.Z n < sint.Z sl2.len
    · have hd : decide (sint.Z n < sint.Z sl2.len) = true := by simpa using hc
      simp only [hd, ↓reduceIte]
      wp_auto
      have Hlt : sint.nat n < xs.length := by rw [Hxl.1]; word
      obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hsx : (st.getConfig (uint.nat i))[sint.nat n]? = some (uint.nat x) := by rw [← Hxm, List.getElem?_map, Hx]; rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl2.len from ⟨hn0, hc⟩))]
      wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hx
      try wp_auto
      wp_apply wp_map_lookup1 $$ [Hmm] as -
      · iexact Hmm
      try wp_auto
      rw [show (zero_val w64 : w64) = W64 0 from rfl]
      have hge : (sint.Z idx ≤ sint.Z ((mm !! x).getD (W64 0))) ↔ (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int))) (uint.nat x) = true := by
        rw [Hmi x]; simp; constructor <;> intro h <;> word
      have htake : ((st.getConfig (uint.nat i)).take (sint.nat (n + W64 1))).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int))) =
          ((st.getConfig (uint.nat i)).take (sint.nat n)).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int))) ++
            (if (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int))) (uint.nat x) then [uint.nat x] else []) := by
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hsx]
        rw [List.filter_append]
        congr 1
        simp only [Option.toList_some, List.filter_cons, List.filter_nil]
      by_cases hk : (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int))) (uint.nat x) = true
      · rw [decide_eq_true (hge.2 hk)]
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl0 ⟨Hsl0, -⟩
        wp_apply wp_slice_append $$ [Ha Hcapa Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [htake, hk]; simp [hna]
      · rw [decide_eq_false (fun e => hk (hge.1 e))]
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [htake, Bool.eq_false_iff.2 hk]; simp [hna]
    have hd : decide (sint.Z n < sint.Z sl2.len) = false := by simpa using hc
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    have hnx : sint.nat n = (st.getConfig (uint.nat i)).length := by rw [← Hxm, List.length_map, Hxl.1]; word
    rw [hnx, List.take_length] at hna
    try wp_auto
    imod ownSlice_persist $$ Ha with #Ha
    have hagl : ((st.getConfig (uint.nat i)).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int)))).length < 2 ^ 62 :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) hcl
    wp_apply wp_IsQuorum sl ((st.getConfig (uint.nat i)).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int)))) sl2 (st.getConfig (uint.nat i)) $$ []
    · isplitl []
      · iunfold setRO; iexists ys; iframe Ha; ipureintro; exact hna
      isplitl []
      · iunfold setRO; iexists xs; iframe Hxs; ipureintro; exact Hxm
      ipureintro; exact hagl
    have hidxn : sint.nat idx - 1 + 1 = sint.nat idx := by
      have : (1 : Int) ≤ sint.Z idx := hi1
      have : sint.nat idx = (sint.Z idx).toNat := rfl
      omega
    have hstep : (List.range (sint.nat (idx + W64 1) - 1)).foldl FF 0 =
        FF ((List.range (sint.nat idx - 1)).foldl FF 0) (sint.nat idx - 1) := by
      rw [show sint.nat (idx + W64 1) - 1 = sint.nat idx - 1 + 1 by word, List.range_succ, List.foldl_append]
      rfl
    have hFq : FF ((List.range (sint.nat idx - 1)).foldl FF 0) (sint.nat idx - 1) =
        if isQuorum ((st.getConfig (uint.nat i)).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int)))) (st.getConfig (uint.nat i)) then sint.nat idx
        else (List.range (sint.nat idx - 1)).foldl FF 0 := by
      rw [hFF]; simp only [hidxn]
    cases hq : isQuorum ((st.getConfig (uint.nat i)).filter (fun k => decide ((st.s (uint.nat i)).matchIndex k ≥ ((sint.nat idx : Nat) : Int)))) (st.getConfig (uint.nat i))
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hstep, hFq, hq]; exact hma
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hstep, hFq, hq]; simp only [↓reduceIte]; word
  · have hidx : sint.Z idx = (((st.s (uint.nat i)).log.length : Nat) : Int) + 1 := by omega
    have hidxn : sint.nat idx - 1 = (st.s (uint.nat i)).log.length := by
      have : sint.nat idx = (sint.Z idx).toNat := rfl
      omega
    rw [hidxn] at hma
    obtain ⟨MA, hMA⟩ : ∃ MA, MA = (List.range (st.s (uint.nat i)).log.length).foldl FF 0 := ⟨_, rfl⟩
    rw [← hMA] at hma
    have hFFle : ∀ (l : Nat), (List.range l).foldl FF 0 ≤ l := by
      intro l
      induction l with
      | zero => simp
      | succ l ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [hFF]; simp only
        rw [← hFF]
        split
        · omega
        · omega
    have hmaL : MA ≤ (st.s (uint.nat i)).log.length := by rw [hMA]; exact hFFle _
    wp_join iprop(∃ nc : w64, newCommitIndex_ptr ↦ nc ∗ maxAgree_ptr ↦ ma ∗ ⌜sint.Z nc = (if Bool.and (decide (MA > 0)) ((((st.s (uint.nat i)).log[MA - 1]?).map Entry.term) == some (st.s (uint.nat i)).currentTerm) then (MA : Int) else (st.s (uint.nat i)).commitIndex)⌝)
      at (if: _ then _ else _) with [newCommitIndex maxAgree] as ⟨%nc, newCommitIndex, maxAgree, %Hnc⟩
    · by_cases hpos : 0 < MA
      rotate_left
      · rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z ma by rw [hma]; show ¬ (0 : Int) < _; omega)]
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        rw [Hf.2.2.2.2.1]; simp [show MA = 0 by omega]
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z ma by rw [hma]; show (0 : Int) < _; omega)]
      wp_auto
      have hk2 : sint.Z (ma - W64 1) = (MA : Int) - 1 := by rw [← hma]; word
      have hk0 : 0 ≤ sint.Z (ma - W64 1) ∧ sint.Z (ma - W64 1) < sint.Z gs.Log'.len := by
        rw [hk2, hlen]; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk0)]
      have hidx2 : (sint.Z (ma - W64 1)).toNat = MA - 1 := by rw [hk2]; omega
      have hkn : MA - 1 < es.length := by rw [Hell]; omega
      obtain ⟨x, Hx⟩ : ∃ x, es[MA - 1]? = some x := ⟨_, List.getElem?_eq_getElem hkn⟩
      obtain ⟨y, Hy⟩ : ∃ y, (st.s (uint.nat i)).log[MA - 1]? = some y :=
        ⟨_, List.getElem?_eq_getElem (Hell ▸ hkn)⟩
      ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hx Hy $$ Hel
      iunfold entryRO at Hxy
      icases Hxy with ⟨%Hxy1, -⟩
      icases ownSlice_elem_acc _ x _ _ es hk0.1 (by rw [hidx2]; exact Hx) $$ Hes with ⟨#Hxe, -⟩
      icases typedPointsto_split _ _ _ $$ Hxe with Hxef
      simp only [TypedPointsto.typedPointstoDef]
      icases Hxef with ⟨#E1, #E2, #E3, -⟩
      wp_auto
      have he := sint_eq_iff x.Term' gs.CurrentTerm' _ _ Hxy1.1 Hf.1
      by_cases ht : y.term = (st.s (uint.nat i)).currentTerm
      · rw [decide_eq_true (he.2 ht)]
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        rw [hma]; simp [hpos, Hy, ht]
      · rw [decide_eq_false (fun e => ht (he.1 e))]
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        rw [Hf.2.2.2.2.1]; simp [hpos, Hy, ht]
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    wp_apply wp_commitTo t st [] i nc $$ [Ht] as Ht
    · iframe Ht; ipureintro; exact Hi
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.advanceCommitIndex (uint.nat i) = some (st.commitTo (uint.nat i) (if Bool.and (decide (MA > 0)) ((((st.s (uint.nat i)).log[MA - 1]?).map Entry.term) == some (st.s (uint.nat i)).currentTerm) then (MA : Int) else (st.s (uint.nat i)).commitIndex)) := by
      unfold State.advanceCommitIndex
      simp only [h1, hMA, hFF]
      simp
    rw [this, ← Hnc]
    iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
