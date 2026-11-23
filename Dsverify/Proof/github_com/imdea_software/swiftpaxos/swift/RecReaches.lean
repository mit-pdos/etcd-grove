/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecReaches.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## `recReaches`' search, pure -/

/-- The reachability relation of the kept dependencies (model ids). -/
abbrev swift.reachRel (k : sp.Kept) : sp.CmdId → sp.CmdId → Prop := fun y d => d ∈ sp.kdeps k y

/-- `recReaches`' search state: every node of `pend` (the stack, and the node being expanded)
is `src` or reachable from it; every seen node is reachable; `src` and every seen node is
pending or has its dependencies seen, none of them `dst`. -/
def swift.dfsOk (k : sp.Kept) (src dst : swift.CommandId) (pend : List swift.CommandId)
    (sm : GMap swift.CommandId Bool) : Prop :=
  (∀ y ∈ pend, y = src ∨ Relation.TransGen (swift.reachRel k) (toCmdId src) (toCmdId y)) ∧
  (∀ y v, sm !! y = some v → v = true ∧
    Relation.TransGen (swift.reachRel k) (toCmdId src) (toCmdId y)) ∧
  (∀ z, (z = src ∨ (sm !! z).isSome) → z ∈ pend ∨
    ∀ d ∈ sp.kdeps k (toCmdId z), d ≠ toCmdId dst ∧ (sm !! ofCmdId d).isSome)

theorem swift.dfs_init (k : sp.Kept) (src dst : swift.CommandId) :
    swift.dfsOk k src dst [src] ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  intro z hz
  left
  rcases hz with rfl | hz
  · simp
  · simp at hz

theorem swift.dfs_reach_of {k : sp.Kept} {src dst : swift.CommandId} {pend : List swift.CommandId}
    {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst pend sm) {x : swift.CommandId}
    (hx : x ∈ pend) {d : sp.CmdId} (hd : d ∈ sp.kdeps k (toCmdId x)) :
    Relation.TransGen (swift.reachRel k) (toCmdId src) d := by
  rcases H.1 x hx with rfl | h
  · exact Relation.TransGen.single hd
  · exact Relation.TransGen.tail h hd

/-- A dependency `y` of the expanded `x`, not yet seen: seen and pushed. -/
theorem swift.dfs_push {k : sp.Kept} {src dst : swift.CommandId} {s : List swift.CommandId}
    {x : swift.CommandId} {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst (s ++ [x]) sm)
    {y : swift.CommandId} (hy : toCmdId y ∈ sp.kdeps k (toCmdId x)) :
    swift.dfsOk k src dst ((s ++ [y]) ++ [x]) (<[y := true]> sm) := by
  have hr := swift.dfs_reach_of H (by simp) hy
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | rfl) | rfl
    · exact h1 z (by simp [hz])
    · exact Or.inr hr
    · exact h1 z (by simp)
  · intro z v hz
    by_cases e : z = y
    · subst e; rw [GMap.lookup_insert_eq] at hz; cases hz; exact ⟨rfl, hr⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hz; exact h2 z v hz
  · intro z hz
    by_cases e : z = y
    · subst e; left; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hz
      rcases h3 z hz with hz | hz
      · left; simp only [List.mem_append, List.mem_singleton] at hz ⊢
        rcases hz with hz | hz
        · exact Or.inl (Or.inl hz)
        · exact Or.inr hz
      · right; intro d hd
        obtain ⟨hd1, hd2⟩ := hz d hd
        refine ⟨hd1, ?_⟩
        by_cases e' : ofCmdId d = y
        · rw [e', GMap.lookup_insert_eq]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e')]; exact hd2

/-- The expanded `x` done (its dependencies seen, none `dst`). -/
theorem swift.dfs_done {k : sp.Kept} {src dst : swift.CommandId} {s : List swift.CommandId}
    {x : swift.CommandId} {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst (s ++ [x]) sm)
    (hx : ∀ d ∈ sp.kdeps k (toCmdId x), d ≠ toCmdId dst ∧ (sm !! ofCmdId d).isSome) :
    swift.dfsOk k src dst s sm := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨fun y hy => h1 y (by simp [hy]), h2, ?_⟩
  intro z hz
  rcases h3 z hz with hz' | hz'
  · simp only [List.mem_append, List.mem_singleton] at hz'
    rcases hz' with hz' | rfl
    · exact Or.inl hz'
    · exact Or.inr hx
  · exact Or.inr hz'

/-- `dst` found among the dependencies of the expanded `x`. -/
theorem swift.dfs_found {k : sp.Kept} {src dst : swift.CommandId} {s : List swift.CommandId}
    {x : swift.CommandId} {sm : GMap swift.CommandId Bool} (H : swift.dfsOk k src dst (s ++ [x]) sm)
    (hd : toCmdId dst ∈ sp.kdeps k (toCmdId x)) :
    sp.recReaches k (toCmdId src) (toCmdId dst) = true :=
  (sp.recReaches_iff k _ _).2 (swift.dfs_reach_of H (by simp) hd)

/-- The stack empty: `dst` is not reachable. -/
theorem swift.dfs_exit {k : sp.Kept} {src dst : swift.CommandId} {sm : GMap swift.CommandId Bool}
    (H : swift.dfsOk k src dst [] sm) : sp.recReaches k (toCmdId src) (toCmdId dst) = false := by
  obtain ⟨-, -, h3⟩ := H
  have closed : ∀ z, (z = src ∨ (sm !! z).isSome) →
      ∀ d ∈ sp.kdeps k (toCmdId z), d ≠ toCmdId dst ∧ (sm !! ofCmdId d).isSome := by
    intro z hz
    rcases h3 z hz with hz | hz
    · simp at hz
    · exact hz
  have key : ∀ y, Relation.TransGen (swift.reachRel k) (toCmdId src) y →
      y ≠ toCmdId dst ∧ (sm !! ofCmdId y).isSome := by
    intro y hy
    induction hy with
    | single h => exact closed src (Or.inl rfl) _ h
    | tail _ hbc ih =>
      have := closed (ofCmdId _) (Or.inr ih.2) _ (by simpa using hbc)
      exact this
  cases h : sp.recReaches k (toCmdId src) (toCmdId dst)
  · rfl
  · exact absurd rfl (key _ ((sp.recReaches_iff k _ _).1 h)).1

section rd
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A read of an entry's dependency slice, owned or read-only. -/
theorem swift.depRead (o : Bool) (dsl : GoSlice) (l : List swift.CommandId) :
    (if o then iprop(dsl ↦* l ∗ ownSliceCap swift.CommandId dsl (DFrac.own 1))
      else iprop(dsl ↦*□ l) : IProp netDistGF) ⊢
    ∃ dq, dsl ↦*{dq} l ∗ (dsl ↦*{dq} l -∗ (if o then iprop(dsl ↦* l ∗
      ownSliceCap swift.CommandId dsl (DFrac.own 1)) else iprop(dsl ↦*□ l))) := by
  cases o
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro #H
    iexists DFrac.discard
    isplitr
    · iexact H
    · iintro -; iexact H
  · simp only [↓reduceIte]
    iintro ⟨H, Hc⟩
    iexists DFrac.own 1
    iframe H
    iintro H; iframe

end rd

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

theorem swift.recReaches.wp_proofM : swift.recReaches.specM (hG := hG) := by
  intro m k o mk src dst
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as Hk
  iunfold swift.keptAt at Hk
  icases Hk with ⟨Hm, %Hmk, Hents⟩
  wp_auto
  wp_apply (wp_map_make1 (K := swift.CommandId) (V := Bool)) as %sm0 Hsm
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [src]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %ssl0 ⟨Hs0, Hcap0⟩
  wp_auto
  ihave HI : (∃ (st : List swift.CommandId) (ssl : GoSlice) (sm : GMap swift.CommandId Bool),
      "stack" ∷ stack_ptr ↦ ssl ∗ "Hs" ∷ ssl ↦* st ∗
      "Hcap" ∷ ownSliceCap swift.CommandId ssl (DFrac.own 1) ∗
      "Hsm" ∷ sm0 ↦$ sm ∗ "%Hdfs" ∷ ⌜swift.dfsOk k src dst st sm⌝ : IProp netDistGF)
    $$ [stack Hs0 Hcap0 Hsm]
  · iexists [src], _, ∅
    iframe
    ipureintro; exact swift.dfs_init k src dst
  wp_for HI
  wp_if_destruct
  · -- an iteration: `x` the stack's last
    ihave %Hlen := ownSlice_len $$ Hs
    obtain ⟨st0, x, rfl⟩ : ∃ st0 x, st = st0 ++ [x] := by
      rcases List.eq_nil_or_concat st with h | ⟨st0, x, h⟩
      · subst h; simp at Hlen; word
      · exact ⟨st0, x, by rw [h]; simp⟩
    simp only [List.length_append, List.length_singleton] at Hlen
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index (V := swift.CommandId) ssl (sint.Z (ssl.len - W64 1)) _ _ x
      (by word)) $$ [Hs] as Hs
    · iframe; ipureintro
      rw [show (sint.Z (ssl.len - W64 1)).toNat = st0.length by word]; simp
    ihave %Hwf := ownSlice_wf $$ Hs
    rw [ite_eq_left (by word)]
    icases ownSlice_slice_with_cap (W64 0) (ssl.len - W64 1) ssl _ (by word) $$ [Hs Hcap]
      with ⟨-, Hs, Hcap⟩
    · iframe
    have hsub : subslice (sint.nat (W64 0)) (sint.nat (ssl.len - W64 1)) (st0 ++ [x]) = st0 := by
      rw [show sint.nat (ssl.len - W64 1) = st0.length by word]
      simp only [subslice]; rw [show sint.nat (W64 0) = 0 from rfl]; simp
    rw [hsub]
    wp_auto
    wp_apply (wp_map_lookup2 _ _ m mk x) $$ Hm as Hm
    have hkx := Hmk.2 x
    cases hx : mk !! x with
    | none =>
      -- not kept: no dependency
      rw [hx] at hkx
      have hkd : sp.kdeps k (toCmdId x) = [] := by
        unfold sp.kdeps
        cases h : k.get (toCmdId x) with
        | none => rfl
        | some _ => rw [h] at hkx; cases hkx
      wp_auto
      wp_for_post
      iframe
      iexists st0, _, sm
      iframe
      ipureintro
      exact swift.dfs_done Hdfs (by rw [hkd]; simp)
    | some p =>
      rw [hx] at hkx
      obtain ⟨e, he⟩ : ∃ e, k.get (toCmdId x) = some e := Option.isSome_iff_exists.mp hkx.symm
      icases (BigSepM.bigSepM_lookup_acc (show Iris.Std.PartialMap.get? mk x = some p from hx)).1
        $$ Hents with ⟨⟨%e', %he', Hre⟩, Hents⟩
      rw [he] at he'; cases he'
      iunfold swift.recOwn at Hre
      icases Hre with ⟨%ph, %cls, %vs, %dsl, Hp, #Hvs, Hdsl, %Hph⟩
      simp only [Option.isSome_some, Option.getD_some]
      wp_auto
      icases swift.depRead _ dsl _ $$ Hdsl with ⟨%dq, Hd, Hdback⟩
      ihave %Hdl := ownSlice_len $$ Hd
      have hkd : sp.kdeps k (toCmdId x) = e.dep := by unfold sp.kdeps; rw [he]; rfl
      ihave HJ : (∃ (i : w64) (s : List swift.CommandId) (ssl' : GoSlice)
          (sm' : GMap swift.CommandId Bool) (yv : swift.CommandId),
          "i" ∷ i_ptr ↦ i ∗ "y" ∷ y_ptr ↦ yv ∗
          "stack" ∷ stack_ptr ↦ ssl' ∗ "Hs" ∷ ssl' ↦* s ∗
          "Hcap" ∷ ownSliceCap swift.CommandId ssl' (DFrac.own 1) ∗
          "Hsm" ∷ sm0 ↦$ sm' ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z dsl.len ∧ swift.dfsOk k src dst (s ++ [x]) sm' ∧
            ∀ j d, j < sint.nat i → e.dep[j]? = some d →
              d ≠ toCmdId dst ∧ (sm' !! ofCmdId d).isSome⌝ : IProp netDistGF)
        $$ [i y stack Hs Hcap Hsm]
      · iexists W64 0, st0, _, sm, _
        iframe
        ipureintro
        refine ⟨by word, by word, Hdfs, ?_⟩
        intro j d hj; word
      wp_for HJ
      wp_if_destruct
      · -- the dependency `e.dep[i]`
        simp only [List.length_map] at Hdl
        have hil : sint.nat i < e.dep.length := by have := Hj.1; word
        obtain ⟨d, hd⟩ : ∃ d, e.dep[sint.nat i]? = some d := ⟨_, List.getElem?_eq_getElem hil⟩
        rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dsl.len from ⟨Hj.1, Hif⟩)]
        wp_apply (wp_load_slice_index (V := swift.CommandId) dsl (sint.Z i) _ _ (ofCmdId d)
          Hj.1) $$ [Hd] as Hd
        · iframe; ipureintro
          rw [show (sint.Z i).toNat = sint.nat i by word, List.getElem?_map, hd]; rfl
        wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
        iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (ofCmdId d = dst))⌝))) $$ []
        · wp_if_destruct
          · ipureintro
            congr 2
            cases dst; simp_all [ofCmdId]
          · ipureintro
            congr 2
            cases dst; simp_all [ofCmdId]
        iintro %v %hv
        subst hv
        have hdmem : d ∈ sp.kdeps k (toCmdId x) := by rw [hkd]; exact List.mem_of_getElem? hd
        wp_if_destruct
        · -- found: `dst` is a dependency of `x`
          have hfound := swift.dfs_found Hj.2.2.1 (by simpa using hdmem)
          wp_for_post
          wp_for_post
          rw [hfound]
          iapply HΦ
          iunfold swift.keptAt
          iframe Hm
          isplitr
          · ipureintro; exact Hmk
          iapply Hents
          iexists e
          isplitr
          · ipureintro; exact he
          iunfold swift.recOwn
          iexists ph, cls, vs, dsl
          iframe Hp Hvs
          isplitl [Hd Hdback]
          · iapply Hdback $$ Hd
          ipureintro; exact Hph
        · have hne : d ≠ toCmdId dst := by intro h; apply Hif; rw [h]; rfl
          wp_apply (wp_map_lookup1 _ _ sm0 sm' (ofCmdId d)) $$ Hsm as Hsm
          have hseen : sm' !! ofCmdId d = none ∨ sm' !! ofCmdId d = some true := by
            cases h : sm' !! ofCmdId d with
            | none => exact Or.inl rfl
            | some v => have := (Hj.2.2.1.2.1 _ v h).1; subst this; exact Or.inr rfl
          rcases hseen with hnone | hsome
          · -- not seen: seen, pushed
            rw [hnone]
            simp only [Option.getD_none, show (zero_val Bool) = false from rfl]
            wp_auto
            wp_apply (wp_mapInsert _ sm0 sm' (ofCmdId d) true) $$ Hsm as Hsm
            wp_bind (App (Val (GoInstruction (CompositeLiteral
              (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [ofCmdId d]
            wp_auto
            isplitl []
            · ipureintro; rfl
            iintro %lsl ⟨Hlsl, -⟩
            wp_auto
            wp_apply wp_slice_append $$ [Hs Hcap Hlsl] as %nsl ⟨Hs, Hcap, -⟩
            · iframe
            wp_for_post
            iframe
            iexists i + W64 1, _, _, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, swift.dfs_push Hj.2.2.1 (by simpa using hdmem), ?_⟩
            intro j d' hj hjd
            by_cases hji : j = sint.nat i
            · subst hji; rw [hd] at hjd; cases hjd
              refine ⟨hne, ?_⟩
              rw [GMap.lookup_insert_eq]; rfl
            · obtain ⟨h1, h2⟩ := Hj.2.2.2 j d' (by word) hjd
              refine ⟨h1, ?_⟩
              by_cases e' : ofCmdId d' = ofCmdId d
              · rw [e', GMap.lookup_insert_eq]; rfl
              · rw [GMap.lookup_insert_ne _ _ (Ne.symm e')]; exact h2
          · -- already seen
            rw [hsome]
            simp only [Option.getD_some]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, _, _, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, Hj.2.2.1, ?_⟩
            intro j d' hj hjd
            by_cases hji : j = sint.nat i
            · subst hji; rw [hd] at hjd; cases hjd
              exact ⟨hne, by rw [hsome]; rfl⟩
            · exact Hj.2.2.2 j d' (by word) hjd
      · -- every dependency done
        wp_for_post
        iframe
        isplitl [Hents Hp Hd Hdback]
        · iapply Hents
          iexists e
          isplitr
          · ipureintro; exact he
          iunfold swift.recOwn
          iexists ph, cls, vs, dsl
          iframe Hp Hvs
          isplitl [Hd Hdback]
          · iapply Hdback $$ Hd
          ipureintro; exact Hph
        iexists s, ssl', sm'
        iframe
        ipureintro
        apply swift.dfs_done Hj.2.2.1
        rw [hkd]
        intro d hd
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
        have : j < e.dep.length := by
          rcases Nat.lt_or_ge j e.dep.length with h | h
          · exact h
          · rw [List.getElem?_eq_none_iff.mpr h] at hj; cases hj
        simp only [List.length_map] at Hdl
        exact Hj.2.2.2 j d (by word) hj
  · -- the stack empty: not reachable
    ihave %Hlen := ownSlice_len $$ Hs
    have hst : st = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst hst
    rw [swift.dfs_exit Hdfs]
    iapply HΦ
    iunfold swift.keptAt
    iframe
    ipureintro; exact Hmk

theorem swift.recReaches.wp_proof : swift.recReaches.specI (hG := hG) := by
  intro m k o src dst
  iintro %Φ ⟨#Hpkg, Hk⟩ HΦ
  iunfold swift.keptOwn at Hk
  icases Hk with ⟨%mk, Hk⟩
  wp_apply (swift.recReaches.wp_proofM m k o mk src dst) $$ [Hk] as Hk
  · iframe #; iunfold swift.keptAt; iexact Hk
  iapply HΦ
  iunfold swift.keptOwn
  iexists mk
  iunfold swift.keptAt at Hk
  iexact Hk

end proof
end Perennial.github_com.imdea_software.swiftpaxos
