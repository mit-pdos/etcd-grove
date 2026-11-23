/-
`(*Exec).findSCC(root)` and `(*Exec).executeCommand(replica, instance)`, from
`strongconnect`'s spec.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecLemmas

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof tarjan

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

theorem wp_findSCC (γ : EpNames) (i : Nat) (r e rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (hSC : StrongconnectSpec (GF := GF) γ i r e rr L p Rext)
    (F : Nat → List Loc) (σ : RState) (v : InstId) (wv : InstRec) (s : GoSlice) (xs : List Loc)
    (hwf : ExecWf σ) (hib : instBounds σ.inst) (hi : i < nR) (hv : σ.inst v = some wv)
    (hc : wv.status = stCOMMITTED) :
    {{ exCtx (GF := GF) γ i r e rr L p Rext ∗ repInstsX γ i r F σ.inst (fun _ => none) ∗
        repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗ repStore r σ.store ∗
        structFieldRef epaxos.Exec go!"stack" e ↦ s ∗ s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) ∗
        ⌜0 < sint.Z s.cap⌝ ∗ repFrag γ i σ ∗ pendFrag γ i none ∗ curFrag γ i [] 0 }}
      (App (Val (e @!! go.GoType.PointerType epaxos.Exec.ty @!! go!"findSCC")) (Val #(ptrOf F v)))
    {{ (b : Bool), RET #b; ∃ σ' : RState,
        repInsts γ i r σ'.inst ∗ repRowArr r go!"ExecedUpTo" σ'.execedUpTo ∗ repStore r σ'.store ∗
        (∃ (s' : GoSlice) (xs' : List Loc), structFieldRef epaxos.Exec go!"stack" e ↦ s' ∗
          s' ↦* xs' ∗ ownSliceCap Loc s' (DFrac.own 1) ∗ ⌜0 < sint.Z s'.cap⌝) ∗
        repFrag γ i σ' ∗ pendFrag γ i none ∗ curFrag γ i [] 0 ∗
        ⌜ExRel σ σ' ∧ ExecWf σ' ∧ instBounds σ'.inst ∧ (b = true → σ'.executed v)⌝ }} := by
  wp_start as ⟨#Hctx, Hins, Heut, Hstore, Hst, Hs, Hcap, %Hcap0, Hfrag, Hpend, Hcur⟩
  wp_auto
  simp only [show (0 : Int) ≤ sint.Z (W64 0) from by decide, Int.le_refl,
    show sint.Z (W64 0) ≤ sint.Z s.cap from by have := Hcap0; simp at this ⊢; omega, _root_.and_self, ↓reduceIte]
  wp_auto
  ihave %Hxl := ownSlice_len _ _ _ $$ Hs
  ihave ⟨Hs, Hcap⟩ := slice_trunc s xs (W64 0) ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩ $$ [Hs Hcap]
  · iframe
  ihave Hheap : exHeap γ i r e F σ St.init index_ptr $$ [Hins Heut Hstore Hst Hs Hcap Hfrag Hpend Hcur index]
  · unfold exHeap stackOwn St.init
    iframe Hins Heut Hstore Hfrag Hpend Hcur
    isplitl [Hst Hs Hcap]
    · iexists slice.slice s Loc (W64 0) (W64 0)
      iframe Hst Hcap
      isplitl [Hs]
      · simp only [List.map_nil]
        rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero]; iexact Hs
      · ipureintro; simp only [slice.slice]; rw [show sint.Z (s.cap - W64 0) = sint.Z s.cap by word]; exact Hcap0
    · iexact index
  wp_apply (hSC F σ St.init v index_ptr wv ⟨hwf, hib, hi, TInv_init _, VisCount_init⟩
    (by simp [St.init, St.vis]) hv hc (fun _ => rfl) (by simp [St.init])) $$ [$Hctx $Hheap]
    as %b ⟨%σ', %t', Hheap, %Hpost⟩
  obtain ⟨hR, hwf', hib', hcnt, hext, -, hb⟩ := Hpost
  -- the stack after the search: its instances exist, and every visited non-executed one is on it
  have hS : (∀ x, t'.vis x → ¬ σ'.executed x → x ∈ t'.S) ∧ ∀ x ∈ t'.S, ∃ w, σ'.inst x = some w := by
    cases b
    · exact hb
    · exact ⟨hb.1.visS, fun x hx => by
        obtain ⟨-, -, -, -, w, hw, -⟩ := hb.1.onS x hx; exact ⟨w, hw⟩⟩
  unfold exHeap stackOwn
  iNamed Hheap
  icases Hheap with ⟨Hins, Heut, Hstore, ⟨%s', Hst, Hs, Hcap, %Hcap'⟩, index, Hfrag, Hpend, Hcur⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave HI : (∃ k : w64, "Hj" ∷ j_ptr ↦ k ∗
      "Hins" ∷ repInstsX γ i r F σ'.inst (fun x => if x ∈ t'.S.take (sint.nat k) then none else t'.ix x) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ t'.S.length⌝ : IProp GF) $$ [j Hins]
  · iexists W64 0; iframe j
    rw [show sint.nat (W64 0) = 0 by rfl]
    simp only [List.take_zero, List.not_mem_nil, if_false]
    iframe Hins
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · -- reset `stack[k].Index`
    have hkl : sint.nat k < t'.S.length := by
      have := Hsl.1; simp only [List.length_map] at this; word
    obtain ⟨x, hx⟩ : ∃ x, t'.S[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hkl⟩
    have hxS : x ∈ t'.S := List.mem_of_getElem? hx
    obtain ⟨w, hw⟩ := hS.2 x hxS
    obtain ⟨hxq, hxi⟩ := hwf'.ids x w hw
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s'.len := ⟨Hk.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s' (sint.Z k) _ _ (ptrOf F x) hb.1 $$ [$Hs] as Hs
    · ipureintro; rw [List.getElem?_map, show (sint.Z k).toNat = sint.nat k from rfl, hx]; rfl
    icases repInstsX_acc γ i r F σ'.inst _ x hxq (by omega) $$ Hins with
      ⟨%iss, %rows, %row, #Hiss, #Hrows, %Hrow, Hrow, %Hp, Hx, Hclose⟩
    rw [hw]
    unfold slotT ownInstT ownInstG
    icases Hx with ⟨%y, Hy, %Hyf, Hyrest⟩
    wp_auto
    ihave Hins := Hclose $$ %(some w) %none Hrow [Hy Hyrest]
    · dsimp only [slotT, ownInstT, ownInstG]
      iexists _
      iframe Hy Hyrest
      ipureintro
      exact ⟨Hyf.1, Hyf.2.1, Hyf.2.2.1, Hyf.2.2.2.1, fun _ => rfl⟩
    wp_for_post
    iframe
    iexists k + W64 1
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := Hsl.1; have := Hsl.2; simp only [List.length_map] at *; word
    rw [hk1, upd_self _ _ _ hw]
    iframe Hj
    isplitl [Hins]
    · have e : upd (fun z => if z ∈ t'.S.take (sint.nat k) then none else t'.ix z) x none =
          (fun z => if z ∈ t'.S.take (sint.nat k + 1) then none else t'.ix z) := by
        funext z
        rw [List.take_add_one, hx]
        simp only [upd, Option.toList_some, List.mem_append, List.mem_singleton]
        by_cases hz : z = x
        · simp [hz]
        · simp [hz]
      rw [e]; iexact Hins
    ipureintro; constructor
    · have := Hk.1; word
    · omega
  · -- every visited instance is executed
    have hkS : sint.nat k = t'.S.length := by
      have := Hsl.1; have := Hk.2; simp only [List.length_map] at *; word
    rw [hkS, List.take_length]
    have hvis : ∀ x, (if x ∈ t'.S then none else t'.ix x) ≠ none →
        ∃ w, σ'.inst x = some w ∧ w.status = stEXECUTED := by
      intro x hx
      by_cases hxS : x ∈ t'.S
      · simp [hxS] at hx
      · simp only [hxS, ite_false] at hx
        have hv : t'.vis x := by unfold St.vis; rcases h : t'.ix x <;> simp_all
        by_cases he : σ'.executed x
        · exact he
        · exact absurd (hS.1 x hv he) hxS
    ihave Hins := repInstsX_toRep (GF := GF) γ i r F σ'.inst _ hvis $$ Hins
    iapply HΦ
    iexists σ'
    iframe Hins Heut Hstore Hfrag Hpend Hcur
    isplitl [Hst Hs Hcap]
    · iexists s', _
      iframe Hst Hs Hcap
      ipureintro; exact Hcap'
    ipureintro
    refine ⟨hR, hwf', hib', fun hbt => ?_⟩
    subst hbt
    obtain ⟨hT, lv, hlv, hcase⟩ := hb
    rcases hcase with ⟨hex, -⟩ | ⟨hvS, hlt, hA, -⟩
    · exact hex
    · exfalso
      -- the root left on the stack: its lowlink witness would lie below `*index`'s start
      obtain ⟨-, u, hu, hnu, -⟩ := hT.lowW v hvS
      have h0 := (hT.onS u hu).2.1
      have e1 : t'.low v = lv := by simp [St.low, hlv]
      have e2 : lv < 1 := by simpa [St.init] using hlt
      omega

theorem wp_executeCommand (γ : EpNames) (i : Nat) (r e rr : Loc) (L : List GoString)
    (p : FwPtrs) (Rext : IProp GF) (hSC : StrongconnectSpec (GF := GF) γ i r e rr L p Rext)
    (σ : RState) (q n : w32) (s : GoSlice) (xs : List Loc)
    (hwf : ExecWf σ) (hib : instBounds σ.inst) (hi : i < nR)
    (hq : 0 ≤ zz q ∧ zz q < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE) :
    {{ exCtx (GF := GF) γ i r e rr L p Rext ∗ repInsts γ i r σ.inst ∗
        repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗ repStore r σ.store ∗
        structFieldRef epaxos.Exec go!"stack" e ↦ s ∗ s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) ∗
        ⌜0 < sint.Z s.cap⌝ ∗ repFrag γ i σ ∗ pendFrag γ i none ∗ curFrag γ i [] 0 }}
      (App (App (Val (e @!! go.GoType.PointerType epaxos.Exec.ty @!! go!"executeCommand"))
        (Val #q)) (Val #n))
    {{ (b : Bool), RET #b; ∃ σ' : RState,
        repInsts γ i r σ'.inst ∗ repRowArr r go!"ExecedUpTo" σ'.execedUpTo ∗ repStore r σ'.store ∗
        (∃ (s' : GoSlice) (xs' : List Loc), structFieldRef epaxos.Exec go!"stack" e ↦ s' ∗
          s' ↦* xs' ∗ ownSliceCap Loc s' (DFrac.own 1) ∗ ⌜0 < sint.Z s'.cap⌝) ∗
        repFrag γ i σ' ∗ pendFrag γ i none ∗ curFrag γ i [] 0 ∗
        ⌜ExRel σ σ' ∧ ExecWf σ' ∧ instBounds σ'.inst ∧
          (b = true → σ'.executed ⟨toN q, toN n⟩)⌝ }} := by
  wp_start as ⟨#Hctx, Hins, Heut, Hstore, Hst, Hs, Hcap, %Hcap0, Hfrag, Hpend, Hcur⟩
  ihave ⟨%F, Hins⟩ := repInsts_toX γ i r σ.inst $$ Hins
  have hxq : (⟨toN q, toN n⟩ : InstId).q < nR := by
    show toN q < nR; have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hxi : (⟨toN q, toN n⟩ : InstId).i < MAX_INSTANCE := by show toN n < MAX_INSTANCE; omega
  unfold exCtx
  icases Hctx with ⟨#Hpk, #Hpkr, #Hpks, #Hpkso, #Hrr, #Hro, #Hfw, #Htc, #Hex, #Her, #Hinv⟩
  icases repInstsX_acc γ i r F σ.inst _ _ hxq hxi $$ Hins with
    ⟨%iss, %rows, %row, #Hiss, #Hrows, %Hrow, Hrow, %Hp, Hx, Hclose⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hrow
  wp_auto
  have e1 : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
  have e2 : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
  have hq' : (sint.Z q).toNat = toN q := rfl
  have hn' : (sint.Z n).toNat = toN n := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z iss.len := by
    have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  have h2 : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row.len := by
    have := hn.1; have := hn.2; have hl := (List.getElem?_eq_some_iff.mp Hp).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hq']; exact Hrow
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ _ _ _ h2.1 $$ [$Hrow] as Hrow
  · ipureintro; rw [e2, hn']; exact Hp
  rcases hx : σ.inst ⟨toN q, toN n⟩ with _ | w
  case none =>
    unfold slotT; icases Hx with %Hnull
    rw [Hnull]
    simp only [decide_true]
    wp_auto
    ihave Hins := Hclose $$ %none %none Hrow []
    · ipureintro; trivial
    rw [← hx, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
    ihave Hins := repInstsX_toRep (GF := GF) γ i r F σ.inst _ (fun _ h => absurd rfl h) $$ Hins
    iapply HΦ
    iexists σ
    iframe Hins Heut Hstore Hfrag Hpend Hcur
    isplitl [Hst Hs Hcap]
    · iexists s, xs; iframe Hst Hs Hcap; ipureintro; exact Hcap0
    ipureintro; exact ⟨ExRel.refl σ, hwf, hib, fun h => by cases h⟩
  case some =>
    unfold slotT ownInstT ownInstG
    icases Hx with ⟨%y, Hy, %Hyf, Hyrest⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
    simp only [Hnn, decide_false]
    wp_auto
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hq']; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row _ _ _ _ h2.1 $$ [$Hrow] as Hrow
    · ipureintro; rw [e2, hn']; exact Hp
    wp_if_destruct
    · -- executed already
      ihave Hins := Hclose $$ %(some w) %none Hrow [Hy Hyrest]
      · dsimp only; iexists y; iframe Hy Hyrest; ipureintro; exact Hyf
      rw [← hx, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
      ihave Hins := repInstsX_toRep (GF := GF) γ i r F σ.inst _ (fun _ h => absurd rfl h) $$ Hins
      iapply HΦ
      iexists σ
      iframe Hins Heut Hstore Hfrag Hpend Hcur
      isplitl [Hst Hs Hcap]
      · iexists s, xs; iframe Hst Hs Hcap; ipureintro; exact Hcap0
      ipureintro
      exact ⟨ExRel.refl σ, hwf, hib, fun _ => ⟨w, hx, by rw [← Hyf.2.2.1]; exact Hif⟩⟩
    wp_if_destruct
    · -- committed: the search
      ihave Hins := Hclose $$ %(some w) %none Hrow [Hy Hyrest]
      · dsimp only; iexists y; iframe Hy Hyrest; ipureintro; exact Hyf
      rw [← hx, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
      have hcw : w.status = stCOMMITTED := by rw [← Hyf.2.2.1]; exact Hif
      ihave #Hctx : exCtx γ i r e rr L p Rext $$ []
      · unfold exCtx; iframe #
      wp_apply (wp_findSCC γ i r e rr L p Rext hSC F σ ⟨toN q, toN n⟩ w s xs hwf hib hi hx hcw)
        $$ [$Hctx $Hins $Heut $Hstore $Hst $Hs $Hcap $Hfrag $Hpend $Hcur] as %b Hpost
      · ipureintro; exact Hcap0
      icases Hpost with ⟨%σ', Hins, Heut, Hstore, Hstk, Hfrag, Hpend, Hcur, %Hpost⟩
      cases b
      · wp_auto
        iapply HΦ
        iexists σ'; iframe; ipureintro
        exact ⟨Hpost.1, Hpost.2.1, Hpost.2.2.1, fun h => by cases h⟩
      · wp_auto
        iapply HΦ
        iexists σ'; iframe; ipureintro
        exact ⟨Hpost.1, Hpost.2.1, Hpost.2.2.1, fun _ => Hpost.2.2.2 rfl⟩
    · -- not committed
      ihave Hins := Hclose $$ %(some w) %none Hrow [Hy Hyrest]
      · dsimp only; iexists y; iframe Hy Hyrest; ipureintro; exact Hyf
      rw [← hx, upd_self _ _ _ rfl, upd_self _ _ _ rfl]
      ihave Hins := repInstsX_toRep (GF := GF) γ i r F σ.inst _ (fun _ h => absurd rfl h) $$ Hins
      iapply HΦ
      iexists σ
      iframe Hins Heut Hstore Hfrag Hpend Hcur
      isplitl [Hst Hs Hcap]
      · iexists s, xs; iframe Hst Hs Hcap; ipureintro; exact Hcap0
      ipureintro
      exact ⟨ExRel.refl σ, hwf, hib, fun h => by cases h⟩

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
