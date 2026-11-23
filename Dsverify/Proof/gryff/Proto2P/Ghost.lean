/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Ghost.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): Iris helpers for `gryffInv2`: the trace halves, the predictions, the
event tokens, and firing the linearized operations' atomic updates over the registrations
(`fire_all2`, stage 1's `fire_all` over `OpInfo`).
-/
module

public import Dsverify.Proof.gryff.Proto2P.StepMain
public import Dsverify.Proof.gryff.Proto.Fire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness
open model kahn pure p2

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-! ## Mono-list halves -/

theorem monoList_halves {A : Type} [Pos.Countable A] (γt : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γt 1 l ⊣⊢
      monoListAuthOwn γt (1 : Qp).half l ∗ monoListAuthOwn γt (1 : Qp).half l := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (monoListAuthOwn_fractional γt l).fractional _ _

/-- Both halves of a mono-list agree, and move together. -/
theorem monoList_halves_update {A : Type} [Pos.Countable A] (γt : GName) (l l' u : List A) :
    monoListAuthOwn (GF := GF) γt (1 : Qp).half l ∗ monoListAuthOwn γt (1 : Qp).half l' ⊢ |==>
      (⌜l = l'⌝ ∗ monoListAuthOwn γt (1 : Qp).half (l ++ u) ∗
        monoListAuthOwn γt (1 : Qp).half (l ++ u) ∗ monoListLbOwn γt (l ++ u)) := by
  iintro ⟨H1, H2⟩
  ihave %h := monoListAuthOwn_agree γt _ _ l l' $$ H1 H2
  obtain ⟨-, rfl⟩ := h
  ihave H := (monoList_halves γt l).2 $$ [H1 H2]
  · iframe H1 H2
  imod monoListAuthOwn_update_app (GF := GF) u $$ H with ⟨H, #Hlb⟩
  icases (monoList_halves γt (l ++ u)).1 $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2 Hlb
  ipureintro; rfl

/-- The invariant's halves of the three traces. -/
def traces3 (γ : ProtoNames) (T : Fin 3 → List Ev) : IProp GF :=
  iprop(monoListAuthOwn (γ.s2.trace 0) (1 : Qp).half (T 0) ∗
    monoListAuthOwn (γ.s2.trace 1) (1 : Qp).half (T 1) ∗
    monoListAuthOwn (γ.s2.trace 2) (1 : Qp).half (T 2))

theorem fin3_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k; decide

theorem traces3_update (γ : ProtoNames) (T : Fin 3 → List Ev) (k : Fin 3) (t : List Ev) (e : Ev) :
    traces3 (GF := GF) γ T ∗ traceHalf γ k t ⊢ |==>
      (⌜T k = t⌝ ∗ traces3 γ (traceSnoc T k e) ∗ traceHalf γ k (t ++ [e]) ∗
        traceLb γ k (t ++ [e])) := by
  unfold traces3 traceHalf traceLb
  iintro ⟨⟨H0, H1, H2⟩, Ht⟩
  rcases fin3_cases k with rfl | rfl | rfl
  · imod monoList_halves_update (GF := GF) (γ.s2.trace 0) (T 0) t [e] $$ [H0 Ht]
      with ⟨%h, H0, Ht, Hlb⟩
    · iframe H0 Ht
    subst h
    imodintro
    simp only [traceSnoc]
    iframe
  · imod monoList_halves_update (GF := GF) (γ.s2.trace 1) (T 1) t [e] $$ [H1 Ht]
      with ⟨%h, H1, Ht, Hlb⟩
    · iframe H1 Ht
    subst h
    imodintro
    simp only [traceSnoc]
    iframe
  · imod monoList_halves_update (GF := GF) (γ.s2.trace 2) (T 2) t [e] $$ [H2 Ht]
      with ⟨%h, H2, Ht, Hlb⟩
    · iframe H2 Ht
    subst h
    imodintro
    simp only [traceSnoc]
    iframe

theorem traces3_agree (γ : ProtoNames) (T : Fin 3 → List Ev) (k : Fin 3) (t : List Ev) :
    traces3 (GF := GF) γ T ∗ traceHalf γ k t ⊢ ⌜T k = t⌝ := by
  unfold traces3 traceHalf
  iintro ⟨⟨H0, H1, H2⟩, Ht⟩
  rcases fin3_cases k with rfl | rfl | rfl
  · ihave %h := monoListAuthOwn_agree (GF := GF) _ _ _ _ _ $$ H0 Ht
    ipureintro; exact h.2
  · ihave %h := monoListAuthOwn_agree (GF := GF) _ _ _ _ _ $$ H1 Ht
    ipureintro; exact h.2
  · ihave %h := monoListAuthOwn_agree (GF := GF) _ _ _ _ _ $$ H2 Ht
    ipureintro; exact h.2

/-! ## Predictions -/

/-- The three predictions as a function. -/
def ws3 (ws0 ws1 ws2 : List w64) : Fin 3 → List w64 :=
  fun i => if i.val = 0 then ws0 else if i.val = 1 then ws1 else ws2

theorem preds_lookup (γ : ProtoNames) (P : GMap Nat (Option (List w64))) (ws0 ws1 ws2 : List w64) :
    ⊢ ghostMapAuth (GF := GF) γ.s2.pred 1 P -∗ predIdIs γ 0 ws0 -∗ predIdIs γ 1 ws1 -∗
        predIdIs γ 2 ws2 -∗
      ⌜∀ i : Fin 3, P.lookup i.val = some (some (ws3 ws0 ws1 ws2 i))⌝ := by
  unfold predIdIs
  iintro HP H0 H1 H2
  ihave %h0 := ghost_map_lookup $$ HP H0
  ihave %h1 := ghost_map_lookup $$ HP H1
  ihave %h2 := ghost_map_lookup $$ HP H2
  ipureintro
  intro i
  rcases fin3_cases i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem preds_get (γ : ProtoNames) (ws0 ws1 ws2 : List w64) (k : Fin 3) :
    predIdIs (GF := GF) γ 0 ws0 ∗ predIdIs γ 1 ws1 ∗ predIdIs γ 2 ws2 ⊢
      predIdIs γ k.val (ws3 ws0 ws1 ws2 k) := by
  rcases fin3_cases k with rfl | rfl | rfl
  · show _ ⊢ predIdIs γ 0 ws0
    iintro ⟨H0, -, -⟩; iexact H0
  · show _ ⊢ predIdIs γ 1 ws1
    iintro ⟨-, H1, -⟩; iexact H1
  · show _ ⊢ predIdIs γ 2 ws2
    iintro ⟨-, -, H2⟩; iexact H2

/-! ## Event tokens -/

theorem evTok_cases (γ : ProtoNames) (k : Fin 3) (e : Ev) :
    evTok (GF := GF) γ k e ⊢
      (∃ (m : Msg) (k' : Fin 3) (n : Nat), ⌜e = .msg m⌝ ∗ rxTok γ k' k n m) ∨
      (∃ (cid rid : w32) (i : RegInput w64), ⌜e.clientReq = some (cid, rid, i)⌝ ∗
        reqTok γ k (sint.Z cid, sint.Z rid) i) ∨
      ⌜e.recv = none ∧ e.clientReq = none⌝ := by
  cases e with
  | msg m =>
    unfold evTok
    iintro ⟨%k', %n, H⟩
    ileft
    iexists m, k', n
    iframe H
    ipureintro; rfl
  | read rid cid kk d =>
    show reqTok γ k (sint.Z cid, sint.Z rid) .read ⊢ _
    iintro H
    iright; ileft
    iexists cid, rid, .read
    iframe H
    ipureintro; rfl
  | write rid cid kk v d =>
    show reqTok γ k (sint.Z cid, sint.Z rid) (.write v) ⊢ _
    iintro H
    iright; ileft
    iexists cid, rid, .write v
    iframe H
    ipureintro; rfl
  | rmw rid cid kk d o n =>
    show reqTok γ k (sint.Z cid, sint.Z rid) (.cas o n) ⊢ _
    iintro H
    iright; ileft
    iexists cid, rid, .cas o n
    iframe H
    ipureintro; rfl
  | forceWrite =>
    iintro -; iright; iright; ipureintro; exact ⟨rfl, rfl⟩
  | recover q i =>
    iintro -; iright; iright; ipureintro; exact ⟨rfl, rfl⟩
  | exec q i =>
    iintro -; iright; iright; ipureintro; exact ⟨rfl, rfl⟩

/-- Consume the event's token from the invariant's maps. -/
theorem evTok_consume (γ : ProtoNames) (S : Inv2St) (k : Fin 3) (e : Ev) :
    ghostMapAuth (GF := GF) γ.s2.rx 1 S.rx ∗ ghostMapAuth γ.s2.reqs 1 S.reqs ∗ evTok γ k e ⊢ |==>
      (∃ rx' reqs', ⌜tokStep S k e rx' reqs'⌝ ∗ ghostMapAuth γ.s2.rx 1 rx' ∗
        ghostMapAuth γ.s2.reqs 1 reqs') := by
  iintro ⟨Hrx, Hreqs, Htok⟩
  icases evTok_cases γ k e $$ Htok with
    (⟨%m, %k', %n, %he, Ht⟩ | ⟨%cid, %rid, %i, %hc, Ht⟩ | %h)
  · unfold rxTok
    ihave %hl := ghost_map_lookup $$ Hrx Ht
    imod ghost_map_delete $$ Hrx Ht with Hrx
    imodintro
    iexists _, S.reqs
    iframe Hrx Hreqs
    ipureintro
    exact Or.inl ⟨m, k', n, he, hl, rfl, rfl⟩
  · unfold reqTok
    ihave %hl := ghost_map_lookup $$ Hreqs Ht
    imod ghost_map_delete $$ Hreqs Ht with Hreqs
    imodintro
    iexists S.rx, _
    iframe Hrx Hreqs
    ipureintro
    exact Or.inr (Or.inl ⟨cid, rid, i, hc, hl, rfl, rfl⟩)
  · imodintro
    iexists S.rx, S.reqs
    iframe Hrx Hreqs
    ipureintro
    exact Or.inr (Or.inr ⟨h.1, h.2, rfl, rfl⟩)

/-! ## Firing over the registrations -/

theorem fire_all2 (γ : ProtoNames) (info : GMap OpId OpInfo) (lin lin' : List (OpId × RegOutput w64))
    (E : CoPset) (hE : E = ⊤ \ ↑gryffN) :
    ∀ (L : List (OpId × RegOutput w64)) (S : List OpId) (σ σ' : w64),
      Perennial.gryff.replayOk σ (entriesI info L) σ' →
      (∀ x ∈ L, (info.lookup x.1).isSome ∧ x ∈ lin' ∧ (∀ o, (x.1, o) ∉ lin) ∧ x.1 ∉ S) →
      (L.map Prod.fst).Nodup →
      ghostVar γ.reg (1 : Qp).half σ ∗
          ([∗map] k ↦ x ∈ info, psiRes (GF := GF) γ lin lin' S k (infoMeta x)) ⊢
        |={E}=> ghostVar γ.reg (1 : Qp).half σ' ∗
          [∗map] k ↦ x ∈ info, psiRes γ lin lin' (S ++ L.map Prod.fst) k (infoMeta x)
  | [], S, σ, σ', hr, _, _ => by
    have : σ' = σ := hr
    subst this
    simp only [List.map_nil, List.append_nil]
    iintro ⟨H1, H2⟩
    imodintro
    iframe
  | x :: L, S, σ, σ', hr, hx, hnd => by
    obtain ⟨hsome, hlin', hnl, hnS⟩ := hx x (List.mem_cons_self ..)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hsome
    have hent : entriesI info (x :: L) = (m.input, x.2) :: entriesI info L := by
      simp [entriesI, hm]
    rw [hent] at hr
    obtain ⟨hout, hr'⟩ := hr
    rw [List.map_cons, List.nodup_cons] at hnd
    iintro ⟨Hreg, Hmap⟩
    icases (BigSepM.bigSepM_delete (show get? info x.1 = some m from hm)).1 $$ Hmap with ⟨Hm, Hrest⟩
    have hpsi : psiRes (GF := GF) γ lin lin' S x.1 (infoMeta m) = opResNL γ lin x.1 (infoMeta m) := by
      unfold psiRes; rw [if_neg hnS]
    rw [hpsi]
    unfold opResNL
    icases Hm with (⟨-, %Q, #HQ, HAU⟩ | ⟨%o, %Q, %σ, %σ', %ho, -, -⟩)
    rotate_left
    · exact absurd ho (hnl o)
    imod opAU_fire γ m.input Q σ E hE $$ [HAU Hreg] with ⟨Hreg, HQr⟩
    · iframe
    rw [hout]
    ihave Hmap : [∗map] k ↦ y ∈ info, psiRes (GF := GF) γ lin lin' (S ++ [x.1]) k (infoMeta y)
      $$ [Hrest HQr]
    · iapply (BigSepM.bigSepM_delete (show get? info x.1 = some m from hm)).2
      isplitl [HQr]
      · have : psiRes (GF := GF) γ lin lin' (S ++ [x.1]) x.1 (infoMeta m) =
            opRes γ lin' x.1 (infoMeta m) := by
          unfold psiRes; rw [if_pos (by simp)]
        rw [this]
        unfold opRes
        iright
        iexists x.2, Q, σ, (casApply σ m.input).1
        isplitr
        · ipureintro; exact hlin'
        isplitr
        · iexact HQ
        ileft
        inext
        iexact HQr
      · iapply (BigSepM.bigSepM_mono (fun {k y} hk => by
          have hk' : x.1 ≠ k := by
            intro e; subst e
            rw [Iris.Std.get?_delete_eq rfl] at hk; cases hk
          rw [psiRes_congr γ lin lin' S (S ++ [x.1]) k (infoMeta y) (by
            simp only [List.mem_append, List.mem_singleton]
            exact ⟨Or.inl, fun h => h.elim id (fun e => absurd e.symm hk')⟩)])) $$ Hrest
    ihave H := fire_all2 γ info lin lin' E hE L (S ++ [x.1]) _ σ' hr' (by
      intro y hy
      obtain ⟨h1, h2, h3, h4⟩ := hx y (List.mem_cons_of_mem _ hy)
      refine ⟨h1, h2, h3, ?_⟩
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨h4, fun e => hnd.1 (e ▸ List.mem_map_of_mem hy)⟩) hnd.2 $$ [Hreg Hmap]
    · iframe
    rw [show S ++ (x :: L).map Prod.fst = S ++ [x.1] ++ L.map Prod.fst by simp]
    iexact H

/-- **Linearize new entries**: from the invariant's operation resources (under its two laters,
paid with two credits), fire the new entries' atomic updates from `σ` to `σ'`; every operation's
resources are then valid for `lin ++ new`. -/
theorem fire_new (γ : ProtoNames) (info : GMap OpId OpInfo) (lin new : List (OpId × RegOutput w64))
    (σ σ' : w64) (E : CoPset) (hE : E = ⊤ \ ↑gryffN)
    (hr : Perennial.gryff.replayOk σ (entriesI info new) σ')
    (hreg : ∀ x ∈ new, (info.lookup x.1).isSome)
    (hnd : ((lin ++ new).map Prod.fst).Nodup) :
    ghostVar (GF := GF) γ.reg (1 : Qp).half σ ∗
        ▷ ([∗map] k ↦ x ∈ info, opRes γ lin k (infoMeta x)) ∗ £ 1 ∗ £ 1 ⊢
      |={E}=> ghostVar γ.reg (1 : Qp).half σ' ∗
        [∗map] k ↦ x ∈ info, opRes γ (lin ++ new) k (infoMeta x) := by
  iintro ⟨Hreg, Hres, Hlc1, Hlc2⟩
  ihave Hres := BI.later_mono (BigSepM.bigSepM_mono (fun {k x} _ => opRes_to_NL γ lin k (infoMeta x))
    |>.trans BigSepM.bigSepM_later_2) $$ Hres
  imod lc_fupd_elim_later $$ Hlc1 Hres with Hres
  imod lc_fupd_elim_later $$ Hlc2 Hres with Hres
  ihave Hres : [∗map] k ↦ x ∈ info, psiRes (GF := GF) γ lin (lin ++ new) [] k (infoMeta x) $$ [Hres]
  · iapply (BigSepM.bigSepM_mono (fun {k x} _ => by
      unfold psiRes; rw [if_neg List.not_mem_nil])) $$ Hres
  rw [List.map_append, List.nodup_append] at hnd
  imod fire_all2 γ info lin (lin ++ new) E hE new [] σ σ' hr
    (fun x hx => ⟨hreg x hx, List.mem_append_right _ hx,
      fun o ho => hnd.2.2 _ (List.mem_map_of_mem ho) _ (List.mem_map_of_mem hx) rfl,
      List.not_mem_nil⟩) hnd.2.1
    $$ [Hreg Hres] with ⟨Hreg, Hres⟩
  · iframe
  imodintro
  iframe Hreg
  iapply (BigSepM.bigSepM_mono (fun {k x} _ => by
      unfold psiRes
      by_cases hkn : k ∈ [] ++ new.map Prod.fst
      · rw [if_pos hkn]
      · rw [if_neg hkn]
        refine (NL_to_opRes γ lin k (infoMeta x)).trans (opRes_lin_grow γ lin _ k (infoMeta x)
          (fun y hy => List.mem_append_left _ hy) (fun o ho => ?_))
        rcases List.mem_append.1 ho with ho | ho
        · exact ho
        · exact absurd (by simpa using List.mem_map_of_mem (f := Prod.fst) ho) hkn)) $$ Hres

end

end Perennial.gryff

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness
open model kahn pure p2

section
variable {PROP : Type _} [BI PROP] [BIAffine PROP]

theorem ids_update (Φ : Option Nat → Nat → PROP) (M : GMap Nat Nat) (i n : Nat) (hi : i < 3) :
    ([∗list] j ∈ List.range 3, Φ (M.lookup j) j) ∗ Φ (some n) i ⊢
      [∗list] j ∈ List.range 3, Φ ((M.insert i n).lookup j) j := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · show (Φ (M.lookup 0) 0 ∗ Φ (M.lookup 1) 1 ∗ Φ (M.lookup 2) 2 ∗ emp) ∗ Φ (some n) 0 ⊢
      Φ (some n) 0 ∗ Φ (M.lookup 1) 1 ∗ Φ (M.lookup 2) 2 ∗ emp
    iintro ⟨⟨-, H1, H2, -⟩, Hn⟩
    iframe Hn H1 H2
  · show (Φ (M.lookup 0) 0 ∗ Φ (M.lookup 1) 1 ∗ Φ (M.lookup 2) 2 ∗ emp) ∗ Φ (some n) 1 ⊢
      Φ (M.lookup 0) 0 ∗ Φ (some n) 1 ∗ Φ (M.lookup 2) 2 ∗ emp
    iintro ⟨⟨H0, -, H2, -⟩, Hn⟩
    iframe Hn H0 H2
  · show (Φ (M.lookup 0) 0 ∗ Φ (M.lookup 1) 1 ∗ Φ (M.lookup 2) 2 ∗ emp) ∗ Φ (some n) 2 ⊢
      Φ (M.lookup 0) 0 ∗ Φ (M.lookup 1) 1 ∗ Φ (some n) 2 ∗ emp
    iintro ⟨⟨H0, H1, -, -⟩, Hn⟩
    iframe Hn H0 H1

end

end Perennial.gryff

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness
open model kahn pure p2

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

theorem traces3_agree' (γ : ProtoNames) (T : Fin 3 → List Ev) (k : Fin 3) (t : List Ev) :
    ⊢ traces3 (GF := GF) γ T -∗ traceHalf γ k t -∗ ⌜T k = t⌝ := by
  iintro H1 H2
  iapply traces3_agree γ T k t
  iframe H1 H2

theorem traces3_lb (γ : ProtoNames) (T : Fin 3 → List Ev) (k : Fin 3) (t : List Ev) :
    ⊢ traces3 (GF := GF) γ T -∗ traceLb γ k t -∗ ⌜t <+: T k⌝ := by
  unfold traces3 traceLb
  iintro ⟨H0, H1, H2⟩ Ht
  rcases fin3_cases k with rfl | rfl | rfl
  · ihave %h := mono_list_auth_lb_valid (GF := GF) _ _ _ _ $$ H0 Ht
    ipureintro; exact h.2
  · ihave %h := mono_list_auth_lb_valid (GF := GF) _ _ _ _ $$ H1 Ht
    ipureintro; exact h.2
  · ihave %h := mono_list_auth_lb_valid (GF := GF) _ _ _ _ $$ H2 Ht
    ipureintro; exact h.2

/-- A client request's token names its replica and input. -/
theorem evTok_req_lookup (γ : ProtoNames) (k : Fin 3) (e : Ev)
    (R : GMap OpId (Nat × RegInput w64)) :
    ⊢ ghostMapAuth (GF := GF) γ.s2.reqs 1 R -∗ evTok γ k e -∗
      ⌜∀ cid rid i, e.clientReq = some (cid, rid, i) →
        R.lookup (sint.Z cid, sint.Z rid) = some (k.val, i)⌝ := by
  iintro HR Htok
  icases evTok_cases γ k e $$ Htok with
    (⟨%m, %k', %n, %he, -⟩ | ⟨%cid, %rid, %i, %hc, Ht⟩ | %h)
  · ipureintro; intro cid rid i hc; subst he; cases hc
  · unfold reqTok
    ihave %hl := ghost_map_lookup $$ HR Ht
    ipureintro
    intro cid' rid' i' hc'
    rw [hc] at hc'; cases hc'; exact hl
  · ipureintro; intro cid rid i hc; rw [h.2] at hc; cases hc

end

end Perennial.gryff

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness
open model kahn pure p2

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

theorem connRep_lookup (γ : ProtoNames) (R : GMap Nat Nat) (conn : Nat) (k : Fin 3) (last : Int) :
    ⊢ ghostMapAuth (GF := GF) γ.s2.connRep 1 R -∗ (⌜last < 0⌝ ∨ connRepIs γ conn k) -∗
      ⌜last < 0 ∨ R.lookup conn = some k.val⌝ := by
  iintro HR (%hl | H)
  · ipureintro; exact Or.inl hl
  · unfold connRepIs
    ihave %h := ghost_map_lookup $$ HR H
    ipureintro; exact Or.inr h

theorem connRep_update (γ : ProtoNames) (R : GMap Nat Nat) (conn : Nat) (k : Fin 3) (last : Int)
    (hn : last < 0 → R.lookup conn = none) :
    ghostMapAuth (GF := GF) γ.s2.connRep 1 R ∗ (⌜last < 0⌝ ∨ connRepIs γ conn k) ⊢ |==>
      (ghostMapAuth γ.s2.connRep 1 (R.insert conn k.val) ∗ connRepIs γ conn k) := by
  iintro ⟨HR, (%hl | #H)⟩
  · imod ghost_map_insert_persist conn k.val (hn hl) $$ HR with ⟨HR, #Hel⟩
    imodintro
    unfold connRepIs
    iframe HR Hel
  · unfold connRepIs
    ihave %h := ghost_map_lookup $$ HR H
    have e : R.insert conn k.val = R := GMap.insert_id R conn k.val (by rw [h])
    rw [e]
    imodintro
    iframe HR H

end

end Perennial.gryff
