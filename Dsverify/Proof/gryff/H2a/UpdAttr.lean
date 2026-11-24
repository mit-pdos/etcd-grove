/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/UpdAttr.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: `updateAttributes`
-/
module

public import Dsverify.Proof.gryff.H2a.Conf
public import Dsverify.Proof.gryff.H2a.EpAt
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The model's `updateAttributes` as three row steps and the `maxSeq` step -/

namespace Perennial.gryff.model


abbrev UA := w32 × Deps × Bool

/-- One command's iteration for row `q` (the same for every command: idempotent). -/
def uaF (s : RState) (q : Nat) (st : UA) : Option UA :=
  match s.confAt q with
  | some hi =>
    if sgt hi (st.2.1.at q) = true then
      match (if inBox (BitVec.ofNat 32 q) hi = true then s.inst (BitVec.ofNat 32 q) hi else none) with
      | some w => some (if sle st.1 w.seq = true then w.seq + 1 else st.1, st.2.1.setAt q hi, true)
      | none => none
    else some st
  | none => some st

/-- One command's iteration of the `maxSeqPerKey1` loop. -/
def uaM (s : RState) (st : UA) : UA :=
  match s.maxSeqK0 with
  | some ms => if sle st.1 ms = true then (ms + 1, st.2.1, true) else st
  | none => st

/-- Row `q`'s loop: skipped, or every command (none: once). -/
def uaG (s : RState) (cmds : List Cmd) (replica : w32) (q : Nat) (st : UA) : Option UA :=
  if (s.id ≠ replica ∧ BitVec.ofNat 32 q = replica) ∨ cmds = [] then some st else uaF s q st

def uaH (s : RState) (cmds : List Cmd) (st : UA) : UA := if cmds = [] then st else uaM s st

theorem forIn_opt_idem {α β : Type} (l : List α) (init : β) (body : α → β → Option (ForInStep β))
    (f : β → Option β) (hb : ∀ a b, body a b = (f b).map ForInStep.yield)
    (hidem : ∀ b b', f b = some b' → f b' = some b') :
    forIn l init body = if l = [] then some init else f init := by
  have hbody : body = fun a b => (f b).map ForInStep.yield := funext fun a => funext fun b => hb a b
  subst hbody
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, reduceCtorEq, ite_false]
    cases hf : f init with
    | none => rfl
    | some b' =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [ih]
      split
      · rfl
      · exact hidem _ _ hf

theorem sle_succ_idem (a w : w32) :
    (if sle (if sle a w = true then w + 1 else a) w = true then w + 1
      else (if sle a w = true then w + 1 else a)) = (if sle a w = true then w + 1 else a) := by
  by_cases h : sle a w = true
  · simp only [h, ite_true]; split <;> rfl
  · simp only [h, Bool.false_eq_true, ite_false]

theorem uaF_idem (s : RState) (q : Nat) (st st' : UA) (h : uaF s q st = some st') :
    uaF s q st' = some st' := by
  unfold uaF at h ⊢
  cases hc : s.confAt q with
  | none => simp [hc] at h ⊢
  | some hi =>
    simp only [hc] at h ⊢
    by_cases hg : sgt hi (st.2.1.at q) = true
    · simp only [hg, ite_true] at h
      cases hw : (if inBox (BitVec.ofNat 32 q) hi = true then s.inst (BitVec.ofNat 32 q) hi else none) with
      | none => simp [hw] at h
      | some w =>
        simp only [hw, Option.some.injEq] at h
        subst h
        by_cases hg' : sgt hi ((st.2.1.setAt q hi).at q) = true
        · simp only [Deps.setAt, List.set_set] at hg' ⊢
          simp only [hg', ite_true, hw, sle_succ_idem, ite_self]
        · simp only [hg', Bool.false_eq_true, ite_false]
    · simp only [hg, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst h
      simp [hg]

theorem uaM_idem (s : RState) (st : UA) : uaM s (uaM s st) = uaM s st := by
  unfold uaM
  cases s.maxSeqK0 with
  | none => rfl
  | some ms =>
    dsimp only
    by_cases h : sle st.1 ms = true
    · simp only [h, ite_true]; split <;> rfl
    · simp only [h, Bool.false_eq_true, ite_false]

theorem forIn_three {β : Type} (init : β) (B : Nat → β → Option (ForInStep β))
    (g : Nat → β → Option β) (hB : ∀ q b, B q b = (g q b).map ForInStep.yield) :
    forIn [0, 1, 2] init B = (g 0 init >>= g 1 >>= g 2) := by
  have hbody : B = fun a b => (g a b).map ForInStep.yield := funext fun a => funext fun b => hB a b
  subst hbody
  simp only [List.forIn_cons, List.forIn_nil]
  cases g 0 init <;> simp
  rename_i b1
  cases g 1 b1 <;> simp
  rename_i b2
  cases g 2 b2 <;> simp

theorem updateAttributes_eq (s : RState) (cmds : List Cmd) (seq0 : w32) (deps0 : Deps)
    (replica : w32) :
  updateAttributes s cmds seq0 deps0 replica =
    (do let st1 ← uaG s cmds replica 0 (seq0, deps0, false)
        let st2 ← uaG s cmds replica 1 st1
        let st3 ← uaG s cmds replica 2 st2
        some (uaH s cmds st3)) := by
  unfold updateAttributes
  dsimp only
  rw [forIn_three (g := uaG s cmds replica)]
  · have : ∀ (X : Option UA) (F : UA → Option UA), (X >>= F) = Option.bind X F := fun _ _ => rfl
    simp only [this, Option.bind_assoc]
    congr 1; funext st1; congr 1; funext st2; congr 1; funext st3
    rw [forIn_opt_idem (f := fun st : w32 × Bool => some (match s.maxSeqK0 with
      | some ms => if sle st.1 ms = true then (ms + 1, true) else st
      | none => st))]
    · unfold uaH uaM
      split
      · rfl
      · cases s.maxSeqK0 with
        | none => rfl
        | some ms => by_cases h : sle st3.1 ms = true <;> simp [h]
    · intro a b; cases s.maxSeqK0 <;> simp; split <;> rfl
    · intro b b' h; simp only [Option.some.injEq] at h; subst h
      cases s.maxSeqK0 with
      | none => rfl
      | some ms => simp only; by_cases h : sle b.1 ms = true <;> simp [h]
  · intro q b
    unfold uaG
    split
    · simp_all
    · rw [forIn_opt_idem (f := uaF s q)]
      · by_cases hc : cmds = []
        · simp [hc]
        · simp only [hc, ite_false]
          rename_i hskip
          simp only [hskip, false_or, hc, ite_false]
          cases uaF s q (b.1, b.2.1, b.2.2) <;> rfl
      · intro a st
        unfold uaF
        cases s.confAt q with
        | none => rfl
        | some hi =>
          dsimp only
          by_cases hg : sgt hi (st.2.1.at q) = true
          · simp only [hg, ite_true]
            cases hw : (if inBox (BitVec.ofNat 32 q) hi = true then s.inst (BitVec.ofNat 32 q) hi
                else none) with
            | none => rfl
            | some w => by_cases h2 : sle st.1 w.seq = true <;> simp [h2]
          · simp [hg]
      · exact uaF_idem s q

end Perennial.gryff.model

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps UA uaF uaG uaH uaM)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem ofNat_toNat_sint' (qv : w64) (h : 0 ≤ sint.Z qv ∧ sint.Z qv < 5) :
    BitVec.ofNat 32 (sint.Z qv).toNat = W32 (sint.Z qv) := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, sint.Z qv = n := ⟨_, (Int.toNat_of_nonneg h.1).symm⟩
  rw [hn, Int.toNat_natCast]
  simp only [W32, BitVec.ofInt_natCast]

/-- The state after `n` rows (`0..3`). -/
def stq (st0 st1 st2 st3 : UA) : Nat → UA
  | 0 => st0
  | 1 => st1
  | 2 => st2
  | _ => st3

/-- `updateAttributes` at fixed witnesses of `epaxosOwn` (it only reads the EPaxos state). -/
theorem wp_updateAttributes_at (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s : RState)
    (W : EpW) (sl : GoSlice) (gs : List src.state.Command) (seq : w32) (deps : GoArray w32 5)
    (replica inst : w32) (res : w32 × Deps × Bool)
    (hcs : model.cmdsOk (gs.map cmdOf) = true) (hrep : 0 ≤ sint.Z replica ∧ sint.Z replica < 3)
    (hid : s.id = rid32 k)
    (hres : model.updateAttributes s (gs.map cmdOf) seq (depsOf deps) replica = some res) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwnAt ρ h r xs s W ∗ sl ↦*□ gs }}
      (App (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"updateAttributes")) (Val #sl)) (Val #seq)) (Val #deps)) (Val #replica)) (Val #inst))
    {{ (seq' : w32) (deps' : GoArray w32 5) (ch : Bool), RET (PairV (PairV #seq' #deps') #ch);
        epaxosOwnAt ρ h r xs s W ∗ ⌜res = (seq', depsOf deps', ch)⌝ }} := by
  obtain ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩ := W
  rw [model.updateAttributes_eq] at hres
  obtain ⟨st1, h1, hres⟩ := Option.bind_eq_some_iff.1 hres
  obtain ⟨st2, h2, hres⟩ := Option.bind_eq_some_iff.1 hres
  obtain ⟨st3, h3, hres⟩ := Option.bind_eq_some_iff.1 hres
  simp only [Option.some.injEq] at hres
  subst hres
  wp_start as ⟨#Hae, Hep, #Hsl⟩
  unfold attrEnv
  icases Hae with ⟨#HR, #HgR, #HId, #HN, #Hfix⟩
  unfold h2Fixed
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, #Hst, #Hsok, -⟩
  simp only [epaxosOwnAt]
  icases Hep with ⟨#HR', #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  ihave Hconfs : [∗list] q ↦ cr ∈ cfs, confRepS cr (s.confAt q) $$ [Hconfs]
  · iapply BigSepL.bigSepL_mono _ $$ Hconfs
    intro q cr _; exact (confRep_S cr _).1
  icases (confRep_S ..).1 $$ Hms with Hms
  wp_auto
  ihave IH : iprop(∃ qv : w64, q_ptr ↦ qv ∗
      seq_ptr ↦ (stq (seq, depsOf deps, false) st1 st2 st3 (sint.Z qv).toNat).1 ∗
      deps_ptr ↦ (array.mk 5 (stq (seq, depsOf deps, false) st1 st2 st3 (sint.Z qv).toNat).2.1 :
        GoArray w32 5) ∗
      changed_ptr ↦ (stq (seq, depsOf deps, false) st1 st2 st3 (sint.Z qv).toNat).2.2 ∗
      ⌜0 ≤ sint.Z qv ∧ sint.Z qv ≤ 3⌝) $$ [q seq deps changed]
  · iexists W64 0; iframe; ipureintro; word
  wp_for IH
  icases IH with ⟨q, seq, deps, changed, %Hq⟩
  wp_auto
  wp_if_destruct
  · have hq3 : sint.Z qv < 3 := by have := go.intoVal_inj Hif; simp at this; word
    have hq5 : 0 ≤ sint.Z qv ∧ sint.Z qv < 5 := by omega
    have hn := ofNat_toNat_sint' qv hq5
    wp_join (Q := fun v => iprop(⌜(v = continueVal ∧
          (s.id ≠ replica ∧ BitVec.ofNat 32 (sint.Z qv).toNat = replica)) ∨
        (v = executeVal ∧ ¬ (s.id ≠ replica ∧ BitVec.ofNat 32 (sint.Z qv).toNat = replica))⌝ ∗
        q_ptr ↦ qv ∗ replica_ptr ↦ replica)) at (if: _ then _ else _)
      with [q replica] as ⟨%Hv, q, replica⟩
    · rw [hid, hn]
      repeat' (first | wp_if_destruct | wp_auto)
      all_goals (iframe; ipureintro)
      all_goals (try (subst replica))
      all_goals (simp_all)
    have hG : ∀ n, n < 3 → uaG s (gs.map cmdOf) replica n (stq (seq, depsOf deps, false) st1 st2 st3 n) =
        some (stq (seq, depsOf deps, false) st1 st2 st3 (n + 1)) := by
      intro n hn
      rcases n with _ | _ | _ | n
      · exact h1
      · exact h2
      · exact h3
      · omega
    have hn1 : (sint.Z (qv + W64 1)).toNat = (sint.Z qv).toNat + 1 := by word
    have hGn := hG _ (by omega : (sint.Z qv).toNat < 3)
    rcases Hv with ⟨rfl, hskip⟩ | ⟨rfl, hskip⟩
    · wp_auto
      wp_for_post
      unfold uaG at hGn
      rw [if_pos (Or.inl hskip)] at hGn
      iframe
      iexists (qv + W64 1)
      rw [hn1, ← Option.some.inj hGn]
      iframe; ipureintro; word
    · wp_auto
      generalize hA : stq (seq, depsOf deps, false) st1 st2 st3 (sint.Z qv).toNat = A at *
      generalize hB : stq (seq, depsOf deps, false) st1 st2 st3 ((sint.Z qv).toNat + 1) = B at *
      generalize hnq : (sint.Z qv).toNat = n at *
      ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
      ihave II : iprop(∃ iv : w64, i_ptr ↦ iv ∗
          seq_ptr ↦ (if sint.Z iv = 0 then A else B).1 ∗
          deps_ptr ↦ (array.mk 5 (if sint.Z iv = 0 then A else B).2.1 : GoArray w32 5) ∗
          changed_ptr ↦ (if sint.Z iv = 0 then A else B).2.2 ∗
          ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z sl.len⌝) $$ [i seq deps changed]
      · iexists W64 0; iframe; ipureintro; word
      wp_for II
      icases II with ⟨i, seq, deps, changed, %Hi⟩
      generalize hC : (if sint.Z iv = 0 then A else B) = C
      wp_auto
      wp_if_destruct
      · have hilt : sint.Z iv < sint.Z sl.len := by simpa using go.intoVal_inj Hif
        have hne : gs.map cmdOf ≠ [] := by
          intro h0; have := Hsllen.1; simp at h0; subst h0; simp at this; word
        have hFA : uaF s n A = some B := by
          unfold uaG at hGn; rw [if_neg (fun h => h.elim hskip hne)] at hGn; exact hGn
        have hF : uaF s n C = some B := by
          rw [← hC]; split
          · exact hFA
          · exact model.uaF_idem _ _ _ _ hFA
        obtain ⟨c, hc⟩ : ∃ c, gs[(sint.Z iv).toNat]? = some c :=
          ⟨_, List.getElem?_eq_getElem (by have := Hsllen.1; word)⟩
        have hcok : c.K' = W64 0 ∧ c.Op' = W8 6 := by
          have := hcs
          simp only [model.cmdsOk, List.all_eq_true, List.mem_map] at this
          have h1 := this (cmdOf c) ⟨c, List.mem_of_getElem? hc, rfl⟩
          simp [model.Cmd.ok, cmdOf, model.opCAS] at h1
          exact ⟨h1.2, h1.1⟩
        have hib : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z sl.len := ⟨Hi.1, hilt⟩
        rw [ite_eq_left hib]
        icases ownSlice_elem_acc (sint.Z iv) c sl DFrac.discard gs hib.1 hc $$ Hsl with ⟨#Hc0, -⟩
        iStructNamed Hc0
        wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
        rw [hcok.1]
        have hcfs : cfs.length = 3 := Hf.2.1
        obtain ⟨cr, hcr⟩ : ∃ cr, cfs[n]? = some cr :=
          ⟨_, List.getElem?_eq_getElem (by rw [hcfs]; omega)⟩
        ihave %Hcfslen := ownSlice_len _ _ _ $$ Hcfs
        have hqb : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z c1S.len := by
          have := Hcfslen.1; rw [hcfs] at this; word
        rw [ite_eq_left hqb]
        wp_apply wp_load_slice_index (t := go.GoType.MapType src.state.Key.ty
            (go.GoType.MapType src.state.Operation.ty go.int32)) c1S (sint.Z qv) cfs _ cr hqb.1
            $$ [$Hcfs] as -
        · ipureintro; rw [hnq]; exact hcr
        icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun q cr => confRepS cr (s.confAt q)) hcr)
          $$ Hconfs with ⟨Hc, Hcclose⟩
        icases (confRepS_open ..).1 $$ Hc with ⟨%m1, Hm1, %Hm1o, Hc⟩
        wp_apply (wp_map_lookup2 _ _ cr m1 (W64 0) (DFrac.own 1)) $$ [$Hm1] as Hm1
        have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
        cases hcv : s.confAt n with
        | none =>
          icases Hc with %Hn
          rw [Hn]
          wp_auto
          wp_for_post
          have hCB : C = B := by
            have := hF; unfold model.uaF at this; rw [hcv] at this; exact Option.some.inj this
          ihave Hc : confRepS cr (s.confAt n) $$ [Hm1]
          · iapply (confRepS_open ..).2; iexists m1; iframe; rw [hcv]; ipureintro; exact ⟨Hm1o, Hn⟩
          ihave Hconfs := Hcclose $$ %(fun q cr => confRepS cr (s.confAt q)) [] Hc
          · iintro !> %k %y %_ %_ H; iexact H
          iframe
          iexists (iv + W64 1)
          rw [hiv1, if_neg (by omega), ← hCB]
          iframe; ipureintro; word
        | some v =>
          icases Hc with ⟨%ir, %im, %Hir, Him, %Himp⟩
          rw [Hir]
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          rw [ite_eq_left hib]
          wp_apply (IntoValTyped.wp_load (t := src.state.Operation.ty) _ _ _) $$ [$Op] as -
          rw [hcok.2]
          wp_apply (wp_map_lookup2 _ _ ir im (W8 6) (DFrac.own 1)) $$ [$Him] as Him
          have him6 : im.lookup (W8 6) = some v := by
            rw [Himp]; simp (config := {decide := true}) [opsAll]
          rw [him6]
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          have hq5' : 0 ≤ sint.Z qv ∧ sint.Z qv < 5 := hq5
          rw [ite_eq_left hq5']
          ihave %Hdl := array_len _ _ _ _ $$ deps
          wp_apply wire.wp_load_arr32 $$ [$deps] as deps
          · ipureintro; word
          have hat : (array.mk 5 C.2.1 : GoArray w32 5).arr.getD (sint.Z qv).toNat (W32 0) =
              C.2.1.at n := by
            simp only [model.Deps.at, hnq]; rfl
          rw [hat]
          ihave Hc : confRepS cr (s.confAt n) $$ [Hm1 Him]
          · iapply (confRepS_open ..).2
            iexists m1; iframe; rw [hcv]
            isplitr
            · ipureintro; exact Hm1o
            · iexists ir, im; iframe; ipureintro; exact ⟨Hir, Himp⟩
          ihave Hconfs := Hcclose $$ %(fun q cr => confRepS cr (s.confAt q)) [] Hc
          · iintro !> %k %y %_ %_ H; iexact H
          wp_if_destruct
          · have hg : model.sgt v (C.2.1.at n) = true := by
              simp only [model.sgt, model.slt, decide_eq_true_eq]; omega
            obtain ⟨w, ⟨hwin, hws⟩, hBw⟩ : ∃ w, (model.inBox (BitVec.ofNat 32 n) v = true ∧
                s.inst (BitVec.ofNat 32 n) v = some w) ∧
                B = (if model.sle C.1 w.seq = true then w.seq + 1 else C.1, C.2.1.setAt n v, true) := by
              have := hF; unfold model.uaF at this; rw [hcv] at this
              simp only [hg, ite_true] at this
              by_cases hb : model.inBox (BitVec.ofNat 32 n) v = true
              · simp only [hb, ite_true] at this
                cases hsw : s.inst (BitVec.ofNat 32 n) v with
                | none => simp [hsw] at this
                | some w => rw [hsw] at this; exact ⟨w, ⟨hb, rfl⟩, (Option.some.inj this).symm⟩
              · simp [hb] at this
            rw [ite_eq_left hq5']
            wp_apply wire.wp_store_arr32 $$ [$deps] as deps
            · ipureintro; word
            rw [hnq]
            have hn3 : n < 3 := by omega
            obtain ⟨sq, hsq⟩ : ∃ sq, isp[n]? = some sq :=
              ⟨_, List.getElem?_eq_getElem (by rw [Hf.1]; exact hn3)⟩
            icases rows_acc' M isp n sq hsq $$ Hrows with ⟨Hrow, Hrowsc⟩
            icases (Perennial.gryff.replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
            have hvb : 0 ≤ sint.Z v ∧ sint.Z v < model.SLOTS := by
              simp only [model.inBox, decide_eq_true_eq] at hwin; exact ⟨hwin.2.2.1, hwin.2.2.2⟩
            obtain ⟨p, hp⟩ : ∃ p, ptrs[(sint.Z v).toNat]? = some p :=
              ⟨_, List.getElem?_eq_getElem (by
                rw [Hrowf.1]; unfold Perennial.gryff.replica.nSlots; unfold model.SLOTS at hvb; omega)⟩
            have hnZ : sint.Z (BitVec.ofNat 32 n) = n := by
              rcases n with _ | _ | _ | n <;> first | rfl | omega
            have hM : M.lookup (sint.Z (BitVec.ofNat 32 n), sint.Z v) = some p := by
              have h1 := Hrowf.2 _ p hp
              have h2 := Hf.2.2.2.2.2.2.1 _ _ hwin
              rw [hws, hnZ] at h2
              rw [hnZ]
              rw [show (((sint.Z v).toNat : Nat) : Int) = sint.Z v by omega] at h1
              rw [h1] at h2 ⊢
              split at h2 <;> simp_all
            icases insts_update ρ xs s M (BitVec.ofNat 32 n) v p w hM hws $$ Hinsts with ⟨Hc, Hiclose⟩
            icases (copyRep_open ..).1 $$ Hc with ⟨%ivs, Hiv, Hcmds, Hlb, %Hivf⟩
            ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
            have hqi : 0 ≤ sint.Z qv ∧ sint.Z qv < sint.Z ispS.len := by
              have := HispSlen.1; rw [Hf.1] at this; word
            rw [ite_eq_left hqi]
            wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
              src.gryff.Instance.ty)) ispS (sint.Z qv) isp _ sq hqi.1 $$ [$Hisp] as -
            · ipureintro; rw [hnq]; exact hsq
            ihave %Hsqlen := ownSlice_len _ _ _ $$ Hrow
            have hvw : sint.Z (W64 (sint.Z v)) = sint.Z v := by word
            have hvi : 0 ≤ sint.Z (W64 (sint.Z v)) ∧ sint.Z (W64 (sint.Z v)) < sint.Z sq.len := by
              rw [hvw]; have := Hsqlen.1; rw [Hrowf.1] at this
              unfold Perennial.gryff.replica.nSlots at this; unfold model.SLOTS at hvb; word
            rw [ite_eq_left hvi]
            wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq
              (sint.Z (W64 (sint.Z v))) ptrs _ p hvi.1 $$ [$Hrow] as Hrow
            · ipureintro; rw [hvw]; exact hp
            have hseq : ivs.Seq' = w.seq := Hivf.2.2.1
            rw [hseq]
            wp_join iprop(seq_ptr ↦ B.1 ∗ sq ↦* ptrs ∗ p ↦ ivs ∗ e_ptr ↦ h ∗ q_ptr ↦ qv ∗
                highestInterf_ptr ↦ v)
              with [seq Hrow Hiv e q highestInterf] as ⟨seq, Hrow, Hiv, e, q, highestInterf⟩
            · have hsle : model.sle C.1 w.seq = true := by
                simp only [model.sle, decide_eq_true_eq]; exact Hif
              rw [ite_eq_left hqi]
              wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
                src.gryff.Instance.ty)) ispS (sint.Z qv) isp _ sq hqi.1 $$ [$Hisp] as -
              · ipureintro; rw [hnq]; exact hsq
              rw [ite_eq_left hvi]
              wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq
                (sint.Z (W64 (sint.Z v))) ptrs _ p hvi.1 $$ [$Hrow] as Hrow
              · ipureintro; rw [hvw]; exact hp
              wp_join_done
              rw [hBw, hsle, ← hseq]; simp only [ite_true]; iframe
            · have hsle : model.sle C.1 w.seq = false := by
                simp only [model.sle, decide_eq_false_iff_not]; exact Hif
              rw [hBw, hsle]; iframe
            ihave Hc := (copyRep_open ρ xs _ p w).2 $$ [Hiv Hcmds Hlb]
            · iexists ivs; iframe; ipureintro; exact Hivf
            ihave Hinsts := Hiclose $$ %s %w [] Hc
            · ipureintro; exact ⟨hws, fun _ _ _ => rfl⟩
            ihave Hrow := (Perennial.gryff.replica.rowOwn_open M _ sq).2 $$ [Hrow]
            · iexists ptrs; iframe; ipureintro; exact Hrowf
            ihave Hrows := Hrowsc $$ %M %(fun _ _ _ => rfl) Hrow
            wp_for_post
            iframe
            iexists (iv + W64 1)
            rw [hiv1, if_neg (by omega), hBw]
            iframe; ipureintro; word
          · wp_for_post
            have hCB : C = B := by
              have := hF; unfold model.uaF at this; rw [hcv] at this
              have hg : model.sgt v (C.2.1.at n) = false := by
                simp only [model.sgt, model.slt, decide_eq_false_iff_not]; omega
              simp only [hg, Bool.false_eq_true, ite_false] at this; exact Option.some.inj this
            iframe
            iexists (iv + W64 1)
            rw [hiv1, if_neg (by omega), ← hCB]
            iframe; ipureintro; word
      · have hi3 : ¬ sint.Z iv < sint.Z sl.len := fun h' => Hif (by rw [decide_eq_true h'])
        rw [decide_eq_false hi3]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hiv : sint.Z iv = sint.Z sl.len := by omega
        have hCB : C = B := by
          rw [← hC]
          by_cases h0 : sint.Z iv = 0
          · rw [if_pos h0]
            have hnil : gs.map cmdOf = [] := by
              have h1 := Hsllen.1
              have h2 : gs.length = 0 := by word
              simp [List.length_eq_zero_iff.1 h2]
            unfold uaG at hGn; rw [if_pos (Or.inr hnil)] at hGn; exact Option.some.inj hGn
          · rw [if_neg h0]
        wp_for_post
        iframe
        iexists (qv + W64 1)
        rw [hn1, hB, ← hCB]
        iframe; ipureintro; word
  · have hq3 : ¬ sint.Z qv < sint.Z (W64 3) := fun h' => Hif (by rw [decide_eq_true h'])
    rw [decide_eq_false hq3]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hqv : (sint.Z qv).toNat = 3 := by word
    rw [hqv]
    simp only [stq]
    wp_auto
    ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
    ihave II : iprop(∃ iv : w64, i_ptr ↦ iv ∗
        seq_ptr ↦ (if sint.Z iv = 0 then st3 else uaM s st3).1 ∗
        changed_ptr ↦ (if sint.Z iv = 0 then st3 else uaM s st3).2.2 ∗
        ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z sl.len⌝) $$ [i seq changed]
    · iexists W64 0; iframe; ipureintro; word
    wp_for II
    icases II with ⟨i, seq, changed, %Hi⟩
    generalize hC : (if sint.Z iv = 0 then st3 else uaM s st3) = C
    have hCM : uaM s C = uaM s st3 := by
      rw [← hC]; split
      · rfl
      · exact model.uaM_idem s st3
    have hCd : C.2.1 = st3.2.1 := by
      rw [← hC]; split
      · rfl
      · unfold uaM; cases s.maxSeqK0 <;> simp only; split <;> rfl
    wp_auto
    wp_if_destruct
    · have hilt : sint.Z iv < sint.Z sl.len := by simpa using go.intoVal_inj Hif
      obtain ⟨c, hc⟩ : ∃ c, gs[(sint.Z iv).toNat]? = some c :=
        ⟨_, List.getElem?_eq_getElem (by have := Hsllen.1; word)⟩
      have hcok : c.K' = W64 0 ∧ c.Op' = W8 6 := by
        have := hcs
        simp only [model.cmdsOk, List.all_eq_true, List.mem_map] at this
        have h1 := this (cmdOf c) ⟨c, List.mem_of_getElem? hc, rfl⟩
        simp [model.Cmd.ok, cmdOf, model.opCAS] at h1
        exact ⟨h1.2, h1.1⟩
      have hib : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z sl.len := ⟨Hi.1, hilt⟩
      have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [ite_eq_left hib]
      icases ownSlice_elem_acc (sint.Z iv) c sl DFrac.discard gs hib.1 hc $$ Hsl with ⟨#Hc0, -⟩
      iStructNamed Hc0
      wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
      rw [hcok.1]
      icases (confRepS_open ..).1 $$ Hms with ⟨%m1, Hm1, %Hm1o, Hc⟩
      wp_apply (wp_map_lookup2 _ _ msR m1 (W64 0) (DFrac.own 1)) $$ [$Hm1] as Hm1
      cases hcv : s.maxSeqK0 with
      | none =>
        icases Hc with %Hn
        rw [Hn]
        wp_auto
        wp_for_post
        have hCB : uaM s C = C := by unfold uaM; rw [hcv]
        ihave Hms : confRepS msR none $$ [Hm1]
        · iapply (confRepS_open ..).2; iexists m1; iframe; ipureintro; exact ⟨Hm1o, Hn⟩
        iframe
        iexists (iv + W64 1)
        rw [hiv1, if_neg (by omega), ← hCM, hCB]
        iframe; ipureintro; word
      | some v =>
        icases Hc with ⟨%ir, %im, %Hir, Him, %Himp⟩
        rw [Hir]
        simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
        wp_auto
        rw [ite_eq_left hib]
        wp_apply (IntoValTyped.wp_load (t := src.state.Operation.ty) _ _ _) $$ [$Op] as -
        rw [hcok.2]
        wp_apply (wp_map_lookup2 _ _ ir im (W8 6) (DFrac.own 1)) $$ [$Him] as Him
        have him6 : im.lookup (W8 6) = some v := by
          rw [Himp]; simp (config := {decide := true}) [opsAll]
        rw [him6]
        simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
        wp_auto
        ihave Hms : confRepS msR (some v) $$ [Hm1 Him]
        · iapply (confRepS_open ..).2
          iexists m1; iframe
          isplitr
          · ipureintro; exact Hm1o
          · iexists ir, im; iframe; ipureintro; exact ⟨Hir, Himp⟩
        wp_if_destruct
        · wp_for_post
          have hCB : uaM s C = (v + 1, C.2.1, true) := by
            unfold uaM; rw [hcv]; dsimp only
            rw [if_pos (by simp only [model.sle, decide_eq_true_eq]; exact Hif)]
          iframe
          iexists (iv + W64 1)
          rw [hiv1, if_neg (by omega), ← hCM, hCB]
          iframe; ipureintro; word
        · wp_for_post
          have hCB : uaM s C = C := by
            unfold uaM; rw [hcv]; dsimp only
            rw [if_neg (by simp only [model.sle, decide_eq_true_eq]; exact Hif)]
          iframe
          iexists (iv + W64 1)
          rw [hiv1, if_neg (by omega), ← hCM, hCB]
          iframe; ipureintro; word
    · have hi3 : ¬ sint.Z iv < sint.Z sl.len := fun h' => Hif (by rw [decide_eq_true h'])
      rw [decide_eq_false hi3]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hiv : sint.Z iv = sint.Z sl.len := by omega
      have hCH : C = uaH s (gs.map cmdOf) st3 := by
        rw [← hC]; unfold uaH
        by_cases h0 : sint.Z iv = 0
        · have hnil : gs.map cmdOf = [] := by
            have h1 := Hsllen.1
            have h2 : gs.length = 0 := by word
            simp [List.length_eq_zero_iff.1 h2]
          rw [if_pos h0, if_pos hnil]
        · have hnil : gs.map cmdOf ≠ [] := by
            intro h0'; apply h0; have h1 := Hsllen.1
            simp at h0'; subst h0'; simp at h1; word
          rw [if_neg h0, if_neg hnil]
      wp_auto
      have hcfs : cfs.length = 3 := Hf.2.1
      have hrn : (sint.Z replica).toNat < 3 := by omega
      obtain ⟨cr, hcr⟩ : ∃ cr, cfs[(sint.Z replica).toNat]? = some cr :=
        ⟨_, List.getElem?_eq_getElem (by rw [hcfs]; omega)⟩
      ihave %Hcfslen := ownSlice_len _ _ _ $$ Hcfs
      have hqw : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
      have hrb : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z c1S.len := by
        rw [hqw]; have := Hcfslen.1; rw [hcfs] at this; word
      rw [ite_eq_left hrb]
      wp_apply wp_load_slice_index (t := go.GoType.MapType src.state.Key.ty
          (go.GoType.MapType src.state.Operation.ty go.int32)) c1S (sint.Z (W64 (sint.Z replica)))
          cfs _ cr hrb.1 $$ [$Hcfs] as -
      · ipureintro; rw [hqw]; exact hcr
      icases (BigSepL.bigSepL_lookup_acc_impl (Φ := fun q cr => confRepS cr (s.confAt q)) hcr)
        $$ Hconfs with ⟨Hc, Hcclose⟩
      icases (confRepS_open ..).1 $$ Hc with ⟨%m1, Hm1, %Hm1o, Hc⟩
      wp_apply (wp_map_len (V := Loc) cr m1 (DFrac.own 1)) $$ [$Hm1] as Hm1
      wp_apply (StatsMap.Max.wp _ go!"conflicts_map_size" _
        (by left; simp only [statsIntKeys]; decide)) $$ [$Hsok] as %nn - -- H1-R5
      ihave Hc := (confRepS_open ..).2 $$ [Hm1 Hc]
      · iexists m1; iframe; ipureintro; exact Hm1o
      ihave Hconfs := Hcclose $$ %(fun q cr => confRep cr (s.confAt q)) [] [Hc]
      · iintro !> %k %y %_ %_ H; dsimp only; iapply (confRep_S ..).2 $$ H
      · dsimp only; iapply (confRep_S ..).2 $$ Hc
      icases (confRep_S ..).2 $$ Hms with Hms
      iapply HΦ
      isplitl
      · simp only [epaxosOwnAt]
        iframe # ∗
        ipureintro; exact Hf
      · ipureintro
        rw [← hCH, ← hCd]
        rfl

/-- `updateAttributes(cmds, seq, deps, replica, instance)` (the statement of `H2/Attr.lean`). -/
theorem wp_updateAttributes' (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) (xs : XS) (s : RState)
    (sl : GoSlice) (gs : List src.state.Command) (seq : w32) (deps : GoArray w32 5)
    (replica inst : w32) (res : w32 × Deps × Bool)
    (hcs : model.cmdsOk (gs.map cmdOf) = true) (hrep : 0 ≤ sint.Z replica ∧ sint.Z replica < 3)
    (hid : s.id = rid32 k)
    (hres : model.updateAttributes s (gs.map cmdOf) seq (depsOf deps) replica = some res) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ attrEnv k r gR h ∗
        epaxosOwn ρ h r xs s ∗ sl ↦*□ gs }}
      (App (App (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"updateAttributes")) (Val #sl)) (Val #seq)) (Val #deps)) (Val #replica)) (Val #inst))
    {{ (seq' : w32) (deps' : GoArray w32 5) (ch : Bool), RET (PairV (PairV #seq' #deps') #ch);
        epaxosOwn ρ h r xs s ∗ ⌜res = (seq', depsOf deps', ch)⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hae, Hep, #Hsl⟩ HΦ
  icases (epaxosOwn_at ..).1 $$ Hep with ⟨%W, Hep⟩
  wp_apply (wp_updateAttributes_at ρ k r gR h xs s W sl gs seq deps replica inst res hcs hrep hid hres)
    $$ [$Hep] as %seq' %deps' %ch ⟨Hep, %Hr⟩
  · iframe #
  iapply HΦ
  iframe
  isplitl
  · iapply (epaxosOwn_at ..).2; iexists W; iexact Hep
  · ipureintro; exact Hr

end

end Perennial.gryff.replica2
