/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/SC.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: `Exec.strongconnect` over the stage-2 lock (generic `GF`)

Stage 1's proof (`Replica/ExecSC.lean`) over the model state: the lock's contents are
`ExecLaws.LA t xs` (the trace `t`, the search state `xs`); a release of the lock (the waits)
moves the trace forward with the committed copies stable (`th_relock`); a popped component is
executed member by member (`resolveExec`, `critical_step` with the guard from `execGuard_of`, the
`PrevValTag` update, the `ExecuteOverwrite` sent with its token, `Status = EXECUTED`).
-/
module

public import Dsverify.Proof.gryff.X.Access
public import Dsverify.Proof.gryff.X.Tag
public import Dsverify.Proof.gryff.X.Sort
public import Dsverify.Proof.gryff.Replica.ExecDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out committedCopy executedB inBox depR execGuard)
open Perennial.gryff.replica (XS Node TInv LInv Post TState XClosed sccStep stackOwn euOwn keyLt
  stackOwn_open euOwn_open stackElems stackOwn_intro stackElems_push rowOwn rowOwn_open rows_acc
  wp_load_inst_dep wp_dlog_Printf wp_Time_IsZero)
open Perennial.gryff.replica2 (Repl2Names rid32 handlerIface scFacts2)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

/-- `scFacts2` without its last conjunct (the executed set's closure, H-X-2 (a)). -/
def scFacts2X (s : RState) (xs : XS) (S : List Node) (idx : Nat) : Prop :=
  (∀ u, u ∈ S ∨ u ∈ xs.1 → (committedCopy s u).isSome) ∧
    (∀ n, n ∈ xs.1 ↔ executedB s n = true) ∧
    ∃ vis : List Node, vis.Nodup ∧ vis.length + 1 = idx ∧
      (∀ n ∈ vis, xs.numF n ≠ 0 ∧ replica.inBox n) ∧ ∀ u ∈ S, u ∈ vis

/-- The search's facts and the executed instances' closure under the dependencies: `scFacts2`
(since H-X-2 (a)), split. -/
def SCF (s : RState) (xs : XS) (S : List Node) (idx : Nat) : Prop :=
  scFacts2X s xs S idx ∧ XClosed (depR s) xs.1

theorem SCF_eq (s : RState) (xs : XS) (S : List Node) (idx : Nat) :
    SCF s xs S idx = scFacts2 s xs S idx := rfl

/-- The search state after the first `j` members of a popped component `Ls` are executed. -/
def xsJ (xs : XS) (Ls : List Node) (j : Nat) : XS := (xs.1 ++ Ls.take j, xs.2.1, xs.2.2)

theorem xsJ_zero (xs : XS) (Ls : List Node) : xsJ xs Ls 0 = xs := by
  simp [xsJ]

theorem SCF.stable {s s' : RState} (hs : Stable s s') {xs : XS} {S : List Node} {idx : Nat}
    (hex : ∀ n, n ∈ xs.1 ↔ executedB s' n = true) (h : SCF s xs S idx) : SCF s' xs S idx := by
  obtain ⟨⟨h1, -, h3⟩, h4⟩ := h
  exact ⟨⟨fun u hu => hs.isSome (h1 u hu), hex, h3⟩,
    XClosed.stable hs (fun u hu => h1 u (.inr hu)) h4⟩

theorem SCF.setLow {s : RState} {xs : XS} {S : List Node} {idx : Nat} (n : Node) (b : Nat)
    (h : SCF s xs S idx) : SCF s (xs.setLow n b) S idx := by
  obtain ⟨⟨h1, h2, vis, h3, h4, h5, h6⟩, h7⟩ := h
  exact ⟨⟨h1, h2, vis, h3, h4, fun n hn => by rw [XS.numF_setLow]; exact h5 n hn, h6⟩, h7⟩

theorem SCF_idx {s xs S idx} (h : SCF s xs S idx) (hS : S.Nodup) :
    0 < idx ∧ idx ≤ 3 * (2 * 1024 * 1024) + 1 ∧ S.length + 1 ≤ idx := by
  obtain ⟨⟨-, -, vis, hnd, hlen, hb, hSv⟩, -⟩ := h
  have h1 := replica.box_nodup_length hnd (fun n hn => (hb n hn).2)
  have h2 := (List.subperm_of_subset hS hSv).length_le
  omega

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

/-- The search's resources with the lock held (stage 1's `scState`). -/
def ExecLaws.St (L : ExecLaws (GF := GF) k ρ r h p) (mtx idxp : Loc) (t : List Ev) (xs : XS)
    (S : List Node) (idx : Nat) : IProp GF :=
  iprop(sync.ownMutex mtx ∗ L.LA t xs ∗ execPrivG ρ h xs S ∗ idxp ↦ W64 (idx : Int))

theorem ExecLaws.St_open (L : ExecLaws (GF := GF) k ρ r h p) (mtx idxp : Loc) (t : List Ev)
    (xs : XS) (S : List Node) (idx : Nat) :
    L.St mtx idxp t xs S idx ⊣⊢
      sync.ownMutex mtx ∗ L.LA t xs ∗ execPrivG ρ h xs S ∗ idxp ↦ W64 (idx : Int) := .rfl

end

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : src.gryff.Assumptions]
variable [time_sem : time.Assumptions]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

set_option goose.wp.extras true

set_option hygiene false in
/-- Open the search's resources (`St`) with the instance space's slices the persistent ones in
context (`HIS`, `Hisp`). -/
macro "open_st" : tactic => `(tactic| (
  icases (ExecLaws.St_open ..).1 $$ St with ⟨Hown, HLA, Hpriv, Hidx⟩;
  icases (ExecLaws.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩;
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS', %crtS', %c1S', %isp', %msR', %pvtR',
    %cfs', %M', %cu', %pm', #HhR', #HnoC', #HIS', #Hisp', #Hcrt', #Hc1', #Hc1s', #Hms',
    #Hpvt', Hcu', Hcrtv', HM', HMe', Hrows', Hinsts', Hmono', Hconfs', Hconf', Hpm', Hrst',
    %Hep'⟩;
  icombine HIS HIS' gives %HISe;
  subst HISe;
  ihave %Hispe := ownSlice_agree _ _ _ _ _ $$ Hisp Hisp';
  subst Hispe))

set_option hygiene false in
/-- Close what `open_st` opened (nothing changed). -/
macro "close_st" : tactic => `(tactic| (
  iapply (ExecLaws.St_open ..).2;
  iframe Hown Hidx Hpriv;
  iapply (ExecLaws.LA_open ..).2; iframe;
  iapply (epaxosOwnG_open ..).2;
  iexists _, crtS', c1S', _, msR', pvtR', cfs', M', cu', pm';
  iframe; iframe #; ipureintro; exact Hep'))

set_option maxHeartbeats 8000000 in
/-- `strongconnect(v, index)` (generic `GF`, internal: with `SCF`). -/
theorem wp_sc (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) (t : List Ev) (xs : XS)
    (S : List Node) (idx : Nat) (G : List Node) (vn : Node) (v idxp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ L.isExecG gR mtx ex ∗
        sync.ownMutex mtx ∗ L.LA t xs ∗ execPrivG ρ h xs S ∗ idxp ↦ W64 (idx : Int) ∗
        ghostMapElem ρ.ptrs vn DFrac.discard v ∗
        ⌜TInv (depR (stOf k t)) (xs.toT S idx) G ∧ vn ∉ xs.1 ∧ xs.numF vn = 0 ∧
          (committedCopy (stOf k t) vn).isSome ∧ SCF (stOf k t) xs S idx⌝ }}
      (App (App (Val (ex @!! go.GoType.PointerType src.gryff.Exec.ty @!! go!"strongconnect"))
        (Val #v)) (Val #idxp))
    {{ RET #true; ∃ (t' : List Ev) (xs' : XS) (S' : List Node) (idx' : Nat),
        sync.ownMutex mtx ∗ L.LA t' xs' ∗ execPrivG ρ h xs' S' ∗ idxp ↦ W64 (idx' : Int) ∗
        ⌜t <+: t' ∧ Post (depR (stOf k t')) (xs.toT S idx) G vn (xs'.toT S' idx') ∧
          SCF (stOf k t') xs' S' idx'⌝ }} := by
  iintro %Φ Hpre HΦ
  iloeb as IH generalizing %t %xs %S %idx %G %vn %v %Φ Hpre HΦ
  icases Hpre with ⟨#Hpkg, #Hfix, Hown, HLA, Hpriv, Hidx, #Hv, %Hpre⟩
  wp_method_call
  wp_call
  icases (L.isExecG_open ..).1 $$ Hfix with ⟨#Hr, #Hh, #Hm, #Hpp, #HR, #Hex, #Hexr, #HId, #HN,
    #HSd, #Hlock, #Heo, #Hrec, #HInv, #Hdlog⟩
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  ihave ⟨HEP, %Hok⟩ := epaxosOwnG_ok ρ h r xs (stOf k t) $$ HEP
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
  icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS, #HeuS, Heu⟩
  ihave %HvM := ghost_map_lookup $$ HM Hv
  icases instsG_upd ρ xs (stOf k t) M vn v HvM $$ Hinsts with ⟨⟨%cv, %Hcv, Hvi⟩, Hclose⟩
  icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv, Hvp, Hvcmds, Hvlb, %Hiv⟩
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf $$ [$Hdlog]
  ihave HTH := L.th_deps t $$ [HTH]
  · iframe; iframe #
  imod HTH with ⟨HTH, %Hdeps⟩
  ihave HTH := L.th_lb t $$ HTH
  imod HTH with ⟨HTH, #HTLb⟩
  obtain ⟨hTI, hvX, hvn, hvc, hF⟩ := Hpre
  obtain ⟨av, hav⟩ := Option.isSome_iff_exists.1 hvc
  have hcvav : cv = av := by
    have := (committedCopy_inst hav).1; rw [Hcv] at this; cases this; rfl
  subst hcvav
  icases (stackOwn_open ..).1 $$ Hstk with ⟨%s, %sptrs, Hsg, Hs, Hscap, %Hsf, #HSe⟩
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  ihave %Hscapwf := ownSliceCap_wf _ _ $$ Hscap
  wp_auto
  have hidx := SCF_idx hF hTI.nodup
  wp_join iprop(∃ s' : GoSlice, globalAddr src.gryff.stack ↦ s' ∗ s' ↦* sptrs ∗
      ownSliceCap Loc s' (DFrac.own 1) ∗ l_ptr ↦ s.len ∗
      ⌜sint.Z s'.len = (S.length : Int) ∧ (S.length : Int) < sint.Z s'.cap ∧
        sint.Z s'.cap < 2 ^ 60⌝) with [Hsg Hs Hscap l] as ⟨%s1, Hsg, Hs, Hscap, l, %Hs1⟩
  · wp_apply wp_slice_make3 (V := Loc) (t := go.GoType.PointerType src.gryff.Instance.ty) s.len (W64 2 * s.len) (by word) as %ns ⟨Hns, Hnscap, %Hnscapeq⟩
    wp_apply wp_slice_copy (t := go.GoType.PointerType src.gryff.Instance.ty) ns _ s sptrs (DFrac.own 1) $$ [$Hns $Hs] as %n ⟨%Hn, Hns, Hs⟩
    wp_join_done
    have heq : sptrs.take (List.replicate (sint.nat s.len) (zero_val Loc)).length ++
        (List.replicate (sint.nat s.len) (zero_val Loc)).drop sptrs.length = sptrs := by
      rw [List.length_replicate, ← Hslen.1, List.take_length, List.drop_replicate, Nat.sub_self,
        List.replicate_zero, List.append_nil]
    rw [heq]
    ihave %Hnslen := ownSlice_len _ _ _ $$ Hns
    iexists ns
    iframe
    ipureintro
    rw [Hnscapeq]
    have := Hnslen.1; have := Hsf.1
    refine ⟨by word, ?_, ?_⟩ <;> word
  · iexists s
    iframe
    ipureintro
    have := Hsf.1; have := Hslen.1
    have hne : sint.Z s.len ≠ sint.Z s.cap := fun h => Hif (by word)
    refine ⟨by word, by word, by word⟩
  have hl1 : sint.Z (s.len + W64 1) = (S.length : Int) + 1 := by have := Hsf.1; word
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (s.len + W64 1) ∧
    sint.Z (s.len + W64 1) ≤ sint.Z s1.cap by rw [hl1]; word)]
  icases ownSlice_slice_into_capacity (W64 0) (s.len + W64 1) s1 sptrs $$ [Hs Hscap]
    with ⟨%vcap, -, Hs, Hscap⟩
  · iframe; ipureintro; rw [hl1]; refine ⟨by word, by word, by word, by word⟩
  ihave %Hs2len := ownSlice_len _ _ _ $$ Hs
  have hslen' : sint.Z s.len = (S.length : Int) := by have := Hsf.1; word
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z s.len ∧ sint.Z s.len < sint.Z (s.len + W64 1 - W64 0) by
    rw [show s.len + W64 1 - W64 0 = s.len + W64 1 by word, hl1]; omega)]
  wp_apply wp_store_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) _ (sint.Z s.len)
    _ v $$ [$Hs] as Hs
  · ipureintro
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, slice.slice] at Hs2len ⊢
    constructor <;> word
  have hvcap : vcap.length = 1 := by
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, slice.slice,
      List.length_append] at Hs2len
    have := Hsf.1; word
  have hps : (List.drop 0 (sptrs ++ vcap)).set (sint.Z s.len).toNat v = sptrs ++ [v] := by
    obtain ⟨x, rfl⟩ : ∃ x, vcap = [x] := by
      match vcap, hvcap with | [x], _ => exact ⟨x, rfl⟩
    rw [List.drop_zero, show (sint.Z s.len).toNat = sptrs.length by have := Hsf.1; omega,
      List.set_append_right _ _ (by omega), Nat.sub_self]; rfl
  rw [hps]
  -- the search has visited `vn`: the ghost state, the instance, the stack
  imod ghostVar_update_halves (xs.setNL vn idx idx) ρ.xs xs xs $$ Hxs Hxs1 with ⟨Hxs, Hxs1⟩
  ihave Hinsts := Hclose $$ %(xs.setNL vn idx idx) %(stOf k t) [] [] [Hvp Hvcmds Hvlb]
  · ipureintro; intro n hn
    have hn' : vn ≠ n := fun e => hn e.symm
    rw [XS.numF_setNL, XS.lowF_setNL]; simp [hn', XS.setNL]
  · ipureintro; intro _ _ _; rfl
  · iexists cv
    isplitr
    · ipureintro; exact Hcv
    iapply (copyRepG_open ..).2
    iexists _
    iframe Hvp Hvcmds Hvlb
    ipureintro
    have hidxw : sint.Z (W64 (idx : Int)) = (idx : Int) := by
      have := hidx.2.1; word
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, -, a13⟩ := Hiv
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ?_, ?_, a13⟩ <;>
      simp only [XS.numF_setNL, XS.lowF_setNL, ite_true] <;> exact hidxw
  -- the search's state after the visit
  have hL0 : LInv (depR (stOf k t)) (xs.toT S idx) G vn (fun w => 0 ≤ w.1 ∧ w.1 < sint.Z (W32 0))
      ((xs.setNL vn idx idx).toT (S ++ [vn]) (idx + 1)) := by
    have := LInv.init hTI vn hvX hvn hidx.1
    rw [XS.visit_toT] at this
    exact this.done_mono (fun w _ hw => by simp at hw; omega)
  have hF0 : SCF (stOf k t) (xs.setNL vn idx idx) (S ++ [vn]) (idx + 1) := by
    obtain ⟨⟨hC, hex, vis, hnd, hlen, hb, hSv⟩, hXc⟩ := hF
    have hvnvis : vn ∉ vis := fun hv => (hb vn hv).1 hvn
    refine ⟨⟨?_, hex, vis ++ [vn], ?_, by simp; omega, ?_, ?_⟩, hXc⟩
    · intro u hu
      rcases hu with hu | hu
      · rcases List.mem_append.1 hu with hu | hu
        · exact hC u (.inl hu)
        · simp at hu; subst hu; exact hvc
      · exact hC u (.inr hu)
    · refine List.nodup_append.2 ⟨hnd, by simp, fun a ha b hb e => ?_⟩
      simp at hb; subst hb; subst e; exact hvnvis ha
    · intro n hn
      rcases List.mem_append.1 hn with hn | hn
      · have hnv : vn ≠ n := fun e => hvnvis (e ▸ hn)
        rw [XS.numF_setNL]; simp only [hnv, ite_false]; exact hb n hn
      · simp at hn; subst hn
        rw [XS.numF_setNL]; simp only [ite_true]
        exact ⟨by omega, committedCopy_box hvc⟩
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact List.mem_append_left _ (hSv u hu)
      · exact List.mem_append_right _ hu
  ihave HI : (∃ (q : w32) (tc : List Ev) (xsc : XS) (Sc : List Node) (idxc : Nat),
      "q" ∷ q_ptr ↦ q ∗
      "St" ∷ L.St mtx idxp tc xsc Sc idxc ∗
      "%HL" ∷ ⌜0 ≤ sint.Z q ∧ sint.Z q ≤ 3 ∧
        LInv (depR (stOf k tc)) (xs.toT S idx) G vn (fun w => 0 ≤ w.1 ∧ w.1 < sint.Z q)
          (xsc.toT Sc idxc) ∧
        t <+: tc ∧ Stable (stOf k t) (stOf k tc) ∧ SCF (stOf k tc) xsc Sc idxc⌝ : IProp GF)
    $$ [q Hown HTH HPr HRs HPO HBt Hcu Hcrtv HM HMe Hrows Hinsts Hmono Hconfs Hconf Hpm Hrst Hxs
      Hxs1 Heu Hidx Hsg Hs Hscap]
  · iexists (W32 0), t, (xs.setNL vn idx idx), (S ++ [vn]), (idx + 1)
    iframe q
    isplitl
    · iapply (L.St_open ..).2
      iframe Hown
      isplitl [HTH HPr HRs HPO HBt Hcu Hcrtv HM HMe Hrows Hinsts Hmono Hconfs Hconf Hpm Hrst Hxs1]
      · iapply (L.LA_open ..).2
        iframe
        iapply (epaxosOwnG_open ..).2
        iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
        iframe; iframe #
        ipureintro
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := Hep
        refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, ?_, ?_, e11⟩
        · intro n hn
          by_cases hnv : n = vn
          · subst hnv; rw [HvM]; rfl
          · have hvn' : vn ≠ n := fun e => hnv e.symm
            rw [XS.numF_setNL, XS.lowF_setNL] at hn; simp only [hvn', ite_false] at hn
            exact e9 n hn
        · intro n hn
          by_cases hnv : n = vn
          · subst hnv; exact hvc
          · have hvn' : vn ≠ n := fun e => hnv e.symm
            rw [XS.numF_setNL, XS.lowF_setNL] at hn; simp only [hvn', ite_false] at hn
            exact e10 n hn
      isplitl [Hxs Heu Hsg Hs Hscap]
      · iapply (execPrivG_open ..).2
        rw [show (xs.setNL vn idx idx).1 = xs.1 from rfl]
        iframe Hxs
        isplitl [Hsg Hs Hscap]
        · iapply stackOwn_intro ρ.toR1 (S ++ [vn]) (slice.slice s1 Loc (W64 0) (s.len + W64 1)) (sptrs ++ [v]) (by rw [List.length_append, List.length_append, Hsf.1]; rfl)
            (by simp only [slice.slice]; constructor <;> word)
          iframe
          iapply stackElems_push ρ.toR1 S sptrs vn v Hsf.1
          rw [show ρ.toR1.ptrs = ρ.ptrs from rfl]
          iframe #
        iexists euS; iframe; iframe #
      have hidxw : W64 (idx : Int) + W64 1 = W64 ((idx + 1 : Nat) : Int) := by
        have := hidx.2.1; word
      rw [hidxw]
      iframe Hidx
    · ipureintro
      exact ⟨by decide, by decide, hL0, List.prefix_refl _, Stable.refl _, hF0⟩
  wp_for HI
  wp_if_destruct
  · -- an iteration of the replicas' loop: replica `q`'s dependencies
    obtain ⟨hq0, -, hJL0, htc0, hstc0, hJF0⟩ := HL
    have hq3 : 0 ≤ sint.Z q ∧ sint.Z q < 3 := ⟨hq0, by
      have : sint.Z (W32 (sint.Z (W64 3))) = 3 := by word
      have := Hif; omega⟩
    have hqw : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
    icases (L.St_open ..).1 $$ St with ⟨Hown, HLA, Hpriv, Hidx⟩
    icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
    icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
      %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
      Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
    icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS, #HeuS, Heu⟩
    ihave %HvM := ghost_map_lookup $$ HM Hv
    icases instsG_upd ρ xsc (stOf k tc) M vn v HvM $$ Hinsts with ⟨⟨%cq, %Hcq, Hvi⟩, Hclose⟩
    icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv, Hvp, Hvcmds, Hvlb, %Hiv⟩
    ihave ⟨Hvp, %Hdl⟩ := inst_deps_len v iv $$ Hvp
    obtain ⟨cq', hcq', -, -, hdeps', -⟩ := hstc0 vn cv hav
    have hcqe : cq = cq' := by
      have := (committedCopy_inst hcq').1; rw [Hcq] at this; cases this; rfl
    subst hcqe
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < 5 by
      rw [hqw]; omega)]
    obtain ⟨d, hd⟩ : ∃ d, iv.Deps'.arr[(sint.Z (W64 (sint.Z q))).toNat]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by rw [hqw, Hdl]; omega)⟩
    wp_apply wp_load_inst_dep v iv _ d (by rw [hqw]; omega) hd $$ [$Hvp] as Hvp
    icases (euOwn_open ..).1 $$ Heu with ⟨%euv, Heus, %Heuf⟩
    ihave %Heulen := ownSlice_len _ _ _ $$ Heus
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z euS.len by
      rw [hqw]; have := Heuf.1; have := Heulen.1; simp only [sint.nat, sint.Z] at *; omega)]
    obtain ⟨eq, heq⟩ : ∃ e, euv[(sint.Z (W64 (sint.Z q))).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [hqw, Heuf.1]; omega)⟩
    wp_apply wp_load_slice_index (t := go.int32) euS _ euv _ eq (by rw [hqw]; omega) $$ [$Heus]
      as Heus
    · ipureintro; exact heq
    -- row `q` of the instance space (its slice is fixed)
    ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
    have hqn : (sint.Z (W64 (sint.Z q))).toNat < isp.length := by rw [hqw, Hep.1]; omega
    obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z (W64 (sint.Z q))).toNat]? = some sq :=
      ⟨_, List.getElem?_eq_getElem hqn⟩
    have hql : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z ispS.len := by
      rw [hqw]; have := HispSlen.1; rw [Hep.1] at this; have h3 := hq3
      simp only [sint.nat, sint.Z] at this h3 ⊢; omega
    icases rows_acc M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
    icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs0, Hrow, %Hrowf0⟩
    ihave %Hrowlen0 := ownSlice_len _ _ _ $$ Hrow
    have hsqlen : sint.Z sq.len = 2 * 1024 * 1024 := by
      have := Hrowlen0.1; rw [Hrowf0.1] at this; unfold replica.nSlots at this
      have := Hrowlen0.2; simp only [sint.nat, sint.Z] at *; omega
    ihave Hrows := Hrows $$ [Hrow]
    · iapply (rowOwn_open ..).2; iexists ptrs0; iframe; ipureintro; exact Hrowf0
    -- close `v`'s instance and the lock's contents
    ihave Hinsts := Hclose $$ %xsc %(stOf k tc) [] [] [Hvp Hvcmds Hvlb]
    · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
    · ipureintro; intro _ _ _; rfl
    · iexists cq; isplitr; · ipureintro; exact Hcq
      iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiv
    -- `eq`, replica `q`'s `ExecedUpTo`: the instances up to it are executed
    have heqf := Heuf.2 (sint.Z (W64 (sint.Z q))).toNat eq heq
    have heqlt : sint.Z eq < 2 * 1024 * 1024 := by
      apply Int.lt_of_not_ge; intro hc
      have hX := heqf.2 (sint.Z eq) (by omega) (Int.le_refl _)
      have := committedCopy_box (hJF0.1.1 _ (.inr hX))
      obtain ⟨-, -, -, h4⟩ := this
      omega
    have heq1 : sint.Z (eq + W32 1) = sint.Z eq + 1 := by word
    have hdv : sint.Z d = sint.Z (cv.deps.at (sint.Z q).toNat) := by
      have hd' := hd
      rw [hqw] at hd'
      rw [← hdeps', ← Hiv.2.2.2.1]
      simp only [model.Deps.at, replica2.depsOf, List.getD_eq_getElem?_getD, hd', Option.getD_some]
    have hdlt : sint.Z d < model.SLOTS := by
      rw [hdv]; exact (Hdeps.1 vn cv hav).1 _ (by omega)
    ihave HJ : (∃ (i : w32) (tc' : List Ev) (xsc' : XS) (Sc' : List Node) (idxc' : Nat),
        "i" ∷ i_ptr ↦ i ∗
        "St" ∷ L.St mtx idxp tc' xsc' Sc' idxc' ∗
        "%HJ" ∷ ⌜sint.Z eq + 1 ≤ sint.Z i ∧ (sint.Z i ≤ sint.Z d + 1 ∨ sint.Z i = sint.Z eq + 1) ∧
          LInv (depR (stOf k tc')) (xs.toT S idx) G vn
            (fun w => (0 ≤ w.1 ∧ w.1 < sint.Z q) ∨ (w.1 = sint.Z q ∧ w.2 < sint.Z i))
            (xsc'.toT Sc' idxc') ∧
          t <+: tc' ∧ Stable (stOf k t) (stOf k tc') ∧ SCF (stOf k tc') xsc' Sc' idxc'⌝ : IProp GF)
      $$ [i Hown HTH HPr HRs Hxs1 HPO HBt Hcu Hcrtv HM HMe Hrows Hinsts Hmono Hconfs Hconf Hpm Hrst
        Hxs Hstk Heus Hidx]
    · iexists (eq + W32 1), tc, xsc, Sc, idxc
      iframe i
      isplitl
      · iapply (L.St_open ..).2
        iframe Hown Hidx
        isplitl [HTH HPr HRs Hxs1 HPO HBt Hcu Hcrtv HM HMe Hrows Hinsts Hmono Hconfs Hconf Hpm Hrst]
        · iapply (L.LA_open ..).2; iframe
          iapply (epaxosOwnG_open ..).2
          iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
          iframe; iframe #; ipureintro; exact Hep
        iapply (execPrivG_open ..).2; iframe
        iexists euS; iframe #
        iapply (euOwn_open ..).2; iexists euv; iframe; ipureintro; exact Heuf
      · ipureintro
        refine ⟨by omega, .inr heq1, ?_, htc0, hstc0, hJF0⟩
        refine hJL0.done_mono (fun w hw hdn => ?_)
        rcases hdn with hdn | ⟨hw1, hw2⟩
        · exact .inl hdn
        · refine .inr ?_
          obtain ⟨_, _, _, _, hw0, _⟩ := hw
          have := heqf.2 w.2 hw0 (by omega)
          have hqn : (((sint.Z (W64 (sint.Z q))).toNat : Nat) : Int) = w.1 := by
            rw [hqw, hw1]; omega
          rw [hqn] at this; exact this
    wp_for HJ
    wp_if_destruct
    · -- an iteration of replica `q`'s instances `i`
      obtain ⟨hJ1, hJ2, hJL, hJt, hJs, hJF⟩ := HJ
      have hid : sint.Z i ≤ sint.Z d := Hif
      have hdepw : depR (stOf k tc') vn (sint.Z q, sint.Z i) := by
        obtain ⟨c2, hc2, -, -, hd2, -⟩ := hJs vn cv hav
        exact ⟨c2, hc2, hq3.1, hq3.2, by omega, by rw [hd2, ← hdv]; exact hid⟩
      have hiq : 0 ≤ sint.Z i ∧ sint.Z i < 2 * 1024 * 1024 := by
        have := heqf.1; unfold model.SLOTS at hdlt; omega
      have hiw : sint.Z (W64 (sint.Z i)) = sint.Z i := by word
      have hil : 0 ≤ sint.Z (W64 (sint.Z i)) ∧ sint.Z (W64 (sint.Z i)) < sint.Z sq.len := by
        rw [hiw, hsqlen]; omega
      -- wait until instance `(q, i)` and the commands are there
      ihave HW : (∃ tw, "St" ∷ L.St mtx idxp tw xsc' Sc' idxc' ∗
          "%HW" ∷ ⌜tc' <+: tw ∧ Stable (stOf k tc') (stOf k tw)⌝ : IProp GF) $$ [St]
      · iexists tc'; iframe; ipureintro; exact ⟨List.prefix_refl _, Stable.refl _⟩
      wp_for HW
      wp_join (Q := fun bv => iprop(∃ b : Bool, ⌜bv = #b⌝ ∗ L.St mtx idxp tw xsc' Sc' idxc' ∗
          i_ptr ↦ i ∗ q_ptr ↦ q ∗ e_ptr ↦ ex ∗ v_ptr ↦ v ∗
          ⌜b = false → ((stOf k tw).inst q i).isSome⌝)) at (if: _ then _ else _) with [St i q e v]
      · open_st
        icases rows_acc M' isp _ sq hsq $$ Hrows' with ⟨Hrow, Hrows'⟩
        icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
        obtain ⟨pw, hp⟩ : ∃ p, ptrs[(sint.Z (W64 (sint.Z i))).toNat]? = some p :=
          ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf.1]; unfold replica.nSlots; omega)⟩
        have hMp := Hrowf.2 _ pw hp
        have hwn : (((sint.Z (W64 (sint.Z q))).toNat : Nat) : Int) = sint.Z q ∧
            (((sint.Z (W64 (sint.Z i))).toNat : Nat) : Int) = sint.Z i := by
          rw [hqw, hiw]; omega
        rw [hwn.1, hwn.2] at hMp
        rw [ite_eq_left hql]
        wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
          ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
        · ipureintro; exact hsq
        rw [ite_eq_left hil]
        wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
          sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
        · ipureintro; exact hp
        wp_if_destruct
        · -- no instance: wait
          ihave Hrows' := Hrows' $$ [Hrow]
          · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
          iexists true
          isplitr; · ipureintro; rfl
          iframe
          isplitl
          · close_st
          ipureintro; intro hf; cases hf
        · -- the instance: its commands
          simp only [Hif, ite_false] at hMp
          rw [ite_eq_left hql]
          wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
            ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
          · ipureintro; exact hsq
          rw [ite_eq_left hil]
          wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
            sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
          · ipureintro; exact hp
          wp_apply wp_insts_load_Cmds ρ _ (stOf k tw) M' (sint.Z q, sint.Z i) pw hMp $$ [$Hinsts']
            as %cs ⟨Hinsts', -⟩
          wp_if_destruct
          · -- no commands: wait
            ihave Hrows' := Hrows' $$ [Hrow]
            · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
            iexists true
            isplitr; · ipureintro; rfl
            iframe
            isplitl
            · close_st
            ipureintro; intro hf; cases hf
          · -- `v`'s commands
            ihave %HvM' := ghost_map_lookup $$ HM' Hv
            wp_apply wp_insts_load_Cmds ρ _ (stOf k tw) M' vn v HvM' $$ [$Hinsts']
              as %cs' ⟨Hinsts', -⟩
            ihave Hrows' := Hrows' $$ [Hrow]
            · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
            have hsome : ((stOf k tw).inst q i).isSome := by
              have := Hep'.2.2.2.2.2.2.1 q i (by
                simp only [inBox, decide_eq_true_eq]; unfold model.SLOTS; omega)
              rw [this, hMp]; rfl
            wp_if_destruct
            · iexists true
              isplitr; · ipureintro; rfl
              iframe
              isplitl
              · close_st
              ipureintro; intro hf; cases hf
            · iexists false
              isplitr; · ipureintro; rfl
              iframe
              isplitl
              · close_st
              ipureintro; intro _; exact hsome
      iintro ⟨%b, %Hb, St, i, q, e, v, %Hbs⟩
      subst Hb
      cases b
      · -- the instance and the commands are there
        have hft : (#false : val) ≠ #true := fun h => absurd (go.intoVal_inj h) (by decide)
        simp only [hft, decide_false, Bool.false_eq_true, ite_false, _root_.decide_true, ite_true]
        have hsome := Hbs rfl
        -- `InstanceSpace[q][i].Status == EXECUTED`: a dependency already executed
        open_st
        ihave ⟨Hinsts', %HNok⟩ := instsG_ok ρ xsc' (stOf k tw) M' $$ Hinsts'
        have Hokw := HeapOk_of _ _ M' HNok Hep'.2.2.2.2.2.2.1 Hep'.2.2.2.2.2.2.2.1
          Hep'.2.2.2.2.2.2.2.2.1
        have hJLw := LInv.stable HW.2 (fun u hu => hJF.1.1 u (.inl hu)) hJL
        have hJFw := SCF.stable HW.2 (fun n => (Hokw.1 n).symm) hJF
        have hdepw' := depR_mono HW.2 hdepw
        icases rows_acc M' isp _ sq hsq $$ Hrows' with ⟨Hrow, Hrows'⟩
        icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
        obtain ⟨pw, hp⟩ : ∃ p, ptrs[(sint.Z (W64 (sint.Z i))).toNat]? = some p :=
          ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf.1]; unfold replica.nSlots; omega)⟩
        have hMp := Hrowf.2 _ pw hp
        have hwn : (((sint.Z (W64 (sint.Z q))).toNat : Nat) : Int) = sint.Z q ∧
            (((sint.Z (W64 (sint.Z i))).toNat : Nat) : Int) = sint.Z i := by
          rw [hqw, hiw]; omega
        rw [hwn.1, hwn.2] at hMp
        have hpnn : pw ≠ Loc.null := by
          intro hpn; rw [if_pos hpn] at hMp
          have := Hep'.2.2.2.2.2.2.1 q i (by
            simp only [inBox, decide_eq_true_eq]; unfold model.SLOTS; omega)
          rw [hsome, hMp] at this; cases this
        rw [if_neg hpnn] at hMp
        wp_auto
        rw [ite_eq_left hql]
        wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
          ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
        · ipureintro; exact hsq
        rw [ite_eq_left hil]
        wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
          sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
        · ipureintro; exact hp
        wp_apply wp_insts_load_Status ρ _ (stOf k tw) M' (sint.Z q, sint.Z i) pw hMp $$ [$Hinsts']
          as %st ⟨Hinsts', %Hst⟩
        ihave Hrows' := Hrows' $$ [Hrow]
        · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
        have hi1 : sint.Z (i + W32 1) = sint.Z i + 1 := by word
        wp_if_destruct
        · -- executed already: the dependency is handled
          have hwX : (sint.Z q, sint.Z i) ∈ xsc'.1 := by
            obtain ⟨c, iv, hc, hf, he⟩ := Hst
            have hcs : c.status = model.St.EXECUTED := by rw [← hf.2.1, ← he]; rfl
            exact hf.2.2.2.2.2.2.2.2.2.2.2.2.1 hcs
          ihave St : L.St mtx idxp tw xsc' Sc' idxc' $$ [Hown Hidx Hpriv HTH HPr HRs Hxs1 HPO HBt
              Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs' Hconf' Hpm' Hrst']
          · close_st
          wp_for_post
          iframe
          iexists (i + W32 1), tw, xsc', Sc', idxc'
          iframe
          ipureintro
          refine ⟨by omega, .inl (by omega), ?_, hJt.trans HW.1, hJs.trans HW.2, hJFw⟩
          rw [hi1]
          refine hJLw.done_mono (fun w _ hd => ?_)
          rcases hd with hd | ⟨hd1, hd2⟩
          · exact .inl (.inl hd)
          · rcases Int.lt_or_eq_of_le (Int.le_of_lt_add_one hd2) with hlt | heqi
            · exact .inl (.inr ⟨hd1, hlt⟩)
            · refine .inr ?_
              have : w = (sint.Z q, sint.Z i) := Prod.ext hd1 heqi
              rw [this]; exact hwX
        · -- not executed: wait until it is committed
          ihave St : L.St mtx idxp tw xsc' Sc' idxc' $$ [Hown Hidx Hpriv HTH HPr HRs Hxs1 HPO HBt
              Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs' Hconf' Hpm' Hrst']
          · close_st
          ihave HW2 : (∃ tw2, "St" ∷ L.St mtx idxp tw2 xsc' Sc' idxc' ∗
              "%HW2" ∷ ⌜tc' <+: tw2 ∧ Stable (stOf k tc') (stOf k tw2) ∧
                ((stOf k tw2).inst q i).isSome⌝ : IProp GF) $$ [St]
          · iexists tw; iframe; ipureintro; exact ⟨hJt.trans HW.1 |>.trans (List.prefix_refl _) |> fun _ => HW.1, HW.2, hsome⟩
          wp_for HW2
          open_st
          icases rows_acc M' isp _ sq hsq $$ Hrows' with ⟨Hrow, Hrows'⟩
          icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
          obtain ⟨pw, hp⟩ : ∃ p, ptrs[(sint.Z (W64 (sint.Z i))).toNat]? = some p :=
            ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf.1]; unfold replica.nSlots; omega)⟩
          have hMp := Hrowf.2 _ pw hp
          rw [hwn.1, hwn.2] at hMp
          have hpnn : pw ≠ Loc.null := by
            intro hpn; rw [if_pos hpn] at hMp
            have := Hep'.2.2.2.2.2.2.1 q i (by
              simp only [inBox, decide_eq_true_eq]; unfold model.SLOTS; omega)
            rw [HW2.2.2, hMp] at this; cases this
          rw [if_neg hpnn] at hMp
          rw [ite_eq_left hql]
          wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
            ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
          · ipureintro; exact hsq
          rw [ite_eq_left hil]
          wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
            sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
          · ipureintro; exact hp
          wp_apply wp_insts_load_Status ρ _ (stOf k tw2) M' (sint.Z q, sint.Z i) pw hMp $$ [$Hinsts']
            as %st2 ⟨Hinsts', %Hst2⟩
          ihave Hrows' := Hrows' $$ [Hrow]
          · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
          ihave St : L.St mtx idxp tw2 xsc' Sc' idxc' $$ [Hown Hidx Hpriv HTH HPr HRs Hxs1 HPO HBt
              Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs' Hconf' Hpm' Hrst']
          · close_st
          by_cases hst4 : st2 = W8 4
          · -- committed: the wait ends
            have hft : (#false : val) ≠ #true := fun h => absurd (go.intoVal_inj h) (by decide)
            simp only [hst4, _root_.decide_true, Bool.not_true, hft, decide_false, Bool.false_eq_true,
              ite_false, ite_true]
            obtain ⟨cw, iw0, hcw, hfw, hstw⟩ := Hst2
            have hcwst : cw.status = model.St.COMMITTED := by rw [← hfw.2.1, ← hstw, hst4]; rfl
            open_st
            ihave ⟨Hinsts', %HNok⟩ := instsG_ok ρ xsc' (stOf k tw2) M' $$ Hinsts'
            have Hokw := HeapOk_of _ _ M' HNok Hep'.2.2.2.2.2.2.1 Hep'.2.2.2.2.2.2.2.1
              Hep'.2.2.2.2.2.2.2.2.1
            have hJLw := LInv.stable HW2.2.1 (fun u hu => hJF.1.1 u (.inl hu)) hJL
            have hJFw := SCF.stable HW2.2.1 (fun n => (Hokw.1 n).symm) hJF
            have hdepw' := depR_mono HW2.2.1 hdepw
            have hqq : BitVec.ofInt 32 (sint.Z q) = q := BitVec.ofInt_toInt
            have hii : BitVec.ofInt 32 (sint.Z i) = i := BitVec.ofInt_toInt
            have hwcc : committedCopy (stOf k tw2) (sint.Z q, sint.Z i) = some cw := by
              unfold committedCopy
              rw [if_pos (show 0 ≤ sint.Z q ∧ sint.Z q < 3 ∧ 0 ≤ sint.Z i ∧ sint.Z i < model.SLOTS from
                ⟨hq3.1, hq3.2, hiq.1, by unfold model.SLOTS; omega⟩)]
              simp only [hqq, hii] at hcw ⊢; rw [hcw]; simp [hcwst]
            have hwX : (sint.Z q, sint.Z i) ∉ xsc'.1 := by
              intro hX; have := (hfw.2.2.2.2.2.2.2.2.2.2.2.2).2 hX; rw [hcwst] at this; cases this
            icases rows_acc M' isp _ sq hsq $$ Hrows' with ⟨Hrow, Hrows'⟩
            icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
            obtain ⟨pw, hp⟩ : ∃ p, ptrs[(sint.Z (W64 (sint.Z i))).toNat]? = some p :=
              ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf.1]; unfold replica.nSlots; omega)⟩
            have hMp := Hrowf.2 _ pw hp
            rw [hwn.1, hwn.2] at hMp
            have hpnn : pw ≠ Loc.null := by
              intro hpn; rw [if_pos hpn] at hMp
              have := Hep'.2.2.2.2.2.2.1 q i (by
                simp only [inBox, decide_eq_true_eq]; unfold model.SLOTS; omega)
              rw [show (stOf k tw2).inst q i = some cw by rw [← hqq, ← hii]; exact hcw, hMp] at this
              cases this
            rw [if_neg hpnn] at hMp
            ihave ⟨HMe', #Hwe⟩ := ptrElems_committed ρ (stOf k tw2) M' _ pw hMp
              (by unfold replica2.committedOrExecuted; rw [hwcc]; rfl) $$ HMe'
            wp_auto
            rw [ite_eq_left hql]
            wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
              ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
            · ipureintro; exact hsq
            rw [ite_eq_left hil]
            wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
              sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
            · ipureintro; exact hp
            ihave Hrows' := Hrows' $$ [Hrow]
            · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
            wp_apply wp_insts_load_Index ρ _ (stOf k tw2) M' (sint.Z q, sint.Z i) pw hMp $$ [$Hinsts']
              as %wx ⟨Hinsts', %Hwx⟩
            have hwnum : sint.Z wx = xsc'.numF (sint.Z q, sint.Z i) := by
              obtain ⟨c3, iv3, hc3, hf3, he3⟩ := Hwx; rw [he3]; exact hf3.2.2.2.2.2.2.2.2.2.2.1
            ihave St : L.St mtx idxp tw2 xsc' Sc' idxc' $$ [Hown Hidx Hpriv HTH HPr HRs Hxs1 HPO HBt
                Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs' Hconf' Hpm' Hrst']
            · close_st
            have hvw : vn ≠ (sint.Z q, sint.Z i) ∨ True := .inr trivial
            wp_if_destruct
            · -- not visited: the recursive call
              have hw0 : xsc'.numF (sint.Z q, sint.Z i) = 0 := by
                have h1 : sint.Z (W64 0) = 0 := rfl
                omega
              icases (L.St_open ..).1 $$ St with ⟨Hown, HLA, Hpriv, Hidx⟩
              imod L.LA_lb tw2 xsc' $$ HLA with ⟨HLA, #HTLb2⟩
              ihave #Hfix' : L.isExecG gR mtx ex $$ []
              · iapply (L.isExecG_open ..).2; iframe #
              wp_method_call
              wp_apply IH $$ [Hown HLA Hpriv Hidx]
              · iframe; iframe #
                ipureintro
                exact ⟨hJLw.inv, hwX, hw0, by rw [hwcc]; rfl, hJFw⟩
              iintro ⟨%t3, %xs3, %S3, %idx3, Hown, HLA, Hpriv, Hidx, %Hpost⟩
              obtain ⟨ht3, hP, hF3⟩ := Hpost
              imod L.LA_stable tw2 t3 xs3 $$ [HInv HLA HTLb2] with ⟨HLA, %Hs3⟩
              · iframe; iframe #
              wp_pures
              icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
              icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS3, %crtS3, %c1S3, %isp3, %msR3,
                %pvtR3, %cfs3, %M3, %cu3, %pm3, #HhR3, #HnoC3, #HIS3, #Hisp3, #Hcrt3, #Hc13, #Hc1s3,
                #Hms3, #Hpvt3, Hcu3, Hcrtv3, HM3, HMe3, Hrows3, Hinsts3, Hmono3, Hconfs3, Hconf3, Hpm3,
                Hrst3, %Hep3⟩
              icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS3, #HeuS3, Heu3⟩
              ihave %HvM3 := ghost_map_lookup $$ HM3 Hv
              ihave %HwM3 := ghost_map_lookup $$ HM3 Hwe
              have hL'' := (LInv.stable Hs3.2 (fun u hu => hJFw.1.1 u (.inl hu)) hJLw).edge_child
                (sint.Z q, sint.Z i) (depR_mono Hs3.2 hdepw') hP
              have hvS3 : vn ∈ S3 := hL''.vS
              have hvc3 : (committedCopy (stOf k t3) vn).isSome := hF3.1.1 vn (.inl hvS3)
              have hvw : vn ≠ (sint.Z q, sint.Z i) := by
                intro e; have h1 := hJLw.numv; simp only [XS.toT] at h1
                rw [e, hw0] at h1; have := hidx.1; omega
              wp_auto
              wp_apply wp_insts_load_Lowlink ρ xs3 (stOf k t3) M3 _ pw HwM3 $$ [$Hinsts3]
                as %wl ⟨Hinsts3, %Hwl⟩
              wp_apply wp_insts_load_Lowlink ρ xs3 (stOf k t3) M3 vn v HvM3 $$ [$Hinsts3]
                as %vl ⟨Hinsts3, %Hvl⟩
              have hwl : sint.Z wl = xs3.lowF (sint.Z q, sint.Z i) := by
                obtain ⟨_, _, _, hf, he⟩ := Hwl; rw [he]; exact hf.2.2.2.2.2.2.2.2.2.2.2.1
              have hvl : sint.Z vl = xs3.lowF vn := by
                obtain ⟨_, _, _, hf, he⟩ := Hvl; rw [he]; exact hf.2.2.2.2.2.2.2.2.2.2.2.1
              have hi1 : sint.Z (i + W32 1) = sint.Z i + 1 := by word
              wp_if_destruct
              · -- `w.Lowlink < v.Lowlink`: `v.Lowlink = w.Lowlink`
                have hlt : xs3.lowF (sint.Z q, sint.Z i) < xs3.lowF vn := by omega
                wp_apply wp_insts_load_Lowlink ρ xs3 (stOf k t3) M3 _ pw HwM3 $$ [$Hinsts3]
                  as %wl2 ⟨Hinsts3, %Hwl2⟩
                have hwl2 : sint.Z wl2 = xs3.lowF (sint.Z q, sint.Z i) := by
                  obtain ⟨_, _, _, hf, he⟩ := Hwl2; rw [he]; exact hf.2.2.2.2.2.2.2.2.2.2.2.1
                icases instsG_upd ρ xs3 (stOf k t3) M3 vn v HvM3 $$ Hinsts3 with
                  ⟨⟨%cv3, %Hcv3, Hvi⟩, Hclose3⟩
                icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv3, Hvp, Hvcm, Hvlb, %Hiv3⟩
                iapply wp_fupd
                wp_auto
                imod ghostVar_update_halves (xs3.setLow vn (xs3.lowF (sint.Z q, sint.Z i))) ρ.xs xs3 xs3
                  $$ Hxs Hxs1 with ⟨Hxs, Hxs1⟩
                ihave Hinsts3 := Hclose3 $$ %(xs3.setLow vn (xs3.lowF (sint.Z q, sint.Z i)))
                  %(stOf k t3) [] [] [Hvp Hvcm Hvlb]
                · ipureintro; intro n hn
                  have hn' : vn ≠ n := fun e => hn e.symm
                  rw [XS.numF_setLow, XS.lowF_setLow]; simp [hn', XS.setLow]
                · ipureintro; intro _ _ _; rfl
                · iexists cv3; isplitr; · ipureintro; exact Hcv3
                  iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro
                  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, a13⟩ := Hiv3
                  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ?_, ?_, ?_⟩
                  · rw [XS.numF_setLow]; exact a11
                  · rw [XS.lowF_setLow]; simp only [ite_true]; rw [hwl2]
                  · exact a13
                have hL2 : LInv (depR (stOf k t3)) (xs.toT S idx) G vn
                    (fun x => (0 ≤ x.1 ∧ x.1 < sint.Z q ∨ x.1 = sint.Z q ∧ x.2 < sint.Z i) ∨
                      x = (sint.Z q, sint.Z i))
                    ((xs3.setLow vn (xs3.lowF (sint.Z q, sint.Z i))).toT S3 idx3) := by
                  rw [← XS.setLow_toT]
                  have hmin : min ((xs3.toT S3 idx3).low vn) ((xs3.toT S3 idx3).low (sint.Z q, sint.Z i)) =
                      xs3.lowF (sint.Z q, sint.Z i) := by simp only [XS.toT]; omega
                  rw [← hmin]; exact hL''
                imodintro
                wp_for_post
                iframe
                iexists (i + W32 1), t3, (xs3.setLow vn (xs3.lowF (sint.Z q, sint.Z i))), S3, idx3
                iframe
                isplitl
                · iapply (L.St_open ..).2; iframe
                  isplitl [HTH HPr HRs Hxs1 HPO HBt Hcu3 Hcrtv3 HM3 HMe3 Hrows3 Hinsts3 Hmono3 Hconfs3
                    Hconf3 Hpm3 Hrst3]
                  · iapply (L.LA_open ..).2; iframe
                    iapply (epaxosOwnG_open ..).2
                    iexists ispS3, crtS3, c1S3, isp3, msR3, pvtR3, cfs3, M3, cu3, pm3
                    iframe; iframe #; ipureintro
                    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := Hep3
                    refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, fun n hn => ?_, fun n hn => ?_, e11⟩
                    · by_cases hnv : n = vn
                      · subst hnv; rw [HvM3]; rfl
                      · have hvn' : vn ≠ n := fun e => hnv e.symm
                        rw [XS.numF_setLow, XS.lowF_setLow] at hn; simp only [hvn', ite_false] at hn
                        exact e9 n hn
                    · by_cases hnv : n = vn
                      · subst hnv; exact hvc3
                      · have hvn' : vn ≠ n := fun e => hnv e.symm
                        rw [XS.numF_setLow, XS.lowF_setLow] at hn; simp only [hvn', ite_false] at hn
                        exact e10 n hn
                  iapply (execPrivG_open ..).2
                  rw [show (xs3.setLow vn (xs3.lowF (sint.Z q, sint.Z i))).1 = xs3.1 from rfl]
                  iframe; iframe #
                ipureintro
                refine ⟨by omega, .inl (by omega), ?_, hJt.trans (HW2.1.trans Hs3.1),
                  (hJs.trans HW2.2.1).trans Hs3.2, hF3.setLow _ _⟩
                rw [hi1]
                refine hL2.done_mono (fun w _ hd => ?_)
                rcases hd with hd | ⟨hd1, hd2⟩
                · exact .inl (.inl (.inl hd))
                · rcases Int.lt_or_eq_of_le (Int.le_of_lt_add_one hd2) with hlt' | heqi
                  · exact .inl (.inl (.inr ⟨hd1, hlt'⟩))
                  · exact .inl (.inr (Prod.ext hd1 heqi))
              · -- unchanged
                have hge : ¬ xs3.lowF (sint.Z q, sint.Z i) < xs3.lowF vn := by omega
                have hL2 : LInv (depR (stOf k t3)) (xs.toT S idx) G vn
                    (fun x => (0 ≤ x.1 ∧ x.1 < sint.Z q ∨ x.1 = sint.Z q ∧ x.2 < sint.Z i) ∨
                      x = (sint.Z q, sint.Z i)) (xs3.toT S3 idx3) := by
                  have hmin : min ((xs3.toT S3 idx3).low vn) ((xs3.toT S3 idx3).low (sint.Z q, sint.Z i)) =
                      (xs3.toT S3 idx3).low vn := by simp only [XS.toT]; omega
                  rw [hmin] at hL''
                  have hsame : ({ xs3.toT S3 idx3 with low := replica.upd (xs3.toT S3 idx3).low vn ((xs3.toT S3 idx3).low vn) } : TState) = xs3.toT S3 idx3 := by
                    simp only [XS.toT]; congr 1; funext m; simp only [replica.upd]; split <;> simp_all
                  rw [hsame] at hL''; exact hL''
                wp_for_post
                iframe
                iexists (i + W32 1), t3, xs3, S3, idx3
                iframe
                isplitl
                · iapply (L.St_open ..).2; iframe
                  isplitl [HTH HPr HRs Hxs1 HPO HBt Hcu3 Hcrtv3 HM3 HMe3 Hrows3 Hinsts3 Hmono3 Hconfs3
                    Hconf3 Hpm3 Hrst3]
                  · iapply (L.LA_open ..).2; iframe
                    iapply (epaxosOwnG_open ..).2
                    iexists ispS3, crtS3, c1S3, isp3, msR3, pvtR3, cfs3, M3, cu3, pm3
                    iframe; iframe #; ipureintro; exact Hep3
                  iapply (execPrivG_open ..).2; iframe; iframe #
                ipureintro
                refine ⟨by omega, .inl (by omega), ?_, hJt.trans (HW2.1.trans Hs3.1),
                  (hJs.trans HW2.2.1).trans Hs3.2, hF3⟩
                rw [hi1]
                refine hL2.done_mono (fun w _ hd => ?_)
                rcases hd with hd | ⟨hd1, hd2⟩
                · exact .inl (.inl (.inl hd))
                · rcases Int.lt_or_eq_of_le (Int.le_of_lt_add_one hd2) with hlt' | heqi
                  · exact .inl (.inl (.inr ⟨hd1, hlt'⟩))
                  · exact .inl (.inr (Prod.ext hd1 heqi))
            · -- visited, not executed: on the stack
              have hwn0 : xsc'.numF (sint.Z q, sint.Z i) ≠ 0 := by
                intro e; apply Hif; rw [e] at hwnum
                apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at hwnum ⊢; simpa using hwnum
              have hL1 := hJLw.edge_onstack (sint.Z q, sint.Z i) hdepw' hwX hwn0
              have hi1 : sint.Z (i + W32 1) = sint.Z i + 1 := by word
              open_st
              ihave %HvM' := ghost_map_lookup $$ HM' Hv
              ihave %HwM' := ghost_map_lookup $$ HM' Hwe
              wp_apply wp_insts_load_Index ρ xsc' (stOf k tw2) M' _ pw HwM' $$ [$Hinsts']
                as %wi ⟨Hinsts', %Hwi⟩
              wp_apply wp_insts_load_Lowlink ρ xsc' (stOf k tw2) M' vn v HvM' $$ [$Hinsts']
                as %vl ⟨Hinsts', %Hvl⟩
              have hwi : sint.Z wi = xsc'.numF (sint.Z q, sint.Z i) := by
                obtain ⟨_, _, _, hf, he⟩ := Hwi; rw [he]; exact hf.2.2.2.2.2.2.2.2.2.2.1
              have hvl : sint.Z vl = xsc'.lowF vn := by
                obtain ⟨_, _, _, hf, he⟩ := Hvl; rw [he]; exact hf.2.2.2.2.2.2.2.2.2.2.2.1
              wp_if_destruct
              · -- `w.Index < v.Lowlink`: `v.Lowlink = w.Index` (`w ≠ v`: `v.Lowlink ≤ v.Index`)
                have hlt : xsc'.numF (sint.Z q, sint.Z i) < xsc'.lowF vn := by omega
                have hvw : vn ≠ (sint.Z q, sint.Z i) := by
                  intro e; have := (hJLw.inv.lowS vn hJLw.vS).1; simp only [XS.toT] at this
                  rw [← e] at hlt; omega
                wp_apply wp_insts_load_Index ρ xsc' (stOf k tw2) M' _ pw HwM' $$ [$Hinsts']
                  as %wi2 ⟨Hinsts', %Hwi2⟩
                have hwi2 : sint.Z wi2 = xsc'.numF (sint.Z q, sint.Z i) := by
                  obtain ⟨_, _, _, hf, he⟩ := Hwi2; rw [he]; exact hf.2.2.2.2.2.2.2.2.2.2.1
                icases instsG_upd ρ xsc' (stOf k tw2) M' vn v HvM' $$ Hinsts' with
                  ⟨⟨%cv3, %Hcv3, Hvi⟩, Hclose3⟩
                icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv3, Hvp, Hvcm, Hvlb, %Hiv3⟩
                icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS4, #HeuS4, Heu4⟩
                iapply wp_fupd
                wp_auto
                imod ghostVar_update_halves (xsc'.setLow vn (xsc'.numF (sint.Z q, sint.Z i))) ρ.xs xsc' xsc'
                  $$ Hxs Hxs1 with ⟨Hxs, Hxs1⟩
                ihave Hinsts' := Hclose3 $$ %(xsc'.setLow vn (xsc'.numF (sint.Z q, sint.Z i)))
                  %(stOf k tw2) [] [] [Hvp Hvcm Hvlb]
                · ipureintro; intro n hn
                  have hn' : vn ≠ n := fun e => hn e.symm
                  rw [XS.numF_setLow, XS.lowF_setLow]; simp [hn', XS.setLow]
                · ipureintro; intro _ _ _; rfl
                · iexists cv3; isplitr; · ipureintro; exact Hcv3
                  iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro
                  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, a13⟩ := Hiv3
                  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ?_, ?_, ?_⟩
                  · rw [XS.numF_setLow]; exact a11
                  · rw [XS.lowF_setLow]; simp only [ite_true]; rw [hwi2]
                  · exact a13
                have hL2 : LInv (depR (stOf k tw2)) (xs.toT S idx) G vn
                    (fun x => (0 ≤ x.1 ∧ x.1 < sint.Z q ∨ x.1 = sint.Z q ∧ x.2 < sint.Z i) ∨
                      x = (sint.Z q, sint.Z i))
                    ((xsc'.setLow vn (xsc'.numF (sint.Z q, sint.Z i))).toT Sc' idxc') := by
                  rw [← XS.setLow_toT]
                  have hmin : min ((xsc'.toT Sc' idxc').low vn) ((xsc'.toT Sc' idxc').num (sint.Z q, sint.Z i)) =
                      xsc'.numF (sint.Z q, sint.Z i) := by simp only [XS.toT]; omega
                  rw [← hmin]; exact hL1
                have hvc' : (committedCopy (stOf k tw2) vn).isSome := hJFw.1.1 vn (.inl hJLw.vS)
                imodintro
                wp_for_post
                iframe
                iexists (i + W32 1), tw2, (xsc'.setLow vn (xsc'.numF (sint.Z q, sint.Z i))), Sc', idxc'
                iframe
                isplitl
                · iapply (L.St_open ..).2; iframe
                  isplitl [HTH HPr HRs Hxs1 HPO HBt Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs'
                    Hconf' Hpm' Hrst']
                  · iapply (L.LA_open ..).2; iframe
                    iapply (epaxosOwnG_open ..).2
                    iexists ispS, crtS', c1S', isp, msR', pvtR', cfs', M', cu', pm'
                    iframe; iframe #; ipureintro; obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := Hep'
                    refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, fun n hn => ?_, fun n hn => ?_, e11⟩
                    · by_cases hnv : n = vn
                      · subst hnv; rw [HvM']; rfl
                      · have hvn' : vn ≠ n := fun e => hnv e.symm
                        rw [XS.numF_setLow, XS.lowF_setLow] at hn; simp only [hvn', ite_false] at hn
                        exact e9 n hn
                    · by_cases hnv : n = vn
                      · subst hnv; exact hvc'
                      · have hvn' : vn ≠ n := fun e => hnv e.symm
                        rw [XS.numF_setLow, XS.lowF_setLow] at hn; simp only [hvn', ite_false] at hn
                        exact e10 n hn
                  iapply (execPrivG_open ..).2
                  rw [show (xsc'.setLow vn (xsc'.numF (sint.Z q, sint.Z i))).1 = xsc'.1 from rfl]
                  iframe; iframe #
                ipureintro
                refine ⟨by omega, .inl (by omega), ?_, hJt.trans HW2.1,
                  hJs.trans HW2.2.1, hJFw.setLow _ _⟩
                rw [hi1]
                refine hL2.done_mono (fun w _ hd => ?_)
                rcases hd with hd | ⟨hd1, hd2⟩
                · exact .inl (.inl (.inl hd))
                · rcases Int.lt_or_eq_of_le (Int.le_of_lt_add_one hd2) with hlt' | heqi
                  · exact .inl (.inl (.inr ⟨hd1, hlt'⟩))
                  · exact .inl (.inr (Prod.ext hd1 heqi))
              · -- unchanged
                have hge : ¬ xsc'.numF (sint.Z q, sint.Z i) < xsc'.lowF vn := by omega
                have hL2 : LInv (depR (stOf k tw2)) (xs.toT S idx) G vn
                    (fun x => (0 ≤ x.1 ∧ x.1 < sint.Z q ∨ x.1 = sint.Z q ∧ x.2 < sint.Z i) ∨
                      x = (sint.Z q, sint.Z i)) (xsc'.toT Sc' idxc') := by
                  have hmin : min ((xsc'.toT Sc' idxc').low vn) ((xsc'.toT Sc' idxc').num (sint.Z q, sint.Z i)) =
                      (xsc'.toT Sc' idxc').low vn := by simp only [XS.toT]; omega
                  rw [hmin] at hL1
                  have hsame : ({ xsc'.toT Sc' idxc' with low := replica.upd (xsc'.toT Sc' idxc').low vn ((xsc'.toT Sc' idxc').low vn) } : TState) = xsc'.toT Sc' idxc' := by
                    simp only [XS.toT]; congr 1; funext m; simp only [replica.upd]; split <;> simp_all
                  rw [hsame] at hL1; exact hL1
                wp_for_post
                iframe
                iexists (i + W32 1), tw2, xsc', Sc', idxc'
                iframe
                isplitl
                · close_st
                ipureintro
                refine ⟨by omega, .inl (by omega), ?_, hJt.trans HW2.1, hJs.trans HW2.2.1, hJFw⟩
                rw [hi1]
                refine hL2.done_mono (fun w _ hd => ?_)
                rcases hd with hd | ⟨hd1, hd2⟩
                · exact .inl (.inl (.inl hd))
                · rcases Int.lt_or_eq_of_le (Int.le_of_lt_add_one hd2) with hlt' | heqi
                  · exact .inl (.inl (.inr ⟨hd1, hlt'⟩))
                  · exact .inl (.inr (Prod.ext hd1 heqi))
          · -- wait (the lock is released)
            simp only [hst4, decide_false, Bool.not_false, _root_.decide_true, ite_true]
            wp_pure
            open_st
            ihave %HvM' := ghost_map_lookup $$ HM' Hv
            icases instsG_upd ρ _ (stOf k tw2) M' vn v HvM' $$ Hinsts' with
              ⟨⟨%cv2, %Hcv2, Hvi⟩, Hclose2⟩
            icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv2, Hvp, Hvcm, Hvlb, %Hiv2⟩
            wp_join iprop(v_ptr ↦ v ∗ v ↦ iv2 ∗ lbRepG ρ iv2.lb' cv2.lb) at next
              with [v Hvp Hvlb] as ⟨v, Hvp, Hvlb⟩
            · icases lbRepG_open_time ρ iv2.lb' cv2.lb $$ Hvlb with (⟨%Hnil, Hvlb⟩ | ⟨%g, Hg, Hgclose⟩)
              · wp_auto
                simp only [Hnil, _root_.decide_true, Bool.not_true]
                wp_auto
                wp_join_done
              · ihave %hnn := typedPointsto_not_null _ _ _ $$ Hg
                wp_auto
                simp only [hnn, _root_.decide_false, Bool.not_false]
                wp_auto
                wp_method_call
                wp_call
                wp_auto
                wp_apply wp_Time_IsZero as %bz _
                cases bz
                · wp_auto
                  wp_join_done
                  iframe
                  simp only [lbTimes]
                  iapply Hgclose $$ %g.executedTime' %g.blockStartTime' Hg
                · wp_auto
                  wp_apply time.wp_Now as %tn _
                  wp_join_done
                  iframe
                  simp only [lbTimes]
                  iapply Hgclose $$ %g.executedTime' %tn Hg
            ihave Hinsts' := Hclose2 $$ %xsc' %(stOf k tw2) [] [] [Hvp Hvcm Hvlb]
            · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
            · ipureintro; intro _ _ _; rfl
            · iexists cv2; isplitr; · ipureintro; exact Hcv2
              iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiv2
            wp_apply wp_slice_literal (V := GoInterface) _
            isplitr
            · ipureintro; rfl
            iintro %_ ⟨-, -⟩
            wp_auto
            wp_apply wp_dlog_Printf $$ [$Hdlog]
            ihave St : L.St mtx idxp tw2 xsc' Sc' idxc' $$ [Hown Hidx Hpriv HTH HPr HRs Hxs1 HPO HBt
                Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs' Hconf' Hpm' Hrst']
            · close_st
            icases (L.St_open ..).1 $$ St with ⟨Hown, HLA, Hpriv, Hidx⟩
            imod L.LA_lb tw2 xsc' $$ HLA with ⟨HLA, #HTLbw⟩
            ihave HLI := L.li_closeA tw2 xsc' $$ [HLA]
            · iapply (L.LA_open ..).1 $$ HLA
            wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hown $HLI]
            wp_apply time.wp_Sleep
            iapply wp_fupd
            wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, HLI⟩
            icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS2, #HeuS2, Heu2⟩
            imod L.relock tw2 xsc' vn v $$ [HInv HLI Hxs HTLbw Hv] with ⟨%tw', HLA, Hxs, %Hst⟩
            · iframe; iframe #
            imod L.LA_kept tw2 tw' xsc' $$ [HInv HLA HTLbw] with ⟨HLA, %Hk⟩
            · iframe; iframe #
            imodintro
            wp_for_post
            iframe
            iexists tw'
            isplitl
            · iapply (L.St_open ..).2; iframe
              iapply (execPrivG_open ..).2; iframe; iframe #
            ipureintro; exact ⟨HW2.1.trans Hst.1, HW2.2.1.trans Hst.2, Hk q i HW2.2.2⟩
      · -- wait (the lock is released)
        simp only [_root_.decide_true, ite_true]
        wp_pure
        open_st
        ihave %HvM' := ghost_map_lookup $$ HM' Hv
        icases instsG_upd ρ _ (stOf k tw) M' vn v HvM' $$ Hinsts' with
          ⟨⟨%cv2, %Hcv2, Hvi⟩, Hclose2⟩
        icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv2, Hvp, Hvcm, Hvlb, %Hiv2⟩
        wp_join iprop(v_ptr ↦ v ∗ v ↦ iv2 ∗ lbRepG ρ iv2.lb' cv2.lb) at next
          with [v Hvp Hvlb] as ⟨v, Hvp, Hvlb⟩
        · icases lbRepG_open_time ρ iv2.lb' cv2.lb $$ Hvlb with (⟨%Hnil, Hvlb⟩ | ⟨%g, Hg, Hgclose⟩)
          · wp_auto
            simp only [Hnil, _root_.decide_true, Bool.not_true]
            wp_auto
            wp_join_done
          · ihave %hnn := typedPointsto_not_null _ _ _ $$ Hg
            wp_auto
            simp only [hnn, _root_.decide_false, Bool.not_false]
            wp_auto
            wp_method_call
            wp_call
            wp_auto
            wp_apply wp_Time_IsZero as %bz _
            cases bz
            · wp_auto
              wp_join_done
              iframe
              simp only [lbTimes]
              iapply Hgclose $$ %g.executedTime' %g.blockStartTime' Hg
            · wp_auto
              wp_apply time.wp_Now as %tn _
              wp_join_done
              iframe
              simp only [lbTimes]
              iapply Hgclose $$ %g.executedTime' %tn Hg
        ihave Hinsts' := Hclose2 $$ %xsc' %(stOf k tw) [] [] [Hvp Hvcm Hvlb]
        · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
        · ipureintro; intro _ _ _; rfl
        · iexists cv2; isplitr; · ipureintro; exact Hcv2
          iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiv2
        wp_apply wp_slice_literal (V := GoInterface) _
        isplitr
        · ipureintro; rfl
        iintro %_ ⟨-, -⟩
        wp_auto
        wp_apply wp_dlog_Printf $$ [$Hdlog]
        ihave St : L.St mtx idxp tw xsc' Sc' idxc' $$ [Hown Hidx Hpriv HTH HPr HRs Hxs1 HPO HBt
            Hcu' Hcrtv' HM' HMe' Hrows' Hinsts' Hmono' Hconfs' Hconf' Hpm' Hrst']
        · close_st
        icases (L.St_open ..).1 $$ St with ⟨Hown, HLA, Hpriv, Hidx⟩
        imod L.LA_lb tw xsc' $$ HLA with ⟨HLA, #HTLbw⟩
        ihave HLI := L.li_closeA tw xsc' $$ [HLA]
        · iapply (L.LA_open ..).1 $$ HLA
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hown $HLI]
        wp_apply time.wp_Sleep
        iapply wp_fupd
        wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, HLI⟩
        icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS2, #HeuS2, Heu2⟩
        imod L.relock tw xsc' vn v $$ [HInv HLI Hxs HTLbw Hv] with ⟨%tw', HLA, Hxs, %Hst⟩
        · iframe; iframe #
        imodintro
        wp_for_post
        iframe
        iexists tw'
        isplitl
        · iapply (L.St_open ..).2; iframe
          iapply (execPrivG_open ..).2; iframe; iframe #
        ipureintro; exact ⟨HW.1.trans Hst.1, HW.2.trans Hst.2⟩
    · -- replica `q`'s dependencies are handled
      wp_for_post
      iframe
      iexists (q + W32 1), _, _, _, _
      iframe q St
      ipureintro
      have hq1 : sint.Z (q + W32 1) = sint.Z q + 1 := by word
      obtain ⟨hJ1, hJ2, hJL, hJt, hJs, hJF⟩ := HJ
      refine ⟨by omega, by omega, ?_, hJt, hJs, hJF⟩
      refine hJL.done_mono (fun w hw hdn => .inl ?_)
      obtain ⟨hdn1, hdn2⟩ := hdn
      rw [hq1] at hdn2
      rcases Int.lt_or_eq_of_le (Int.le_of_lt_add_one hdn2) with hlt | heqq
      · exact .inl ⟨hdn1, hlt⟩
      · refine .inr ⟨heqq, ?_⟩
        obtain ⟨c, hc, -, -, -, hw2⟩ := hw
        obtain ⟨c2, hc2, -, -, hd2, -⟩ := hJs vn cv hav
        rw [hc2] at hc; cases hc
        rw [hd2, heqq, ← hdv] at hw2
        have hid : ¬ sint.Z i ≤ sint.Z d := Hif
        omega
  · -- every dependency is handled
    have hq3' : ¬ sint.Z q < 3 := fun hh => Hif (by simp [sint.Z] at hh ⊢; simp [hh])
    have hq3 : sint.Z q = 3 := by have := HL.2.1; omega
    have hdec : decide (sint.Z q < sint.Z (W32 (sint.Z (W64 3)))) = false := by
      rw [decide_eq_false_iff_not, show sint.Z (W32 (sint.Z (W64 3))) = 3 by word]; omega
    obtain ⟨-, -, hL, htc, hstc, hFc⟩ := HL
    have hall : ∀ w, depR (stOf k tc) vn w → (0 ≤ w.1 ∧ w.1 < sint.Z q) := by
      intro w hw; obtain ⟨_, _, h0, h3, _⟩ := hw; omega
    icases (L.St_open ..).1 $$ St with ⟨Hown, HLA, Hpriv, Hidx⟩
    icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
    ihave ⟨HEP, %Hok⟩ := epaxosOwnG_ok ρ h r xsc (stOf k tc) $$ HEP
    icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
      %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
      Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
    ihave %HvM := ghost_map_lookup $$ HM Hv
    icases instsG_upd ρ xsc (stOf k tc) M vn v HvM $$ Hinsts with ⟨⟨%cv, %Hcv, Hvi⟩, Hclose⟩
    icases (copyRepG_open ..).1 $$ Hvi with ⟨%iv, Hvp, Hvcmds, Hvlb, %Hiv⟩
    wp_auto
    have hnum : xsc.numF vn = idx := hL.numv
    wp_if_destruct
    · -- `v.Lowlink == v.Index`: `v`'s component is found
      have heq : (xsc.toT Sc idxc).low vn = (xsc.toT Sc idxc).num vn := by
        have h1 := Hiv.2.2.2.2.2.2.2.2.2.2.1; have h2 := Hiv.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [XS.toT]; rw [Hif] at h2; omega
      obtain ⟨T, hT, hscc, hpost⟩ := hL.finish_pop hall heq
      ihave Hinsts := Hclose $$ %xsc %(stOf k tc) [] [] [Hvp Hvcmds Hvlb]
      · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
      · ipureintro; intro _ _ _; rfl
      · iexists cv; isplitr; · ipureintro; exact Hcv
        iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiv
      icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS, #HeuS, Heu⟩
      icases (stackOwn_open ..).1 $$ Hstk with ⟨%s2, %ptrs, Hsg, Hs, Hscap, %Hsf, #HSe⟩
      ihave ⟨HM, %Hrel⟩ := stackElems_rel ρ Sc ptrs M $$ [HSe HM]
      · iframe; iframe #
      ihave %Hs2len := ownSlice_len _ _ _ $$ Hs
      ihave %Hs2cap := ownSliceCap_wf _ _ $$ Hscap
      have hSc : Sc = S ++ vn :: T := by simpa [XS.toT] using hT
      have hs2len : sint.Z s2.len = (Sc.length : Int) := by
        have h1 := Hsf.1; have h2 := Hs2len; simp only [sint.nat, sint.Z] at h2 ⊢; omega
      have hSlen : sint.Z s.len = (S.length : Int) := hslen'
      have hSlen2 : (S.length : Int) + 1 + T.length = Sc.length := by
        rw [hSc]; simp only [List.length_append, List.length_cons]; omega
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s2.len ∧
          sint.Z s2.len ≤ sint.Z s2.cap by
        rw [hSlen, hs2len]; have := Hs2cap; refine ⟨by omega, by omega, ?_⟩
        rw [← hs2len]; omega)]
      icases (ownSlice_split_all s.len s2 (DFrac.own 1) ptrs ⟨by omega, by
        rw [hSlen, hs2len]; omega⟩).1 $$ Hs with ⟨Hpre, Hsuf⟩
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface) _
      isplitr
      · ipureintro; rfl
      iintro %_ ⟨-, -⟩
      wp_auto
      wp_apply wp_dlog_Printf $$ [$Hdlog]
      -- the sorter: the component's pointers and the instance space
      have hSn : sint.nat s.len = S.length := by
        have := hSlen; simp only [sint.nat, sint.Z] at this ⊢; omega
      ihave Hna : naOwn ρ xsc (stOf k tc) M (slice.slice s2 Loc s.len s2.len) (vn :: T)
        $$ [Hsuf Hinsts]
      · iapply (naOwn_open ..).2; iexists _; iframe; ipureintro
        rw [hSn]
        refine ⟨?_, fun i n hin => ?_, fun n hn => hFc.1.1 n (.inl (by rw [hSc]; simp [hn]))⟩
        · rw [List.length_drop, Hsf.1, hSc]; simp
        · have := Hrel (S.length + i) n (by rw [hSc, List.getElem?_append_right (by omega)]; simpa using hin)
          rw [List.getElem?_drop]; exact this
      have hTl : (vn :: T).length ≤ 2 ^ 62 := by
        have := hidx.2.1; have := hFc; simp only [List.length_cons]
        have h1 : Sc.length + 1 ≤ idxc := (SCF_idx hFc hL.inv.nodup).2.2
        have h2 : idxc ≤ 3 * (2 * 1024 * 1024) + 1 := (SCF_idx hFc hL.inv.nodup).2.1
        omega
      wp_apply wp_sort_nodeArray ρ xsc (stOf k tc) M _ (vn :: T) hTl $$ [Hna]
      · iexact Hna
      iintro ⟨%Ls, Hna, %Hperm, %Hsorted⟩
      icases (naOwn_open ..).1 $$ Hna with ⟨%ptrs', Hsuf, Hinsts, %Hna⟩
      wp_auto
      -- the component's members, executed in turn
      ihave HR : (∃ (j : w64) (tj : List Ev) (wv : Loc),
          "i" ∷ i_ptr ↦ j ∗ "w" ∷ w_ptr ↦ wv ∗ "Hown" ∷ sync.ownMutex mtx ∗
          "HLA" ∷ L.LA tj (xsJ xsc Ls (sint.nat j)) ∗
          "Hxs" ∷ ghostVar ρ.xs (1 : Qp).half (xsJ xsc Ls (sint.nat j)) ∗
          "Hsuf" ∷ slice.slice s2 Loc s.len s2.len ↦* ptrs' ∗
          "%HJ" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ Ls.length ∧ tc <+: tj ∧
            Stable (stOf k tc) (stOf k tj)⌝ : IProp GF)
        $$ [i w Hown HTH HPr HRs Hxs1 HPO HBt Hcu Hcrtv HM HMe Hrows Hinsts Hmono Hconfs Hconf Hpm
          Hrst Hxs Hsuf]
      · iexists (W64 0), tc, (zero_val Loc)
        rw [show sint.nat (W64 0) = 0 from rfl, xsJ_zero]
        iframe
        isplitl
        · iapply (L.LA_open ..).2; iframe
          iapply (epaxosOwnG_open ..).2
          iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
          iframe; iframe #; ipureintro; exact Hep
        ipureintro; exact ⟨by decide, by simp, List.prefix_refl _, Stable.refl _⟩
      have hlsl : sint.Z (s2.len - s.len) = (Ls.length : Int) := by
        have := Hperm.length_eq; simp only [List.length_cons] at this
        have h1 : sint.Z (s2.len - s.len) = sint.Z s2.len - sint.Z s.len := by
          have := Hs2cap; have := hSlen; word
        rw [h1, hSlen, hs2len]; omega
      -- the component, at the pop: committed members, its closure, its order
      have hLsc : ∀ u ∈ Ls, (committedCopy (stOf k tc) u).isSome := fun u hu =>
        hFc.1.1 u (.inl (by rw [hSc]; exact List.mem_append_right _ ((Hperm.mem_iff).2 hu)))
      have hLsscc : sccStep (depR (stOf k tc)) xsc.1 Ls := sccStep_perm Hperm hscc
      have hLsnd : Ls.Nodup := hLsscc.2.1
      have hLssort : Ls.Pairwise (fun a b => keyLt (keyS (stOf k tc) a) (keyS (stOf k tc) b)) :=
        sorted_of_sort (stOf k tc) Ls hLsnd Hsorted
      have hXc : XClosed (depR (stOf k tc)) xsc.1 := hFc.2
      have hXcm : ∀ u ∈ xsc.1, (committedCopy (stOf k tc) u).isSome := fun u hu =>
        hFc.1.1 u (.inr hu)
      wp_for HR
      wp_if_destruct
      · -- an iteration: the `j`-th member
        have hjl : sint.nat j < Ls.length := by
          rw [hlsl] at Hif; have := HJ.1; simp only [sint.nat, sint.Z] at Hif this ⊢; omega
        obtain ⟨wn, hwn⟩ : ∃ wn, Ls[sint.nat j]? = some wn := ⟨_, List.getElem?_eq_getElem hjl⟩
        obtain ⟨pw, hpw, hMw⟩ := Hna.2.1 _ wn hwn
        have hwSc : wn ∈ Sc := by
          rw [hSc]; exact List.mem_append_right _ ((Hperm.mem_iff).2 (List.mem_of_getElem? hwn))
        obtain ⟨iw, hiw⟩ := List.mem_iff_getElem?.1 hwSc
        ihave ⟨%pw', %hpw', #Hwe⟩ := stackElems_elem ρ Sc ptrs iw wn hiw $$ HSe
        have hpweq : pw' = pw := by
          obtain ⟨p1, hp1, hM1⟩ := Hrel iw wn hiw
          rw [hpw'] at hp1; cases hp1; rw [hM1] at hMw; cases hMw; rfl
        cases hpweq
        rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (s2.len - s.len)
          from ⟨HJ.1, by rw [hlsl]; simp only [sint.nat, sint.Z] at hjl ⊢; omega⟩)]
        wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) _ (sint.Z j)
          ptrs' _ pw HJ.1 $$ [$Hsuf] as Hsuf
        · ipureintro; exact hpw
        -- wait for the commands (`w.Cmds == nil`: the lock is released meanwhile)
        ihave HW : (∃ tw, "Hown" ∷ sync.ownMutex mtx ∗ "HLA" ∷ L.LA tw (xsJ xsc Ls (sint.nat j)) ∗
            "%HW" ∷ ⌜tc <+: tw ∧ Stable (stOf k tc) (stOf k tw)⌝ : IProp GF) $$ [Hown HLA]
        · iexists tj; iframe; ipureintro; exact ⟨HJ.2.2.1, HJ.2.2.2⟩
        wp_for HW
        wp_apply wp_LA_load_Cmds L tw _ wn pw $$ [$HLA $Hwe] as %cs HLA
        wp_if_destruct
        · -- no commands yet: wait
          imod L.LA_lb tw (xsJ xsc Ls (sint.nat j)) $$ HLA with ⟨HLA, #HTLbw⟩
          ihave HLI := L.li_closeA tw (xsJ xsc Ls (sint.nat j)) $$ [HLA]
          · iapply (L.LA_open ..).1 $$ HLA
          wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hown $HLI]
          wp_apply time.wp_Sleep
          iapply wp_fupd
          wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hown, HLI⟩
          imod L.relock tw (xsJ xsc Ls (sint.nat j)) wn pw $$ [HInv HLI Hxs HTLbw Hwe]
            with ⟨%tw', HLA, Hxs, %Hst⟩
          · iframe; iframe #
          imodintro
          wp_for_post
          iframe
          iexists tw'; iframe; ipureintro
          exact ⟨HW.1.trans Hst.1, HW.2.trans Hst.2⟩
        · -- the commands are there
          have hcs : ¬ cs = slice.nil := fun e => Hif (by simp [e])
          simp only [hcs, decide_false, Bool.false_eq_true, ite_false]
          -- the step's later credits (review stage 2, finding 7): this iteration's pure steps
          wp_pure_lc Hlc1
          wp_pure_lc Hlc2
          icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
          ihave ⟨HEP, %Hokw⟩ := epaxosOwnG_ok ρ h r _ (stOf k tw) $$ HEP
          icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS', %crtS', %c1S', %isp', %msR', %pvtR',
            %cfs', %M', %cu', %pm', #HhR', #HnoC', #HIS', #Hisp', #Hcrt', #Hc1', #Hc1s', #Hms',
            #Hpvt', Hcu, Hcrtv, HM, HMe, Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
          ihave %HwM := ghost_map_lookup $$ HM Hwe
          imod L.th_deps tw $$ [HInv HTH] with ⟨HTH, %Hdw⟩
          · iframe; iframe #
          icases instsG_upd ρ _ (stOf k tw) M' wn pw HwM $$ Hinsts with
            ⟨⟨%cw, %Hcw, Hwi⟩, Hclose⟩
          icases (copyRepG_open ..).1 $$ Hwi with ⟨%iw, Hwp, Hwcmds, Hwlb, %Hiw⟩
          -- the leader's bookkeeping: its execution time (and a log line)
          wp_pure
          wp_join iprop(w_ptr ↦ pw ∗ pw ↦ iw ∗ lbRepG ρ iw.lb' cw.lb ∗ e_ptr ↦ ex) at next
            with [w Hwp Hwlb e] as ⟨w, Hwp, Hwlb, e⟩
          · icases lbRepG_open_time ρ iw.lb' cw.lb $$ Hwlb with (⟨%Hnil, Hwlb⟩ | ⟨%g, Hg, Hgclose⟩)
            · wp_auto
              simp only [Hnil, _root_.decide_true, Bool.not_true]
              wp_auto
              wp_join_done
            · ihave %hnn := typedPointsto_not_null _ _ _ $$ Hg
              wp_auto
              simp only [hnn, _root_.decide_false, Bool.not_false]
              wp_auto
              wp_apply time.wp_Now as %tn _
              wp_method_call
              wp_call
              wp_auto
              wp_apply wp_Time_IsZero as %bz _
              cases bz
              · wp_auto
                wp_method_call
                wp_call
                wp_auto
                wp_apply time.Time.wp_Sub as %d _
                wp_method_call
                wp_call
                wp_auto
                wp_apply time.Time.wp_Sub as %d2 _
                wp_apply wp_slice_literal (V := GoInterface) _
                isplitr
                · ipureintro; rfl
                iintro %_ ⟨-, -⟩
                wp_auto
                wp_apply wp_dlog_Printf $$ [$Hdlog]
                wp_join_done
                iframe
                simp only [lbTimes]
                iapply Hgclose $$ %tn %g.blockStartTime' Hg
              · wp_auto
                wp_method_call
                wp_call
                wp_auto
                wp_apply time.Time.wp_Sub as %d2 _
                wp_apply wp_slice_literal (V := GoInterface) _
                isplitr
                · ipureintro; rfl
                iintro %_ ⟨-, -⟩
                wp_auto
                wp_apply wp_dlog_Printf $$ [$Hdlog]
                wp_join_done
                iframe
                simp only [lbTimes]
                iapply Hgclose $$ %tn %g.blockStartTime' Hg
          -- the execution event `exec (Leader, Slot)`: resolved, then the step
          have hst := HW.2
          have hwc : (committedCopy (stOf k tw) wn).isSome :=
            hst.isSome (hLsc wn (List.mem_of_getElem? hwn))
          obtain ⟨cw', hcw'⟩ := Option.isSome_iff_exists.1 hwc
          have hcwe : cw' = cw := by
            have := (committedCopy_inst hcw').1; rw [Hcw] at this; cases this; rfl
          subst hcwe
          have hwX : wn ∉ (xsJ xsc Ls (sint.nat j)).1 := by
            simp only [xsJ, List.mem_append, not_or]
            refine ⟨hLsscc.2.2.1 wn (List.mem_of_getElem? hwn), fun hm => ?_⟩
            obtain ⟨i', hi', he⟩ := List.getElem_of_mem hm
            rw [List.length_take] at hi'
            rw [List.getElem_take] at he
            have := (List.getElem?_eq_some_iff.1 hwn).2
            have hne := (List.pairwise_iff_getElem.1 hLsnd) i' (sint.nat j) (by omega)
              (List.getElem?_eq_some_iff.1 hwn).1 (by omega)
            exact hne (he.trans this.symm)
          have hcwst : cw'.status = model.St.COMMITTED := by
            rcases (committedCopy_inst hcw').2 with h1 | h1
            · exact h1
            · exfalso; apply hwX; rw [← Hokw.1]
              simp only [executedB, hcw', h1, beq_self_eq_true]
          have hqw : BitVec.ofInt 32 wn.1 = iw.Leader' := by
            rw [← Hiw.2.2.2.2.2.2.2.2.1]; exact BitVec.ofInt_toInt
          have hiw : BitVec.ofInt 32 wn.2 = iw.Slot' := by
            rw [← Hiw.2.2.2.2.2.2.2.2.2.1]; exact BitVec.ofInt_toInt
          have hwbox := committedCopy_box hwc
          have hinst : (stOf k tw).inst iw.Leader' iw.Slot' = some cw' := by
            rw [← hqw, ← hiw]; exact Hcw
          have hib : model.inBox iw.Leader' iw.Slot' = true := by
            unfold model.inBox; rw [Hiw.2.2.2.2.2.2.2.2.1, Hiw.2.2.2.2.2.2.2.2.2.1]
            obtain ⟨b0, b1, b2, b3⟩ := hwbox
            exact decide_eq_true ⟨b0, b1, b2, b3⟩
          have hwnq : (sint.Z iw.Leader', sint.Z iw.Slot') = wn := by
            rw [Hiw.2.2.2.2.2.2.2.2.1, Hiw.2.2.2.2.2.2.2.2.2.1]
          have hguard : execGuard (stOf k tw) (sint.Z iw.Leader', sint.Z iw.Slot') := by
            rw [hwnq]
            refine execGuard_of (stOf k tw) xsc.1 Ls (sint.nat j) wn (sccStep.stable hst hLsc hLsscc)
              (XClosed.stable hst hXcm hXc) (fun u hu => hst.isSome (hLsc u hu)) ?_ Hokw.2
              (sorted_stable hst hLsc hLssort) hwn
            intro u; rw [Hokw.1]; simp [xsJ]
          wp_apply L.res_wp tw [] iw.Leader' iw.Slot' $$ [$Hpkg $Hpp $HPr]
          iintro ⟨HPr, -⟩
          imod L.th_ok tw iw.Leader' iw.Slot' cw' hib hinst hcwst hguard $$ [HInv HTH]
            with ⟨HTH, %Hstep⟩
          · iframe; iframe #
          obtain ⟨s', outs, hstep⟩ := Hstep
          imod L.crit tw iw.Leader' iw.Slot' s' outs hstep $$ [HInv HTH HPr Hlc1 Hlc2 HPO]
            with ⟨HTH, HPr, HPO, %Hs'⟩
          · iframe; iframe #; iapply (lc_split (n := 1) (m := 1)).2; iframe
          obtain ⟨c1, hc1, hres⟩ := stepExec_ok (show model.stepExec (stOf k tw) iw.Leader' iw.Slot'
            = .ok (s', outs) from hstep)
          rw [hinst] at hc1; cases hc1
          have hstab : Stable (stOf k tw) s' := execRes_stable hinst hres
          have hcoe := execRes_committed_iff hinst hcwst hres
          ihave %Hid := L.rs_id (stOf k tw) $$ HRs
          icases (cmdsRepG_open ..).1 $$ Hwcmds with ⟨%gs, #Hgs, %Hgsc⟩
          ihave %Hgslen := ownSlice_len _ _ _ $$ Hgs
          -- `if len(w.Cmds) > 0`: the result to the run loop (G44: not for a no-op)
          wp_auto
          wp_join iprop(∃ pm'' : GMap w64 src.gryffproto.ValTag, pvtR' ↦$ pm'' ∗
              L.PO (tw ++ [.exec iw.Leader' iw.Slot']) [] ∗
              ⌜(∀ kk, kk ≠ W64 0 → pm''.lookup kk = none) ∧
                (pm''.lookup (W64 0)).map replica2.vtOf = s'.prevValTag⌝ ∗
              w_ptr ↦ pw ∗ pw ↦ iw ∗ e_ptr ↦ ex)
            with [Hpm HPO w Hwp e] as ⟨%pm'', Hpm, HPO, %Hpm'', w, Hwp, e⟩
          · -- a command: `PrevValTag`, the CAS, the result sent to the run loop
            have hCl : sint.Z (W64 0) < sint.Z iw.Cmds'.len := Hif
            obtain ⟨g0, gt, rfl⟩ : ∃ g0 gt, gs = g0 :: gt := by
              cases gs with
              | nil =>
                exfalso; have h1 := Hgslen.1; simp only [List.length_nil, sint.nat] at h1
                have h0 : sint.Z (W64 0) = 0 := rfl
                simp only [sint.Z] at Hif h0 h1; omega
              | cons g0 gt => exact ⟨g0, gt, rfl⟩
            have hcm : cw'.cmds = replica2.cmdOf g0 :: gt.map replica2.cmdOf := by
              rw [← Hgsc.1]; rfl
            have hk0 : g0.K' = W64 0 := by
              have := (Hdw.1 wn cw' hcw').2
              rw [hcm] at this
              simp only [model.cmdsOk, List.all_cons, Bool.and_eq_true, model.Cmd.ok,
                beq_iff_eq, replica2.cmdOf] at this
              exact this.1.2
            rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z iw.Cmds'.len from
              ⟨by decide, hCl⟩)]
            icases ownSlice_elem_acc (sint.Z (W64 0)) g0 iw.Cmds' DFrac.discard (g0 :: gt)
              (by decide) rfl $$ Hgs with ⟨#Hg0, -⟩
            wp_apply wp_load_cmd_K _ g0 $$ [Hg0]
            · iexact Hg0
            rw [hk0]
            wp_apply wp_map_lookup2 _ _ pvtR' pm' (W64 0) _ $$ [$Hpm] as Hpm
            -- the value the CAS applies to: the newer of the base and `PrevValTag`
            wp_join iprop(∃ vtv : src.gryffproto.ValTag, vt_ptr ↦ vtv ∗ pw ↦ iw ∗ w_ptr ↦ pw ∗
                ⌜replica2.vtOf vtv = execVT0 (stOf k tw) cw'⌝) at next
              with [vt Hwp w pvt] as ⟨%vtv, vt, Hwp, w, %Hvt0⟩
            · have hpv := Hep.2.2.2.2.2.1
              cases hpm0 : pm' !! W64 0 with
              | none =>
                rw [hpm0] at hpv; simp only [Option.map_none] at hpv
                simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
                wp_auto
                wp_join_done
                iexists _; iframe; ipureintro
                unfold execVT0; rw [← hpv]; simp only [replica2.vtOf]; rw [← Hiw.2.2.2.2.1]; rfl
              | some pvg =>
                rw [hpm0] at hpv; simp only [Option.map_some] at hpv
                simp only [Option.isSome_some, _root_.decide_true, Bool.not_true]
                wp_auto
                wp_apply wp_inst_Base_GreaterThan pw iw pvg.T' $$ [$Hwp] as Hwp
                cases hgt : (replica2.tagOf iw.Base'.T').gt (replica2.tagOf pvg.T')
                · wp_auto
                  wp_join_done
                  iexists _; iframe; ipureintro
                  unfold execVT0; rw [← hpv, ← Hiw.2.2.2.2.1]
                  simp only [replica2.vtOf] at hgt ⊢
                  simp only [hgt, Bool.false_eq_true, ite_false]
                · wp_auto
                  wp_join_done
                  iexists _; iframe; ipureintro
                  unfold execVT0; rw [← hpv, ← Hiw.2.2.2.2.1]
                  simp only [replica2.vtOf] at hgt ⊢
                  simp only [hgt, ite_true]
            -- the CAS
            wp_join iprop(∃ vtv1 : src.gryffproto.ValTag, vt_ptr ↦ vtv1 ∗ pw ↦ iw ∗ w_ptr ↦ pw ∗
                ⌜replica2.vtOf vtv1 = execVT1 (replica2.vtOf vtv) (replica2.cmdOf g0)⌝) at next
              with [vt Hwp w] as ⟨%vtv1, vt, Hwp, w, %Hvt1⟩
            · rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z iw.Cmds'.len from
                ⟨by decide, hCl⟩)]
              wp_apply wp_load_cmd_OldValue _ g0 $$ [Hg0]
              · iexact Hg0
              wp_if_destruct
              · rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z iw.Cmds'.len from
                  ⟨by decide, hCl⟩)]
                wp_apply wp_load_cmd_V _ g0 $$ [Hg0]
                · iexact Hg0
                wp_join_done
                iexists _; iframe; ipureintro
                unfold execVT1; simp only [replica2.cmdOf, replica2.vtOf, Hif, ite_true]
              · wp_join_done
                iexists _; iframe; ipureintro
                unfold execVT1; simp only [replica2.cmdOf, replica2.vtOf, Hif, ite_false]
            -- `PrevValTag[0] = vt`
            rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z iw.Cmds'.len from
              ⟨by decide, hCl⟩)]
            wp_apply wp_load_cmd_K _ g0 $$ [Hg0]
            · iexact Hg0
            rw [hk0]
            wp_apply wp_mapInsert _ pvtR' pm' (W64 0) _ $$ [$Hpm] as Hpm
            -- `executeOverwriteChan <- &ExecuteOverwrite{K, vt.V, &vt.T, Leader, Slot}`
            icases (bagAtG_open ..).1 $$ Heo with ⟨%ch, #Hch, #Hbag⟩
            wp_auto
            rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z iw.Cmds'.len from
              ⟨by decide, hCl⟩)]
            wp_apply wp_load_cmd_K _ g0 $$ [Hg0]
            · iexact Hg0
            have hvt : replica2.vtOf (src.gryffproto.ValTag.mk vtv1.V' (src.gryffproto.Tag.mk vtv1.T'.Ts' vtv1.T'.Cid' (vtv1.T'.Rmwc' + W32 1))) = execVT (stOf k tw) cw' (replica2.cmdOf g0) := by
              unfold execVT; rw [← Hvt0, ← Hvt1]; rfl
            unfold execRes at hres; rw [hcm] at hres
            simp only [Hid, sendTo_rid, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hres
            obtain ⟨rfl, rfl⟩ := hres
            imod L.self (tw ++ [.exec iw.Leader' iw.Slot']) _ [] $$ [HInv HPO] with ⟨HPO, HTok⟩
            · iframe; iframe #
            icases typedPointsto_not_null_dup _ _ _ $$ vt with ⟨vt, %Hvtnn⟩
            iStructNamed vt
            ipersist T
            wp_apply wp_bag_send (ρ.chans "executeOverwrite") ch _ (eoChanPG L.Tok) $$ [$Hbag «$v» HTok]
            · iapply (eoChanPG_open ..).2
              iexists _; iframe
              iexists _; iframe #
              ipureintro
              refine ⟨hk0, ?_⟩
              rw [← hvt, show cw'.leader = iw.Leader' from Hiw.2.2.2.2.2.2.1.symm,
                show cw'.slot = iw.Slot' from Hiw.2.2.2.2.2.1.symm]
              rfl
            wp_join_done
            iexists _; iframe
            ipureintro
            refine ⟨fun kk hkk => ?_, ?_⟩
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)]; exact Hep.2.2.2.2.1 kk hkk
            · rw [GMap.lookup_insert]; simp only [Option.map_some]; rw [hvt]; rfl
          · -- a no-op (G44): nothing
            have hgs : gs = [] := by
              have := Hgslen.1
              cases gs with
              | nil => rfl
              | cons _ _ => exfalso; apply Hif; simp only [List.length_cons] at this
                            simp only [sint.nat] at this; word
            subst hgs
            have hcm : cw'.cmds = [] := by rw [← Hgsc.1]; rfl
            unfold execRes at hres; rw [hcm] at hres
            simp only [Option.some.injEq, Prod.mk.injEq] at hres
            obtain ⟨rfl, rfl⟩ := hres
            iexists pm'; iframe
            ipureintro; exact ⟨Hep.2.2.2.2.1, Hep.2.2.2.2.2.1⟩
          wp_apply wp_slice_literal (V := GoInterface) _
          isplitr
          · ipureintro; rfl
          iintro %_ ⟨-, -⟩
          wp_auto
          iapply wp_fupd
          wp_apply wp_dlog_Printf $$ [$Hdlog]
          try wp_auto
          -- the new state: the instance executed, the search state, the lock's contents
          obtain ⟨pv, hs'eq⟩ := execRes_state hres
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
            have := HJ.1; have := hjl; have := hlsl
            simp only [sint.nat, sint.Z] at *; have := Hs2cap; word
          have hx2 : (xsJ xsc Ls (sint.nat j + 1)).1 = (xsJ xsc Ls (sint.nat j)).1 ++ [wn] := by
            simp only [xsJ, List.append_assoc]
            rw [List.take_add_one, hwn]; rfl
          imod ghostVar_update_halves (xsJ xsc Ls (sint.nat j + 1)) ρ.xs _ _ $$ Hxs Hxs1
            with ⟨Hxs, Hxs1⟩
          ihave Hinsts := Hclose $$ %(xsJ xsc Ls (sint.nat j + 1)) %s' [] [] [Hwp Hwlb]
          · ipureintro; intro n' hn'
            refine ⟨rfl, rfl, ?_⟩
            rw [hx2, List.mem_append]; simp [hn']
          · ipureintro; intro n' hn' hok
            obtain ⟨c2, hc2, -, hl2, hs2⟩ := hok
            rw [hs'eq]; simp only [RState.setInst]
            split
            · rename_i hh; exfalso; apply hn'
              have r1 := c2.leader.le_toInt; have r2 := c2.leader.toInt_lt
              have r3 := c2.slot.le_toInt; have r4 := c2.slot.toInt_lt
              simp only [sint.Z] at hl2 hs2
              have h1 : sint.Z (BitVec.ofInt 32 n'.1) = n'.1 :=
                sint_ofInt_of (by rw [← hl2]; omega) (by rw [← hl2]; omega)
              have h2 : sint.Z (BitVec.ofInt 32 n'.2) = n'.2 :=
                sint_ofInt_of (by rw [← hs2]; omega) (by rw [← hs2]; omega)
              rw [← hwnq, ← hh.1, ← hh.2, h1, h2]
            · rfl
          · iexists { cw' with status := model.St.EXECUTED }
            isplitr
            · ipureintro; rw [hs'eq]; simp only [RState.setInst]; rw [hqw, hiw]; simp
            iapply (copyRepG_open ..).2
            iexists _; iframe
            isplitl
            · iapply (cmdsRepG_open ..).2; iexists gs; iframe #; ipureintro; exact Hgsc
            ipureintro
            obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := Hiw
            refine ⟨a1, rfl, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, ?_⟩
            rw [hx2]; simp
          ihave HRs := L.rs_congr (stOf k tw) s' iw.Leader' iw.Slot' outs hstep $$ HRs
          ihave HMe := ptrElems_congr ρ (stOf k tw) s' M' hcoe $$ HMe
          have hep2 : epFacts (xsJ xsc Ls (sint.nat j + 1)) s' isp' cfs' M' cu' pm'' := by
            obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := Hep
            have hkey : ∀ q' i' : w32, s'.inst q' i' =
                if q' = iw.Leader' ∧ i' = iw.Slot' then some { cw' with status := model.St.EXECUTED }
                else (stOf k tw).inst q' i' := by
              intro q' i'; rw [hs'eq]; rfl
            refine ⟨e1, e2, by rw [hs'eq]; exact e3, by rw [hs'eq]; exact e4, Hpm''.1, Hpm''.2,
              ?_, ?_, ?_, ?_, by rw [hs'eq]; exact e11⟩
            · intro q' i' hb'
              rw [hkey, ← e7 q' i' hb']
              split
              · rename_i hh; rw [hh.1, hh.2, hinst]; rfl
              · rfl
            · intro q' i' hb'
              rw [hkey]
              split
              · rename_i hh; rw [hh.1, hh.2, hib] at hb'; cases hb'
              · exact e8 q' i' hb'
            · intro n hn
              rw [hx2, List.mem_append, List.mem_singleton] at hn
              rcases hn with (hn | rfl) | hn
              · exact e9 n (.inl hn)
              · rw [HwM]; rfl
              · exact e9 n (.inr hn)
            · intro n hn
              rw [hx2, List.mem_append, List.mem_singleton] at hn
              unfold replica2.committedOrExecuted
              rw [hcoe]
              rcases hn with (hn | rfl) | hn
              · exact e10 n (.inl hn)
              · exact hwc
              · exact e10 n (.inr hn)
          ihave HLA : L.LA (tw ++ [.exec iw.Leader' iw.Slot']) (xsJ xsc Ls (sint.nat j + 1)) $$
              [HTH HPr HRs HPO HBt Hxs1 Hcu Hcrtv HM HMe Hrows Hinsts Hmono Hconfs Hconf Hpm Hrst]
          · iapply (L.LA_open ..).2
            rw [Hs']
            iframe
            iapply (epaxosOwnG_open ..).2
            iexists ispS', crtS', c1S', isp', msR', pvtR', cfs', M', cu', pm''
            iframe
            have hep3 := hep2
            rw [hs'eq] at hep3 ⊢; simp only [RState.setInst] at hep3 ⊢
            iframe; iframe #
            ipureintro; exact hep3
          imodintro
          wp_for_post
          iframe
          iexists (j + W64 1), (tw ++ [.exec iw.Leader' iw.Slot']), pw
          rw [hj1]
          iframe
          ipureintro
          refine ⟨by have := HJ.1; have := hjl; simp only [sint.nat, sint.Z] at *; word, by omega,
            HW.1.trans (List.prefix_append _ _), HW.2.trans (by rw [Hs']; exact hstab)⟩
      · -- after the loop: the component is executed, popped from the stack
        have hjL : sint.nat j = Ls.length := by
          have := HJ.1; have := HJ.2.1; rw [hlsl] at Hif
          simp only [sint.nat, sint.Z] at *; omega
        rw [hjL]
        have hxsL : (xsJ xsc Ls Ls.length).1 = xsc.1 ++ Ls := by simp [xsJ]
        have h0 : sint.Z (W64 0) = 0 := rfl
        have hSL : (S.length : Int) ≤ Sc.length := by rw [hSc]; simp; omega
        rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z s.len ∧
            sint.Z s.len ≤ sint.Z s2.cap by
          rw [h0, hSlen]; have := Hs2cap; have := hs2len; omega)]
        ihave ⟨HLA, %Hokf⟩ := L.LA_ok tj _ $$ HLA
        ihave Hcap := ownSlice_slice_absorb_capacity s2 ptrs' (W64 0) s.len
          ⟨by rw [h0]; exact Int.le_refl 0, by rw [h0, hSlen]; omega, by rw [hSlen, hs2len]; omega⟩
          $$ [Hsuf Hscap]
        · iframe
        wp_auto
        iapply HΦ
        iexists tj, (xsJ xsc Ls Ls.length), S, idxc
        iframe Hown HLA Hidx
        isplitl [Hxs Hsg Hpre Hcap Heu]
        · iapply (execPrivG_open ..).2
          iframe Hxs
          isplitl [Hsg Hpre Hcap]
          · ihave %Hprelen := ownSlice_len _ _ _ $$ Hpre
            iapply stackOwn_intro ρ.toR1 S (slice.slice s2 Loc (W64 0) s.len)
              (ptrs.take (sint.nat s.len)) (by rw [List.length_take, hSn, Hsf.1, hSc]; simp)
              (by simp only [slice.slice]; have := Hs2cap; have := Hsf.2; constructor <;> word)
            iframe
            rw [hSn]
            iapply stackElems_take ρ.toR1 S (vn :: T) ptrs
            rw [← hSc]; iframe #
          · iexists euS; iframe #; rw [hxsL]; iapply euOwn_mono euS xsc.1 Ls $$ Heu
        ipureintro
        have hstf := HJ.2.2.2
        have hSsub : ∀ u ∈ S, u ∈ Sc := fun u hu => by rw [hSc]; exact List.mem_append_left _ hu
        refine ⟨htc.trans HJ.2.2.1, ?_, ?_⟩
        · have hp := hpost Ls Hperm.symm
          have hσ : ({ xsc.toT Sc idxc with X := (xsc.toT Sc idxc).X ++ Ls, S := (xs.toT S idx).S } :
              TState) = (xsJ xsc Ls Ls.length).toT S idxc := by
            simp [XS.toT, xsJ]; exact ⟨rfl, rfl⟩
          rw [hσ] at hp
          exact Post.stable hstf (fun u hu => hFc.1.1 u (.inl (hSsub u hu))) hp
        · obtain ⟨⟨hC, -, vis, hnd, hlen, hb, hSv⟩, -⟩ := hFc
          refine ⟨⟨?_, fun n => (Hokf.1 n).symm, vis, hnd, hlen, hb, fun u hu => hSv u (hSsub u hu)⟩, ?_⟩
          · intro u hu
            rw [hxsL] at hu
            refine hstf.isSome ?_
            rcases hu with hu | hu
            · exact hC u (.inl (hSsub u hu))
            · rcases List.mem_append.1 hu with hu | hu
              · exact hC u (.inr hu)
              · exact hLsc u hu
          · rw [hxsL]
            refine XClosed.stable hstf (fun u hu => ?_) (fun x hx y hd => ?_)
            · rcases List.mem_append.1 hu with hu | hu
              · exact hXcm u hu
              · exact hLsc u hu
            · rcases List.mem_append.1 hx with hx | hx
              · exact List.mem_append_left _ (hXc x hx y hd)
              · rcases hLsscc.2.2.2.1 x hx y hd with h1 | h1
                · exact List.mem_append_left _ h1
                · exact List.mem_append_right _ h1
    · -- `v.Lowlink != v.Index`: `v` stays on the stack
      have hne : (xsc.toT Sc idxc).low vn ≠ (xsc.toT Sc idxc).num vn := by
        intro e; apply Hif
        have h1 := Hiv.2.2.2.2.2.2.2.2.2.2.1; have h2 := Hiv.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [XS.toT] at e
        apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at h1 h2; omega
      have hpost := hL.finish_keep hall hne
      ihave Hinsts := Hclose $$ %xsc %(stOf k tc) [] [] [Hvp Hvcmds Hvlb]
      · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
      · ipureintro; intro _ _ _; rfl
      · iexists cv; isplitr; · ipureintro; exact Hcv
        iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiv
      iapply HΦ
      iexists tc, xsc, Sc, idxc
      iframe Hown Hpriv Hidx
      isplitl
      · iapply (L.LA_open ..).2; iframe
        iapply (epaxosOwnG_open ..).2
        iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
        iframe; iframe #; ipureintro; exact Hep
      ipureintro
      exact ⟨htc, hpost, hFc⟩

end

end Perennial.gryff.X
