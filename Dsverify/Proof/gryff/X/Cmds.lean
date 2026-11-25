/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Cmds.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: `findSCC`, `executeCommand`, `inStack` (generic `GF`)
-/
module

public import Dsverify.Proof.gryff.X.SC

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff.model (RState Copy Msg Ev Out committedCopy executedB inBox depR)
open Perennial.gryff.replica (XS Node TInv Post TState XClosed stackOwn euOwn stackOwn_open
  euOwn_open stackElems stackOwn_intro rowOwn rowOwn_open rows_acc wp_dlog_Printf)
open Perennial.gryff.replica2 (Repl2Names rid32 scFacts2)
open Perennial.gryff.pure (stOf)
open github_com.goose_lang.primitive (ProphId)

/-- The executor's invariant between searches: the visited instances are executed, the executed
set is closed under the dependencies (at state `s`). -/
def ExecInv (s : RState) (xs : XS) : Prop :=
  (∀ u, xs.numF u ≠ 0 → u ∈ xs.1) ∧ XClosed (depR s) xs.1

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : src.gryff.Assumptions]
variable [time_sem : time.Assumptions]
variable {k : Fin 3} {ρ : Repl2Names} {r h : Loc} {p : ProphId}

set_option goose.wp.extras true

/-- `findSCC(root)`: a search from an empty stack; the root is executed after it. -/
theorem wp_findSCC (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) (t : List Ev) (xs : XS)
    (S : List Node) (vn : Node) (v : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ L.isExecG gR mtx ex ∗
        sync.ownMutex mtx ∗ L.LA t xs ∗ execPrivG ρ h xs S ∗
        ghostMapElem ρ.ptrs vn DFrac.discard v ∗
        ⌜vn ∉ xs.1 ∧ (committedCopy (stOf k t) vn).isSome ∧ ExecInv (stOf k t) xs⌝ }}
      (App (Val (ex @!! go.GoType.PointerType src.gryff.Exec.ty @!! go!"findSCC")) (Val #v))
    {{ RET #true; ∃ (t' : List Ev) (xs' : XS),
        sync.ownMutex mtx ∗ L.LA t' xs' ∗ execPrivG ρ h xs' [] ∗
        ⌜t <+: t' ∧ vn ∈ xs'.1 ∧ xs.1 <+: xs'.1 ∧ ExecInv (stOf k t') xs'⌝ }} := by
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨#Hpkg, #Hfix, Hown, HLA, Hpriv, #Hv, %Hpre⟩
  wp_method_call
  wp_call
  icases (L.isExecG_open ..).1 $$ Hfix with ⟨#Hr, #Hh, #Hm, #Hpp, #HR, #Hex, #Hexr, #HId, #HN,
    #HSd, #Hlock, #Heo, #Hrec, #HInv, #Hdlog⟩
  icases (execPrivG_open ..).1 $$ Hpriv with ⟨Hxs, Hstk, %euS, #HeuS, Heu⟩
  icases (stackOwn_open ..).1 $$ Hstk with ⟨%s, %sptrs, Hsg, Hs, Hscap, %Hsf, #HSe⟩
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  ihave %Hscapwf := ownSliceCap_wf _ _ $$ Hscap
  wp_auto
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
      sint.Z (W64 0) ≤ sint.Z s.cap by have := Hscapwf; exact ⟨by decide, by decide, by word⟩)]
  icases (ownSlice_split_all (W64 0) s (DFrac.own 1) sptrs ⟨by decide, Hslen.2⟩).1 $$ Hs
    with ⟨Hs0, Hs⟩
  ihave Hcap := ownSlice_slice_absorb_capacity s _ (W64 0) (W64 0)
    ⟨by decide, by decide, Hslen.2⟩ $$ [Hs Hscap]
  · iframe
  wp_auto
  ihave ⟨HLA, %Hok⟩ := L.LA_ok t xs $$ HLA
  obtain ⟨hvX, hvc, hinv1, hXc⟩ := Hpre
  have hvn : xs.numF vn = 0 := Classical.byContradiction fun hne => hvX (hinv1 vn hne)
  ihave Hst : stackOwn ρ.toR1 [] $$ [Hsg Hcap Hs0]
  · iapply stackOwn_intro ρ.toR1 [] (slice.slice s Loc (W64 0) (W64 0)) []
      rfl (by simp only [slice.slice]; have := Hscapwf; have := Hsf.2; constructor <;> word)
    iframe
    unfold stackElems; iapply BigSepL.bigSepL_nil.2; itrivial
  wp_apply wp_sc L gR mtx ex t xs [] 1 [] vn v index_ptr $$ [Hown HLA Hxs Hst Heu index]
  · iframe #
    iframe
    isplitl
    · iapply (execPrivG_open ..).2; iframe; iframe #
    ipureintro
    refine ⟨TInv.start _ xs.1 xs.numF xs.lowF hinv1, hvX, hvn, hvc, ⟨?_, fun n => (Hok.1 n).symm,
      [], List.nodup_nil, rfl, by simp, by simp⟩, hXc⟩
    intro u hu
    rcases hu with hu | hu
    · simp at hu
    · exact executedB_isSome ((Hok.1 u).2 hu)
  iintro ⟨%t', %xs', %S', %idx', Hown, HLA, Hpriv, Hidx, %Hpost⟩
  obtain ⟨htp, hP, hF⟩ := Hpost
  obtain ⟨hS', hvX'⟩ := hP.root_popped rfl
  simp only [XS.toT] at hS' hvX'
  subst hS'
  wp_auto
  iapply HΦ
  iexists t', xs'
  iframe
  ipureintro
  refine ⟨htp, hvX', hP.Xpre, fun u hu => ?_, hF.2⟩
  exact Classical.byContradiction fun hX => by
    have := hP.inv.visited u hu hX
    simp [XS.toT] at this

/-- `executeCommand(q, i)`: `true` when instance `(q, i)` is executed after it. -/
theorem wp_executeCommand (L : ExecLaws (GF := GF) k ρ r h p) (gR mtx ex : Loc) (t : List Ev)
    (xs : XS) (q i : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ L.isExecG gR mtx ex ∗
        sync.ownMutex mtx ∗ L.LA t xs ∗ execPrivG ρ h xs [] ∗
        ⌜ExecInv (stOf k t) xs ∧ inBox q i = true⌝ }}
      (App (App (Val (ex @!! go.GoType.PointerType src.gryff.Exec.ty @!! go!"executeCommand"))
        (Val #q)) (Val #i))
    {{ (b : Bool), RET #b; ∃ (t' : List Ev) (xs' : XS),
        sync.ownMutex mtx ∗ L.LA t' xs' ∗ execPrivG ρ h xs' [] ∗
        ⌜t <+: t' ∧ xs.1 <+: xs'.1 ∧ ExecInv (stOf k t') xs' ∧
          (b = true → (sint.Z q, sint.Z i) ∈ xs'.1)⌝ }} := by
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨#Hpkg, #Hfix, Hown, HLA, Hpriv, %Hpre⟩
  obtain ⟨hinv, hib⟩ := Hpre
  wp_method_call
  wp_call
  icases (L.isExecG_open ..).1 $$ Hfix with ⟨#Hr, #Hh, #Hm, #Hpp, #HR, #Hex, #Hexr, #HId, #HN,
    #HSd, #Hlock, #Heo, #Hrec, #HInv, #Hdlog⟩
  icases (L.LA_open ..).1 $$ HLA with ⟨HTH, HPr, HRs, HEP, Hxs1, HPO, HBt⟩
  ihave ⟨HEP, %Hok⟩ := epaxosOwnG_ok ρ h r xs (stOf k t) $$ HEP
  icases (epaxosOwnG_open ..).1 $$ HEP with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M,
    %cu, %pm, #HhR, #HnoC, #HIS, #Hisp, #Hcrt, #Hc1, #Hc1s, #Hms, #Hpvt, Hcu, Hcrtv, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hconf, Hpm, Hrst, %Hep⟩
  wp_auto
  have hq3 : 0 ≤ sint.Z q ∧ sint.Z q < 3 ∧ 0 ≤ sint.Z i ∧ sint.Z i < model.SLOTS := by
    simpa [inBox] using hib
  rw [show model.SLOTS = 2 * 1024 * 1024 from rfl] at hq3
  have hqw : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
  have hiw : sint.Z (W64 (sint.Z i)) = sint.Z i := by word
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
  have hqn : (sint.Z (W64 (sint.Z q))).toNat < isp.length := by rw [hqw, Hep.1]; omega
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z (W64 (sint.Z q))).toNat]? = some sq :=
    ⟨_, List.getElem?_eq_getElem hqn⟩
  have hql : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z ispS.len := by
    rw [hqw]; have := HispSlen.1; rw [Hep.1] at this; have h3 := hq3
    simp only [sint.nat, sint.Z] at this h3 ⊢; omega
  rw [ite_eq_left hql]
  wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
  · ipureintro; exact hsq
  icases rows_acc M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
  icases (rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
  have hil : 0 ≤ sint.Z (W64 (sint.Z i)) ∧ sint.Z (W64 (sint.Z i)) < sint.Z sq.len := by
    rw [hiw]; have := Hrowlen.1; rw [Hrowf.1] at this; unfold replica.nSlots at this
    have h3 := hq3; simp only [sint.nat, sint.Z] at this h3 ⊢; omega
  rw [ite_eq_left hil]
  obtain ⟨pw, hp⟩ : ∃ p, ptrs[(sint.Z (W64 (sint.Z i))).toNat]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf.1]; unfold replica.nSlots; omega)⟩
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
  · ipureintro; exact hp
  have hMp := Hrowf.2 _ pw hp
  have hwn : (((sint.Z (W64 (sint.Z q))).toNat : Nat) : Int) = sint.Z q ∧
      (((sint.Z (W64 (sint.Z i))).toNat : Nat) : Int) = sint.Z i := by
    rw [hqw, hiw]; omega
  rw [hwn.1, hwn.2] at hMp
  wp_if_destruct
  · -- no instance yet
    ihave Hrows := Hrows $$ [Hrow]
    · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
    iapply HΦ
    iexists t, xs
    iframe Hown Hpriv
    isplitl
    · iapply (L.LA_open ..).2; iframe
      iapply (epaxosOwnG_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
      iframe; iframe #; ipureintro; exact Hep
    ipureintro
    refine ⟨List.prefix_refl _, List.prefix_refl _, hinv, ?_⟩
    intro hf; cases hf
  · -- the instance
    simp only [Hif, ite_false] at hMp
    rw [ite_eq_left hql]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
      ispS _ isp _ sq (by have := hqw; omega) $$ [$Hisp] as -
    · ipureintro; exact hsq
    rw [ite_eq_left hil]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
      sq _ ptrs _ pw (by have := hiw; omega) $$ [$Hrow] as Hrow
    · ipureintro; exact hp
    ihave Hrows := Hrows $$ [Hrow]
    · iapply (rowOwn_open ..).2; iexists ptrs; iframe; ipureintro; exact Hrowf
    icases instsG_upd ρ xs (stOf k t) M (sint.Z q, sint.Z i) pw hMp $$ Hinsts with
      ⟨⟨%c, %Hc, Hwi⟩, Hclose⟩
    icases (copyRepG_open ..).1 $$ Hwi with ⟨%iw, Hwp, Hwcm, Hwlb, %Hiw⟩
    wp_auto
    wp_if_destruct
    · -- executed already
      have hX : (sint.Z q, sint.Z i) ∈ xs.1 := Hiw.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [← Hiw.2.1]; exact Hif)
      ihave Hinsts := Hclose $$ %xs %(stOf k t) [] [] [Hwp Hwcm Hwlb]
      · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
      · ipureintro; intro _ _ _; rfl
      · iexists c; isplitr; · ipureintro; exact Hc
        iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiw
      iapply HΦ
      iexists t, xs
      iframe Hown Hpriv
      isplitl
      · iapply (L.LA_open ..).2; iframe
        iapply (epaxosOwnG_open ..).2
        iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
        iframe; iframe #; ipureintro; exact Hep
      ipureintro
      refine ⟨List.prefix_refl _, List.prefix_refl _, hinv, ?_⟩
      intro _; exact hX
    · wp_if_destruct
      · -- committed: the search from it
        have hst : c.status = model.St.COMMITTED := by
          rw [← Hiw.2.1]; have := Hif; simp at this; exact this
        have hqq : BitVec.ofInt 32 (sint.Z q) = q := BitVec.ofInt_toInt
        have hii : BitVec.ofInt 32 (sint.Z i) = i := BitVec.ofInt_toInt
        have hcc : committedCopy (stOf k t) (sint.Z q, sint.Z i) = some c := by
          unfold committedCopy
          rw [if_pos (show 0 ≤ sint.Z q ∧ sint.Z q < 3 ∧ 0 ≤ sint.Z i ∧ sint.Z i < model.SLOTS from
            ⟨hq3.1, hq3.2.1, hq3.2.2.1, by unfold model.SLOTS; omega⟩)]
          simp only [hqq, hii] at Hc ⊢; rw [Hc]; simp [hst]
        have hnX : (sint.Z q, sint.Z i) ∉ xs.1 := by
          intro hX; have := (Hiw.2.2.2.2.2.2.2.2.2.2.2.2).2 hX; rw [hst] at this; cases this
        ihave Hinsts := Hclose $$ %xs %(stOf k t) [] [] [Hwp Hwcm Hwlb]
        · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
        · ipureintro; intro _ _ _; rfl
        · iexists c; isplitr; · ipureintro; exact Hc
          iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiw
        ihave ⟨HMe, #Hwe⟩ := ptrElems_committed ρ (stOf k t) M _ pw hMp
          (by unfold replica2.committedOrExecuted; rw [hcc]; rfl) $$ HMe
        wp_apply wp_slice_literal (V := GoInterface) _
        isplitr
        · ipureintro; rfl
        iintro %_ ⟨-, -⟩
        wp_auto
        wp_apply wp_dlog_Printf $$ [$Hdlog]
        ihave HLA : L.LA t xs $$ [HTH HPr HRs Hxs1 HPO HBt Hcu Hcrtv HM HMe Hrows Hinsts Hmono
            Hconfs Hconf Hpm Hrst]
        · iapply (L.LA_open ..).2; iframe
          iapply (epaxosOwnG_open ..).2
          iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
          iframe; iframe #; ipureintro; exact Hep
        wp_apply wp_findSCC L gR mtx ex t xs [] (sint.Z q, sint.Z i) pw $$ [Hown HLA Hpriv]
        · iframe; iframe #; ipureintro; exact ⟨hnX, by rw [hcc]; rfl, hinv⟩
        iintro ⟨%t', %xs', Hown, HLA, Hpriv, %Hp⟩
        wp_auto
        iapply HΦ
        iexists t', xs'
        iframe
        ipureintro
        exact ⟨Hp.1, Hp.2.2.1, Hp.2.2.2, fun _ => Hp.2.1⟩
      · -- not committed
        ihave Hinsts := Hclose $$ %xs %(stOf k t) [] [] [Hwp Hwcm Hwlb]
        · ipureintro; intro _ _; exact ⟨rfl, rfl, Iff.rfl⟩
        · ipureintro; intro _ _ _; rfl
        · iexists c; isplitr; · ipureintro; exact Hc
          iapply (copyRepG_open ..).2; iexists _; iframe; ipureintro; exact Hiw
        iapply HΦ
        iexists t, xs
        iframe Hown Hpriv
        isplitl
        · iapply (L.LA_open ..).2; iframe
          iapply (epaxosOwnG_open ..).2
          iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
          iframe; iframe #; ipureintro; exact Hep
        ipureintro
        refine ⟨List.prefix_refl _, List.prefix_refl _, hinv, ?_⟩
        intro hf; cases hf

end

end Perennial.gryff.X
