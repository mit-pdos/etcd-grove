/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__logInfo.lean`. Lean-first (no Rocq
counterpart); traceutil-log (2026-11-23). The first loop merges each subtrace's fields into its
steps' (`append`, in place or not: the steps' fields are tracked as slices of regions,
`LogLemmas.lean`); the second formats the steps longer than the threshold (`writeFields` of a
region's slice, `fmt.Sprintf` of the message, the fields and the duration, a `time.Duration` whose
`String()` Perennial proves); then the zap fields.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__logInfo
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.writeFields
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.LogLemmas
public import Spec.math.rand.Int31
public import Spec.go_uber_org.zap.Int32
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Time
public import Spec.go_uber_org.zap.Strings
public import Spec.go_uber_org.zap.Int
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode _root_.Perennial.go_etcd_io.etcd.pkg.v3

/-- `logInfo`'s step format. -/
private abbrev stepFmt : GoString := go!"'%v' %s (duration: %v)"

set_option maxRecDepth 20000 in
private theorem fmtDirectives_stepFmt :
    _root_.Perennial.fmt.fmtDirectives stepFmt =
      some [⟨W8 118, false⟩, ⟨W8 115, false⟩, ⟨W8 118, false⟩] := by
  decide

section args
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

open _root_.Perennial.fmt in
/-- A string, under any directive. -/
private theorem argOkAt_string (mv : List w8) (dd : Directive) (x : GoString) :
    ⊢ argOkAt (GF := GF) mv dd (interface.mkOk go.string #x) := by
  unfold argOkAt; ileft; ipureintro
  exact EtcdGrove.fmt.argWf_of_argsWf (ArgsWf.cons_string x [] ArgsWf.nil)

open _root_.Perennial.fmt in
/-- `%v` of a `time.Duration`: its `String()`. -/
private theorem argOkAt_duration_v (x : time.Duration) :
    ⊢ argOkAt (GF := GF) methodVerbs ⟨W8 118, false⟩ (interface.mkOk time.Duration.ty #x) := by
  unfold argOkAt
  iright; iright; ileft
  isplitr
  · ipureintro; refine ⟨by decide, rfl, fun h => absurd h (by decide)⟩
  unfold argOk
  iright; iright
  isplitr
  · unfold stringMethodSpec
    imodintro
    iintro %Φ HΦ
    wp_apply _root_.Perennial.time.Duration.wp_String x as %s -
    iapply HΦ
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Error")
    have h3 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"String")
    have h4 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"CanInterface")
    simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3 h4
    refine ⟨by simpa using h1, by simpa using h2, by simpa [noArgStringSig] using h3,
      by simpa using h4⟩

end args

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.logInfo.wp_proof
    (hWF : traceutil.writeFields.spec (GF := GF) (hG := hG))
    (hRand : rand.Int31.spec (GF := GF) (hG := hG))
    (hZInt32 : zap.Int32.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZDur : zap.Duration.spec (GF := GF) (hG := hG))
    (hZTime : zap.Time.spec (GF := GF) (hG := hG))
    (hZStrings : zap.Strings.spec (GF := GF) (hG := hG))
    (hZInt : zap.Int'.spec (GF := GF) (hG := hG)) :
    traceutil.Trace.logInfo.spec (GF := GF) (hG := hG) := by
  intro t e d
  wp_start as Ht
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He, #Hlz⟩
  icases traceutil.regions_of_steps ss $$ Hsf with ⟨%regs, Hregs, %Hin⟩
  have Hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
  wp_auto
  wp_apply time.wp_Now as %now -
  (try wp_auto)
  wp_apply _root_.Perennial.time.Time.wp_ptr_Sub $$ endTime as %tot endTime
  (try wp_auto)
  wp_apply hRand as %tn -
  (try wp_auto)
  ihave %Hssl := ownSlice_len $$ Hss
  ihave IH1 : iprop(∃ (i : w64) (ss' : List traceutil.step) (regs' : List (GoSlice × Nat)),
      "i" ∷ i_ptr ↦ i ∗ "t" ∷ t_ptr ↦ t ∗ "Ht" ∷ t ↦ v ∗ "Hss" ∷ v.steps' ↦* ss' ∗
      "Hregs" ∷ ([∗list] r ∈ regs', traceutil.regionOwn r) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.steps'.len ∧ ss'.length = ss.length ∧
        (∀ st ∈ ss', traceutil.sliceIn regs' st.fields')⌝) $$ [i t Ht Hss Hregs]
  · iexists W64 0, ss, regs
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, Hssl.2, by simp, Hin⟩
  wp_for IH1
  wp_if_destruct
  · obtain ⟨Hi0, Hi1, Hi2, Hi3⟩ := Hi
    have Hif : sint.Z i < sint.Z v.steps'.len := by simpa using Hif
    have Hlt : sint.nat i < ss'.length := by rw [Hi2, Hssl.1]; word
    obtain ⟨tst, Htst⟩ : ∃ x, ss'[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v.steps'.len := ⟨Hi0, Hif⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index v.steps' (sint.Z i) ss' (DFrac.own 1) tst Hi0 $$ [Hss] as Hss
    · iframe; ipureintro; exact Htst
    (try wp_auto)
    have HtIn : traceutil.sliceIn regs' tst.fields' := Hi3 tst (List.mem_of_getElem? Htst)
    cases hs : tst.isSubTraceStart'
    · (try wp_auto)
      cases he : tst.isSubTraceEnd'
      · (try wp_auto)
        wp_for_post
        iframe
        iexists i + W64 1, ss', regs'
        simp only [named]
        iframe
        ipureintro; exact ⟨by word, by word, Hi2, Hi3⟩
      · (try wp_auto)
        ihave IH3 : iprop(∃ (j : w64) (s2 : List traceutil.step) (r2 : List (GoSlice × Nat)),
            "j" ∷ j_ptr ↦ j ∗ "t" ∷ t_ptr ↦ t ∗ "Ht" ∷ t ↦ v ∗ "Hss" ∷ v.steps' ↦* s2 ∗
            "Hregs" ∷ ([∗list] r ∈ r2, traceutil.regionOwn r) ∗
            "%Hj" ∷ ⌜-1 ≤ sint.Z j ∧ sint.Z j < sint.Z v.steps'.len ∧ s2.length = ss.length ∧
              (∀ st ∈ s2, traceutil.sliceIn r2 st.fields') ∧ traceutil.sliceIn r2 tst.fields'⌝)
            $$ [j t Ht Hss Hregs]
        · iexists _, ss', regs'
          simp only [named]
          iframe
          ipureintro; exact ⟨by word, by word, Hi2, Hi3, HtIn⟩
        wp_for IH3
        obtain ⟨Hj0, Hjl, Hj1, Hj2, Hj3⟩ := Hj
        wp_if_destruct
        · have Hj0' : 0 ≤ sint.Z j := by simpa using Hif
          have Hlt : sint.nat j < s2.length := by rw [Hj1, Hssl.1]; word
          obtain ⟨sj, Hsj⟩ : ∃ x, s2[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
          have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.steps'.len := ⟨Hj0', Hjl⟩
          (try wp_auto)
          (try rw [ite_eq_left Hbnd])
          icases ownSlice_elem_acc (sint.Z j) sj v.steps' _ s2 Hj0' Hsj $$ Hss with ⟨Hel, Hback⟩
          (try wp_auto)
          cases hjs : sj.isSubTraceStart'
          · simp only [Bool.not_false, decide_true, ↓reduceIte]
            (try wp_auto)
            (try rw [ite_eq_left Hbnd])
            (try wp_auto)
            wp_apply traceutil.wp_region_append r2 tst.fields' sj.fields' Hj3
              (Hj2 sj (List.mem_of_getElem? Hsj)) $$ Hregs as %s' ⟨%r3, Hregs, %Hr3⟩
            (try wp_auto)
            (try rw [ite_eq_left Hbnd])
            (try wp_auto)
            ihave Hss := Hback $$ Hel
            wp_for_post
            iframe
            iexists j - W64 1, _, r3
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, by simp [Hj1], ?_, traceutil.sliceIn_mono Hr3.1 Hj3⟩
            exact traceutil.steps_set_in Hr3.1 Hj2 _ _ Hr3.2
          · simp only [Bool.not_true, Hft, decide_false, Bool.false_eq_true, ↓reduceIte]
            (try wp_auto)
            (try simp only [decide_true, ↓reduceIte])
            (try wp_auto)
            ihave Hss := Hback $$ Hel
            rw [traceutil.list_set_self (show s2[(sint.Z j).toNat]? = some sj from Hsj)]
            wp_for_post
            iframe
            iexists i + W64 1, s2, r2
            simp only [named]
            iframe
            ipureintro; exact ⟨by word, by word, Hj1, Hj2⟩
        · (try wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, s2, r2
          simp only [named]
          iframe
          ipureintro; exact ⟨by word, by word, Hj1, Hj2⟩
    · (try wp_auto)
      ihave IH2 : iprop(∃ (j : w64) (s2 : List traceutil.step) (r2 : List (GoSlice × Nat)),
          "j" ∷ j_ptr ↦ j ∗ "t" ∷ t_ptr ↦ t ∗ "Ht" ∷ t ↦ v ∗ "Hss" ∷ v.steps' ↦* s2 ∗
          "Hregs" ∷ ([∗list] r ∈ r2, traceutil.regionOwn r) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ s2.length = ss.length ∧
            (∀ st ∈ s2, traceutil.sliceIn r2 st.fields') ∧ traceutil.sliceIn r2 tst.fields'⌝)
          $$ [j t Ht Hss Hregs]
      · iexists _, ss', regs'
        simp only [named]
        iframe
        ipureintro; exact ⟨by word, Hi2, Hi3, HtIn⟩
      wp_for IH2
      obtain ⟨Hj0, Hj1, Hj2, Hj3⟩ := Hj
      wp_if_destruct
      · have Hlt : sint.nat j < s2.length := by rw [Hj1, Hssl.1]; word
        obtain ⟨sj, Hsj⟩ : ∃ x, s2[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.steps'.len := ⟨Hj0, Hif⟩
        (try wp_auto)
        (try rw [ite_eq_left Hbnd])
        icases ownSlice_elem_acc (sint.Z j) sj v.steps' _ s2 Hj0 Hsj $$ Hss with ⟨Hel, Hback⟩
        (try wp_auto)
        cases hje : sj.isSubTraceEnd'
        · simp only [Bool.not_false, decide_true, ↓reduceIte]
          (try wp_auto)
          (try rw [ite_eq_left Hbnd])
          (try wp_auto)
          wp_apply traceutil.wp_region_append r2 tst.fields' sj.fields' Hj3
            (Hj2 sj (List.mem_of_getElem? Hsj)) $$ Hregs as %s' ⟨%r3, Hregs, %Hr3⟩
          (try wp_auto)
          (try rw [ite_eq_left Hbnd])
          (try wp_auto)
          ihave Hss := Hback $$ Hel
          wp_for_post
          iframe
          iexists j + W64 1, _, r3
          simp only [named]
          iframe
          ipureintro
          refine ⟨by word, by simp [Hj1], ?_, traceutil.sliceIn_mono Hr3.1 Hj3⟩
          exact traceutil.steps_set_in Hr3.1 Hj2 _ _ Hr3.2
        · simp only [Bool.not_true, Hft, decide_false, Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          simp only [decide_true, ↓reduceIte]
          (try wp_auto)
          ihave Hss := Hback $$ Hel
          rw [traceutil.list_set_self (show s2[(sint.Z j).toNat]? = some sj from Hsj)]
          wp_for_post
          iframe
          iexists i + W64 1, s2, r2
          simp only [named]
          iframe
          ipureintro; exact ⟨by word, by word, Hj1, Hj2⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists i + W64 1, s2, r2
        simp only [named]
        iframe
        ipureintro; exact ⟨by word, by word, Hj1, Hj2⟩
  · (try wp_auto)
    obtain ⟨Hi0, Hi1, Hi2, Hi3⟩ := Hi
    ihave IH4 : iprop(∃ (i : w64) (strs : List GoString) (sl : GoSlice) (lst : time.Time),
        "i" ∷ i_ptr ↦ i ∗ "t" ∷ t_ptr ↦ t ∗ "Ht" ∷ t ↦ v ∗ "Hss" ∷ v.steps' ↦* ss' ∗
        "Hregs" ∷ ([∗list] r ∈ regs', traceutil.regionOwn r) ∗
        "steps" ∷ steps_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* strs ∗
        "Hslc" ∷ ownSliceCap GoString sl (DFrac.own 1) ∗
        "lastStepTime" ∷ lastStepTime_ptr ↦ lst ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.steps'.len⌝)
        $$ [i t Ht Hss Hregs steps lastStepTime]
    · iexists W64 0, [], slice.nil, v.startTime'
      simp only [named]
      iframe
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro; exact ⟨by decide, Hssl.2⟩
    wp_for IH4
    wp_if_destruct
    · obtain ⟨Hk0, Hk1⟩ := Hi
      have Hif : sint.Z i < sint.Z v.steps'.len := by simpa using Hif
      have Hlt : sint.nat i < ss'.length := by rw [Hi2, Hssl.1]; word
      obtain ⟨tst, Htst⟩ : ∃ x, ss'[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v.steps'.len := ⟨Hk0, Hif⟩
      rw [ite_eq_left Hbnd]
      wp_apply wp_load_slice_index v.steps' (sint.Z i) ss' (DFrac.own 1) tst Hk0 $$ [Hss] as Hss
      · iframe; ipureintro; exact Htst
      (try wp_auto)
      have HtIn : traceutil.sliceIn regs' tst.fields' := Hi3 tst (List.mem_of_getElem? Htst)
      cases hs : tst.isSubTraceStart'
      · (try wp_auto)
        cases he : tst.isSubTraceEnd'
        · (try wp_auto)
          iStructNamed tstep
          wp_apply _root_.Perennial.time.Time.wp_ptr_Sub $$ time as %dur time
          (try wp_auto)
          wp_if_destruct
          · icases traceutil.region_read regs' tst.fields' HtIn $$ Hregs with ⟨%fs, Hf, %Hfwf, Hfb⟩
            wp_apply hWF tst.fields' fs (DFrac.own 1) $$ [Hf] as %wstr Hf
            · iframe #
              iframe
              ipureintro; exact Hfwf
            ihave Hregs := Hfb $$ Hf
            (try wp_auto)
            wp_apply wp_slice_literal (V := GoInterface)
              [interface.mkOk go.string #tst.msg', interface.mkOk go.string #wstr,
                interface.mkOk time.Duration.ty #dur]
            isplitr
            · ipureintro; rfl
            iintro %al ⟨Hal, -⟩
            (try wp_auto)
            wp_apply _root_.Perennial.fmt.wp_Sprintf stepFmt _ _ (DFrac.own 1) $$ [$Pfmt $Hal]
              as %str ⟨-, -⟩
            · iapply (_root_.Perennial.fmt.argsOk_intro fmtDirectives_stepFmt)
              simp only [_root_.Perennial.fmt.argsOkAt]
              isplitr; · iapply argOkAt_string
              isplitr; · iapply argOkAt_string
              isplitr; · iapply argOkAt_duration_v
              itrivial
            (try wp_auto)
            wp_apply wp_slice_literal (V := GoString) [str]
            isplitr
            · ipureintro; rfl
            iintro %sl2 ⟨Hsl2, -⟩
            (try wp_auto)
            wp_apply wp_slice_append (V := GoString) _ _ _ _ _ $$ [$Hsl $Hslc $Hsl2]
              as %sl3 ⟨Hsl, Hslc, -⟩
            (try wp_auto)
            wp_for_post
            iframe
            iexists i + W64 1, _, sl3, tst.time'
            simp only [named]
            iframe
            ipureintro; exact ⟨by word, by word⟩
          · (try wp_auto)
            wp_for_post
            iframe
            iexists i + W64 1, strs, sl, tst.time'
            simp only [named]
            iframe
            ipureintro; exact ⟨by word, by word⟩
        · (try wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, strs, sl, lst
          simp only [named]
          iframe
          ipureintro; exact ⟨by word, by word⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists i + W64 1, strs, sl, lst
        simp only [named]
        iframe
        ipureintro; exact ⟨by word, by word⟩
    · (try wp_auto)
      wp_apply hZInt32 as %f0 -
      (try wp_auto)
      wp_apply hZString as %f1 -
      (try wp_auto)
      iunfold traceutil.ownFields at Hfs
      icases Hfs with ⟨%tfs, Htf, Htfc, %Htfwf⟩
      wp_apply hWF v.fields' tfs (DFrac.own 1) $$ [Htf] as %dstr Htf
      · iframe #
        iframe
        ipureintro; exact Htfwf
      (try wp_auto)
      wp_apply hZString as %f2 -
      (try wp_auto)
      wp_apply hZDur as %f3 -
      (try wp_auto)
      wp_apply hZTime as %f4 -
      (try wp_auto)
      wp_apply hZTime as %f5 -
      (try wp_auto)
      wp_apply hZStrings as %f6 -
      (try wp_auto)
      wp_apply hZInt as %f7 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3, f4, f5, f6, f7]
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨-, -⟩
      (try wp_auto)
      iapply HΦ
      iexists v
      iframe
      iexact Hlz

end proof

end EtcdGrove
end Perennial
