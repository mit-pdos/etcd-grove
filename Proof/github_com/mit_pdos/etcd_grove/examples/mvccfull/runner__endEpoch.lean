/- Lean-first (no Rocq counterpart). The proof of `runner.endEpoch`: proved.

Four loops over `m.streams`, then `m.streams = nil`: each stream's stop flag set (its counter
invariant); each registrar's end (`regDone.Wait()`: its `regOwn`, the stream now `epochStream1`);
each stream complete up to `m.rev` (`complete` until it says so, `time.Sleep`); each stream closed
(`Close`, by `close_au`: the registrar's half of the closed flag), its receiver's end
(`recvDone.Wait()`: its `rcvOwn`), a watch refused (`Watch` at `watch_closed_au`: the writer's live
share opens the incarnation's invariant for the store's state; `ErrEmptyWatcherRange`'s identity
from `errVars.law`), and a cancel refused (`Cancel` at `cancel_closed_au`, the receiver's `wsRecv` deposited in the
stream's invariant; `ErrWatcherNotExist`'s),
the stream's `epochTok` (its receiver's history slot and both goroutines' `epRd`) collected.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__endEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__complete
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.context.TODO
public import Perennial.Spec.time.Sleep
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EpochLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.endEpoch.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (_hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF))
    (_hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_stream_complete : stream.complete.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_runner_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    runner.endEpoch.spec (GF := GF) (hG := hG) := by
  intro E q qw sl ss rv Hlb hrv0 hrv1 hrv2
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : Persistent (epCtx (GF := GF) E) := by
    haveI := hpers.1; unfold epCtx rnCtx isInc ctrInv runnerKeys runnerH; infer_instance
  wp_start as ⟨#Hep, Hstr, Hsl, Hss, Hrev, Hhr, #Hlb, Hrdw, Hlive⟩
  ihave Hep2 := Hep
  iunfold epCtx at Hep2
  icases Hep2 with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hks, #Hh, #Hhist, #Hcfg, #Hwa, #Hwst, #Hc1, #Hc2,
    #Hc3, #Hc4⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  -- the first loop: each stream's stop flag set
  ihave HI : (∃ (i : w64) (sv : Loc), "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ sv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i s]
  · iexists W64 0, _; iframe; ipureintro; constructor <;> word
  wp_for HI
  by_cases Hlt : sint.Z i < sint.Z sl.len
  rotate_left
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    -- the second loop: each registrar's end
    ihave HI : (∃ (i2 : w64) (sv2 : Loc), "i" ∷ i_ptr ↦ i2 ∗ "s" ∷ s_ptr ↦ sv2 ∗
        "Hss1" ∷ ([∗list] s ∈ ss.take (sint.nat i2), epochStream1 E q s) ∗
        "Hss" ∷ ([∗list] s ∈ ss.drop (sint.nat i2), epochStream E q s) ∗
        "%Hi2" ∷ ⌜0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ sint.Z sl.len⌝ : IProp GF) $$ [i s Hss]
    · iexists W64 0, _
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
      iframe
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro; constructor <;> word
    wp_for HI
    by_cases Hlt2 : sint.Z i2 < sint.Z sl.len
    rotate_left
    · rw [decide_eq_false Hlt2]; simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      have hi2n : sint.nat i2 = ss.length := by rw [Hlen.1]; word
      rw [hi2n, List.take_length, List.drop_length]
      -- the third loop: each stream complete up to `m.rev`
      ihave HI : (∃ (i3 : w64) (sv3 : Loc), "i" ∷ i_ptr ↦ i3 ∗ "s" ∷ s_ptr ↦ sv3 ∗
          "Hss1" ∷ ([∗list] s ∈ ss, epochStream1 E q s) ∗ "Hrev" ∷ mF go!"rev" E.mp ↦ rv ∗
          "Hhr" ∷ histRd E.h E.γh ∗
          "%Hi3" ∷ ⌜0 ≤ sint.Z i3 ∧ sint.Z i3 ≤ sint.Z sl.len⌝ : IProp GF) $$ [i s Hss1 Hrev Hhr]
      · iexists W64 0, _
        iframe
        ipureintro; constructor <;> word
      wp_for HI
      by_cases Hlt3 : sint.Z i3 < sint.Z sl.len
      rotate_left
      · rw [decide_eq_false Hlt3]; simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        -- the fourth loop: each stream closed, its receiver's end, a watch and a cancel refused
        ihave HI : (∃ (i4 : w64) (sv4 : Loc), "i" ∷ i_ptr ↦ i4 ∗ "s" ∷ s_ptr ↦ sv4 ∗
            "Hss1" ∷ ([∗list] s ∈ ss.drop (sint.nat i4), epochStream1 E q s) ∗
            "Htoks" ∷ ([∗list] _x ∈ List.replicate (sint.nat i4) (), epochTok E q) ∗
            "%Hi4" ∷ ⌜0 ≤ sint.Z i4 ∧ sint.Z i4 ≤ sint.Z sl.len⌝ : IProp GF) $$ [i s Hss1]
        · iexists W64 0, _
          rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.replicate_zero]
          iframe
          isplitr
          · iapply BigSepL.bigSepL_nil.2; itrivial
          ipureintro; constructor <;> word
        wp_for HI
        by_cases Hlt4 : sint.Z i4 < sint.Z sl.len
        rotate_left
        · rw [decide_eq_false Hlt4]; simp only [Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          have hi4n : sint.nat i4 = ss.length := by rw [Hlen.1]; word
          rw [hi4n]
          iapply HΦ
          iframe
        rw [decide_eq_true Hlt4]; simp only [↓reduceIte]
        have hil4 : sint.nat i4 < ss.length := by rw [Hlen.1]; word
        list_elem ss (sint.nat i4) as sv4'
        have hb4 : 0 ≤ sint.Z i4 ∧ sint.Z i4 < sint.Z sl.len := ⟨Hi4.1, Hlt4⟩
        (try wp_auto)
        (try simp only [hb4, _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index sl (sint.Z i4) ss (DFrac.own 1) sv4' Hi4.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; exact Hsv4'_lookup
        (try wp_auto)
        rw [List.drop_eq_getElem_cons hil4]
        have hsv4 : ss[sint.nat i4] = sv4' := by
          rw [List.getElem?_eq_getElem hil4] at Hsv4'_lookup; exact Option.some.inj Hsv4'_lookup
        rw [hsv4]
        icases BigSepL.bigSepL_cons.1 $$ Hss1 with ⟨Hes, Hss1⟩
        iunfold epochStream1 at Hes
        icases Hes with ⟨%T, %hT, HT, Hrc, %C, Hrg⟩
        haveI := streamCtx_persistent hpers T
        icases HT with #HT
        obtain ⟨hTe, hTs⟩ := hT
        ihave HT2 := HT
        iunfold streamCtx at HT2
        icases HT2 with ⟨-, -, -, -, #HwsF, -, #Hws, #Hsinv, -, -⟩
        iunfold regOwn at Hrg
        icases Hrg with ⟨Hrd1, Hcl, Hcn⟩
        ihave %Hwsh := (hsh.2.2.2 T.ws T.ep.ι.kv T.σs.ws) $$ Hws
        obtain ⟨tyW, vW, hwsv, hWatch, -, -, -, hCancel, hClose, -⟩ := Hwsh
        rw [← hTs]
        rw [hwsv]
        (try wp_auto)
        wp_apply (hClose T.ep.ι.kv T.σs.ws (fun _ => ghostVar (GF := GF) T.σs.cl (1 : Qp).half true))
          $$ [Hcl] as ⟨%S1, Hcl⟩
        · iframe #
          iapply close_au hpers T.σs $$ [Hcl]
          iframe #; iframe
        (try wp_auto)
        ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
        · iPkgInit
        wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ (sF go!"recvDone" T.s))
          $$ [Hrc] as ⟨Hres, -⟩
        · iframe Hrc
        icases Hres with ⟨-, %rs, Hro⟩
        iunfold rcvOwn at Hro
        icases Hro with ⟨Hrd2, Hhr2, Hwr, Hrcv⟩
        (try wp_auto)
        wp_apply wp_ctxTODO
        (try wp_auto)
        wp_apply wp_runner_genKey E.x E.ks $$ [] as %sk ⟨%k, Hsk, %Hkin⟩
        · iframe #
        (try wp_auto)
        imod ownSlice_persist $$ Hsk with #Hsk
        ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
        ihave #Hflt : filtersImpl (GF := GF) slice.nil ([] : List (EvM → Bool)) $$ []
        · iunfold filtersImpl
          iexists []
          isplitl
          · iapply ownSlice_nil
          simp
          isplitl
          · itrivial
          · iempintro
        rw [hTe]
        wp_apply (hWatch E.ι.kv T.σs.ws todoCtxVal
            { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }
            sk slice.nil slice.nil k [] [] (W64 0)
            (fun _ S _ => iprop(epLive (GF := GF) E qw ∗ ghostVar T.σs.cl (1 : Qp).half true ∗
              ⌜S.closed = true⌝)))
          $$ [Hrdw Hlive Hcl] as %id %err ⟨Hrdw, Hres⟩
        · iframe #
          iframe Hrdw
          isplitl []
          · ileft; ipureintro; rfl
          isplitl []
          · ipureintro; decide
          iright
          iapply watch_closed_au hpers E qw T.σs k [] slice.nil (W64 0) [] $$ [Hlive Hcl]
          iframe #; iframe
        icases Hres with (⟨%Hc, -⟩ | ⟨-, %σ, %S, ⟨Hlive, Hcl, %HSc⟩, Herr⟩)
        · exfalso; simp at Hc
        simp only [HSc, ↓reduceIte]
        icases Herr with #Herr
        ihave Hinit := errVars $$ Hmpkg
        icases Hinit with ⟨-, -, #HeEmp, #HeNE, -⟩
        iunfold errorsNewVar at HeEmp
        icases HeEmp with ⟨%xe, #HeEmp, -⟩
        ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Herr HeEmp
        subst Hag
        (try wp_auto)
        wp_apply wp_check
        · ipureintro; simp
        (try wp_auto)
        wp_apply (hCancel E.ι.kv T.σs.ws (W64 0)
            (fun S => iprop(ghostVar (GF := GF) T.σs.cl (1 : Qp).half true ∗ ⌜S.closed = true⌝)))
          $$ [Hcl Hwr] as %err2 ⟨%S2, ⟨Hcl, %HS2⟩, Hres2⟩
        · iframe #
          iapply cancel_closed_au hpers T.σs (W64 0) rs $$ [Hcl Hwr]
          iframe #; iframe
        icases Hres2 with (%Hc2 | ⟨-, #Herr2⟩)
        · exfalso; rw [HS2] at Hc2; exact absurd Hc2.2.2 (by decide)
        iunfold errorsNewVar at HeNE
        icases HeNE with ⟨%xn, #HeNE, -⟩
        ihave %Hag2 := typedPointsto_agree_wand _ _ _ _ _ $$ Herr2 HeNE
        subst Hag2
        (try wp_auto)
        wp_apply wp_check
        · ipureintro; simp
        (try wp_auto)
        ihave Htoks : ([∗list] _x ∈ List.replicate (sint.nat i4 + 1) (), epochTok (GF := GF) E q)
          $$ [Htoks Hhr2 Hrd1 Hrd2]
        · rw [List.replicate_succ']
          iapply BigSepL.bigSepL_append.2
          iframe Htoks
          iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
          iunfold epochTok
          iframe
        wp_for_post
        iframe
        iexists i4 + W64 1, T.s
        have hi41 : sint.nat (i4 + W64 1) = sint.nat i4 + 1 := by word
        rw [hi41]
        iframe
        ipureintro; constructor <;> word
      rw [decide_eq_true Hlt3]; simp only [↓reduceIte]
      have hil3 : sint.nat i3 < ss.length := by rw [Hlen.1]; word
      list_elem ss (sint.nat i3) as sv3'
      have hb3 : 0 ≤ sint.Z i3 ∧ sint.Z i3 < sint.Z sl.len := ⟨Hi3.1, Hlt3⟩
      (try wp_auto)
      (try simp only [hb3, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index sl (sint.Z i3) ss (DFrac.own 1) sv3' Hi3.1 $$ [Hsl] as Hsl
      · iframe; ipureintro; exact Hsv3'_lookup
      (try wp_auto)
      have hset3 : ss.set (sint.nat i3) sv3' = ss := by
        apply List.ext_getElem?; intro n; rw [List.getElem?_set]
        split
        · rename_i h; subst h; rw [Hsv3'_lookup]
        · rfl
      icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ s => epochStream1 (GF := GF) E q s)
        Hsv3'_lookup).1 $$ Hss1 with ⟨Hes, Hss1⟩
      icases epochStream1_ctx hpers E q sv3' $$ Hes with ⟨Hes, %T, %hT, HT⟩
      haveI := streamCtx_persistent hpers T
      icases HT with #HT
      ispecialize Hss1 $$ %sv3' Hes
      rw [hset3]
      obtain ⟨hTe, hTs⟩ := hT
      have hcomp := wp_stream_complete T Hlb rv
      rw [hTe] at hcomp
      have hcomp' := hcomp hrv0 hrv1 hrv2
      clear hcomp
      rw [← hTs]
      ihave IH : (True : IProp GF) $$ []
      · itrivial
      wp_for IH
      wp_apply hcomp' $$ [Hhr] as %b Hhr
      · iframe #; iframe
      cases b
      · simp only [Bool.not_false, _root_.decide_true, ↓reduceIte]
        (try wp_auto)
        wp_apply wp_Sleep
        wp_for_post
        iframe
      · have Hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
        simp only [Bool.not_true, decide_eq_false Hft, Bool.false_eq_true, _root_.decide_true,
          ↓reduceIte]
        (try wp_auto)
        wp_for_post
        iframe
        iexists i3 + W64 1, T.s
        iframe
        ipureintro; constructor <;> word
    rw [decide_eq_true Hlt2]; simp only [↓reduceIte]
    have hil2 : sint.nat i2 < ss.length := by rw [Hlen.1]; word
    list_elem ss (sint.nat i2) as sv2'
    have hb2 : 0 ≤ sint.Z i2 ∧ sint.Z i2 < sint.Z sl.len := ⟨Hi2.1, Hlt2⟩
    (try wp_auto)
    (try simp only [hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z i2) ss (DFrac.own 1) sv2' Hi2.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hsv2'_lookup
    (try wp_auto)
    rw [List.drop_eq_getElem_cons hil2]
    have hsv2 : ss[sint.nat i2] = sv2' := by
      rw [List.getElem?_eq_getElem hil2] at Hsv2'_lookup; exact Option.some.inj Hsv2'_lookup
    rw [hsv2]
    icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hes, Hss⟩
    iunfold epochStream at Hes
    icases Hes with ⟨%T, %hT, HT, Hrg, Hrc⟩
    haveI := streamCtx_persistent hpers T
    icases HT with #HT
    obtain ⟨hTe, hTs⟩ := hT
    ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ (sF go!"regDone" sv2'))
      $$ [Hrg] as ⟨Hres, -⟩
    · iframe Hrg
    icases Hres with ⟨-, Hres⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists i2 + W64 1, sv2'
    iframe
    have hi21 : sint.nat (i2 + W64 1) = sint.nat i2 + 1 := by word
    rw [hi21, List.take_add_one, List.getElem?_eq_getElem hil2, hsv2]
    simp only [Option.toList_some]
    isplitl [Hss1 HT Hrc Hres]
    · iapply BigSepL.bigSepL_append.2
      iframe Hss1
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      iunfold epochStream1
      iexists T
      iframe
      iframe #
      ipureintro; exact ⟨hTe, hTs⟩
    isplitl [Hss]
    · iexact Hss
    ipureintro; constructor <;> word
  rw [decide_eq_true Hlt]; simp only [↓reduceIte]
  have hil : sint.nat i < ss.length := by rw [Hlen.1]; word
  list_elem ss (sint.nat i) as sv'
  have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, Hlt⟩
  (try wp_auto)
  (try simp only [hb, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index sl (sint.Z i) ss (DFrac.own 1) sv' Hi.1 $$ [Hsl] as Hsl
  · iframe; ipureintro; exact Hsv'_lookup
  (try wp_auto)
  have hset : ss.set (sint.nat i) sv' = ss := by
    apply List.ext_getElem?; intro n; rw [List.getElem?_set]
    split
    · rename_i h; subst h; rw [Hsv'_lookup]
    · rfl
  icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ s => epochStream (GF := GF) E q s)
    Hsv'_lookup).1 $$ Hss with ⟨Hes, Hss⟩
  icases epochStream_ctx hpers E q sv' $$ Hes with ⟨Hes, %T, %hT, HT⟩
  haveI := streamCtx_persistent hpers T
  icases HT with #HT
  ispecialize Hss $$ %sv' Hes
  rw [hset]
  obtain ⟨hTe, hTs⟩ := hT
  iunfold streamCtx at HT
  icases HT with ⟨-, -, -, -, -, -, -, -, -, #Hstop⟩
  rw [hTs]
  wp_apply_core sync.atomic.Int64.wp_Store (sF go!"stop" sv') (W64 1) $$ [] [-]
  · iPkgInit
  iunfold ctrInv at Hstop
  iinv Hstop with >Hi Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "stop") from
    Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  icases Hi with ⟨%v, Hi⟩
  iexists v
  iframe Hi
  iintro Hi
  imod Hcl with -
  imod Hclose $$ [Hi] with -
  · inext; iexists W64 1; iexact Hi
  imodintro
  (try wp_auto)
  wp_for_post
  iframe
  iexists i + W64 1, sv'
  iframe
  ipureintro; constructor <;> word

end proof

end mvccfull
end EtcdGrove
end Perennial
