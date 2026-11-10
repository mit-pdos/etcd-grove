/- Lean-first (no Rocq counterpart). The proof of `runner.startEpoch`: proved (the
incarnation's store a watchable store, which `NewWatchStream` needs: `EpochLemmas.inc_watchable`,
from `isInc`).

The callees in call order: `m.regs.Store(0)` (its counter invariant); per stream: `NewWatchStream`
(through `shapes.law`, at the watchable store), the stream's ghost state (`stream_alloc`), its lock
(`smu_alloc`), its stop flag's invariant, its two wait groups (`sync.join`, one `Add(1)` each, `P'`
the goroutine's resources); the receiver's goroutine (`recvOne`, `time.Sleep`, `Done` with its
`rcvOwn`), the registrar's (`stop.Load`, `act`, `time.Sleep`, `Done` with its `regOwn`); the
stream appended to `m.streams`. The loop's invariant takes one `epochTok` per iteration (its history
slot to the receiver, its two `epRd` to the goroutines) and gives one `epochStream`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__recvOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__act
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

theorem runner.startEpoch.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (_hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_stream_recvOne : stream.recvOne.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_stream_act : stream.act.spec (GF := GF) (hG := hG)) :
    runner.startEpoch.spec (GF := GF) (hG := hG) := by
  intro E q qw
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : Persistent (epCtx (GF := GF) E) := by
    haveI := hpers.1; unfold epCtx rnCtx isInc ctrInv runnerKeys runnerH; infer_instance
  wp_start as ⟨#Hep, Hkv, Hstr, Htoks⟩
  ihave Hep2 := Hep
  iunfold epCtx at Hep2
  icases Hep2 with ⟨Hrn, #Hinc, #Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, #Hkeys, %Hks, #Hh, #Hhist, #Hcfg, #Hwa, #Hwst, #Hc1, #Hc2,
    #Hc3, #Hc4⟩
  ihave %Hwatch := inc_watchable E $$ Hinc
  obtain ⟨sw, hsw⟩ := Hwatch
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"regs" E.mp) (W64 0) $$ [] [-]
  · iPkgInit
  iunfold ctrInv at Hregs
  iinv Hregs with >Hi Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "regs") from
    Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  icases Hi with ⟨%v, Hi⟩
  iexists v
  iframe Hi
  iintro Hi
  imod Hcl with -
  imod Hclose $$ [Hi] with -
  · inext; iexists W64 0; iexact Hi
  imodintro
  wp_auto
  iStructNamedSuffix Hcfg "F"
  iStructNamedSuffix MixF "M"
  ipersist x
  ipersist m
  ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave HI : (∃ (j : w64) (sl : GoSlice) (ss : List Loc),
      "j" ∷ j_ptr ↦ j ∗ "Hstr" ∷ mF go!"streams" E.mp ↦ sl ∗ "Hsl" ∷ sl ↦* ss ∗
      "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗ "Hkv" ∷ mF go!"kv" E.mp ↦{DFrac.own qw} E.kv ∗
      "Hss" ∷ ([∗list] s ∈ ss, epochStream E q s) ∗
      "Htoks" ∷ ([∗list] _x ∈ List.replicate ((sint.Z E.cfg.Streams').toNat - ss.length) (),
        epochTok E q) ∗
      "%Hj" ∷ ⌜ss.length = sint.nat j ∧ 0 ≤ sint.Z j ∧
        (sint.Z j ≤ sint.Z E.cfg.Streams' ∨ j = W64 0)⌝ : IProp GF)
      $$ [j Hstr Hnil Hcap0 Hkv Htoks]
  · iexists W64 0, slice.nil, []
    iframe
    isplitl [Hnil]
    · iexact Hnil
    isplitl [Hcap0]
    · iexact Hcap0
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨rfl, by decide, Or.inr rfl⟩
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z E.cfg.Streams'
  rotate_left
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    have hlen : ss.length = (sint.Z E.cfg.Streams').toNat := by
      rcases Hj with ⟨h1, h2, h3 | h3⟩
      · have : sint.nat j = (sint.Z j).toNat := rfl
        omega
      · subst h3
        have : sint.Z E.cfg.Streams' ≤ 0 := by have := Hlt; simp at this; omega
        have : sint.nat (W64 0) = 0 := rfl
        omega
    iframe
    ipureintro; exact hlen
  rw [decide_eq_true Hlt]; simp only [↓reduceIte]
  (try wp_auto)
  ihave Hinc2 := Hinc
  iunfold isInc at Hinc2
  icases Hinc2 with ⟨#Hmi, #Hkvm, %Hws⟩
  have hNWS := (hsh.2.1 sw).2 E.ι.kv
  rw [hsw]
  wp_auto
  wp_apply hNWS $$ [] as %wsv ⟨%ι, #Hws, HS, Hrcv⟩
  · iframe #
  rw [← hsw]
  clear hNWS
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %wm Hwm
  (try wp_auto)
  irename «$r0» => Hst
  generalize «$r0_ptr» = sp at *
  iStructNamedSuffix Hst "S"
  ipersist s
  ipersist xS
  ipersist mS
  ipersist kvS
  ipersist wsS
  ipersist watchersS
  -- one epoch token
  have hlt : ss.length < (sint.Z E.cfg.Streams').toNat := by
    have : sint.nat j = (sint.Z j).toNat := rfl
    omega
  rw [show (sint.Z E.cfg.Streams').toNat - ss.length =
    ((sint.Z E.cfg.Streams').toNat - (ss.length + 1)) + 1 by omega, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, Htoks⟩
  iunfold epochTok at Htok
  icases Htok with ⟨Hhr, Hrd1, Hrd2⟩
  -- the stream's ghost state, its lock, its stop flag
  imod stream_alloc ι $$ HS with ⟨%σs, %Hσs, #Hsinv, Hcl, Hcn, Hreg, Hrcv1, Hrcv2⟩
  subst Hσs
  imod smu_alloc ⟨E, sp, wsv, wm, σs⟩ $$ [muS Hwm orderS eventlessS Hreg Hrcv1] with #Hmu
  · iframe
  imod inv_alloc (sCtrN .@ "stop") ⊤
    (∃ v : w64, sync.atomic.ownInt64 (GF := GF) (sF go!"stop" sp) (DFrac.own 1) v) $$ [stopS]
    with #Hstop
  · inext; iexists W64 0
    rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact stopS
  haveI := streamCtx_persistent hpers ⟨E, sp, wsv, wm, σs⟩
  ihave #Hctx : streamCtx (GF := GF) ⟨E, sp, wsv, wm, σs⟩ $$ []
  · iunfold streamCtx
    iunfold ctrInv
    iframe #
  -- the wait groups
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ recvDoneS with ⟨%γrd, Hrdwg⟩
  imod sync.join.init _ γrd $$ Hrdwg with Hrdwg
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") _ $$ regDoneS with ⟨%γrg, Hrgwg⟩
  imod sync.join.init _ γrg $$ Hrgwg with Hrgwg
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  -- the receiver
  wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
    iprop(∃ rs, rcvOwn (GF := GF) ⟨E, sp, wsv, wm, σs⟩ q.half rs) _ _ (W32 0)) $$ [Hrdwg]
    as ⟨Hrdwg, Hrdone⟩
  · iframe; ipureintro; decide
  (try wp_auto)
  wp_apply wp_fork $$ [Hrdone Hrd2 Hhr Hrcv Hrcv2]
  · wp_auto
    ihave IH : (∃ rs : List WResp,
        rcvOwn (GF := GF) ⟨E, sp, wsv, wm, σs⟩ q.half rs : IProp GF) $$ [Hrd2 Hhr Hrcv Hrcv2]
    · iexists []; iunfold rcvOwn; iframe
    wp_for IH
    irename IH => Hr
    wp_apply (wp_stream_recvOne ⟨E, sp, wsv, wm, σs⟩ q.half rs) $$ [Hr] as %b ⟨%rs', Hr⟩
    · iframe #; iunfold rcvOwn; iexact Hr
    cases b
    · have Hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
      simp only [decide_eq_false Hft, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
        iprop(∃ rs, rcvOwn (GF := GF) ⟨E, sp, wsv, wm, σs⟩ q.half rs) _) $$ [Hrdone Hr]
      · iframe
      (try wp_auto)
      itrivial
    · simp only [_root_.decide_true, ↓reduceIte]
      (try wp_auto)
      wp_apply wp_Sleep
      wp_for_post
      iframe
      iexists rs'
      iframe
  (try wp_auto)
  -- the registrar
  wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
    iprop(∃ C, regOwn (GF := GF) ⟨E, sp, wsv, wm, σs⟩ q.half C) _ _ (W32 0)) $$ [Hrgwg]
    as ⟨Hrgwg, Hrgdone⟩
  · iframe; ipureintro; decide
  (try wp_auto)
  wp_apply wp_fork $$ [Hrgdone Hrd1 Hcl Hcn]
  · wp_auto
    ihave IH : (∃ C : List w64,
        regOwn (GF := GF) ⟨E, sp, wsv, wm, σs⟩ q.half C : IProp GF) $$ [Hrd1 Hcl Hcn]
    · iexists []; iunfold regOwn; iframe
    wp_for IH
    irename IH => Hr
    wp_apply_core sync.atomic.Int64.wp_Load (sF go!"stop" sp) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iinv Hstop with >Hi Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(sCtrN .@ "stop") from
      Std.LawfulSet.empty_subset)
    iintro Hcl2
    inext
    icases Hi with ⟨%v, Hi⟩
    iexists v
    iframe Hi
    iintro Hi
    imod Hcl2 with -
    imod Hclose $$ [Hi] with -
    · inext; iexists v; iexact Hi
    imodintro
    (try wp_auto)
    by_cases hv : v = W64 0
    · rw [decide_eq_true hv]
      simp only [_root_.decide_true, ↓reduceIte]
      (try wp_auto)
      wp_apply (wp_stream_act ⟨E, sp, wsv, wm, σs⟩ q.half C) $$ [Hr] as ⟨%C', Hr⟩
      · iframe #; iunfold regOwn; iexact Hr
      (try wp_auto)
      wp_apply wp_Sleep
      wp_for_post
      iframe
      iexists C'
      iframe
    · rw [decide_eq_false hv]
      have Hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
      simp only [decide_eq_false Hft, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
        iprop(∃ C, regOwn (GF := GF) ⟨E, sp, wsv, wm, σs⟩ q.half C) _) $$ [Hrgdone Hr]
      · iframe Hrgdone; iexists C; iunfold regOwn; iexact Hr
      (try wp_auto)
      itrivial
  (try wp_auto)
  wp_apply (wp_slice_literal (l := [sp]))
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hosl] as %sl' ⟨Hsl, Hcap, -⟩
  (try wp_auto)
  wp_for_post
  iframe
  iexists j + W64 1, sl', ss ++ [sp]
  iframe
  rw [List.length_append, List.length_singleton, show W32 0 + W32 1 = W32 1 from rfl]
  isplitl [Hrdwg Hrgwg]
  · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    iunfold epochStream
    iexists ⟨E, sp, wsv, wm, σs⟩
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iframe #
    iframe
  isplitl [Htoks]
  · iexact Htoks
  ipureintro
  obtain ⟨h1, h2, -⟩ := Hj
  refine ⟨?_, by word, Or.inl (by word)⟩
  rw [h1]; word

end proof

end mvccfull
end EtcdGrove
end Perennial
