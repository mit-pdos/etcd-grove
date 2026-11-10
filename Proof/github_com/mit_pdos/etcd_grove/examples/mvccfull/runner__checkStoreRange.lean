/- Lean-first (no Rocq counterpart). The proof of `runner.checkStoreRange`: Draft, to come.

The outline: `err == ErrCompacted` (`errVars.law`: mvcc's error variables are distinct
`errors.New` values) holds exactly in `rangeOutcomeC`'s compacted case; there `rangeRev σ.rev ro.Rev
< σ.crev ≤ σ.rev` (`reach_bounds`) makes the revision `ro.Rev`, positive, and `cmpHi_acc` at the
compaction revision's lower bound (`readQ`) bounds `cmpHi` above it. Otherwise (the live case;
`res ≠ null` rules out the context's), the result's revision is `σ.rev` (every case of
`rangeOutcome`), `inBounds` holds by `lo ≤ σ.rev` and `revHi_acc`, the snapshot extends `readQ`'s
lower bound, and `checkRangeAt` at `(σ.rev, clo)` takes `rangeOutcomeC_lower` and `hist_match`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkStoreRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.ReadLemmas
public import Perennial.Proof.sync.atomic.Link

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

theorem runner.checkStoreRange.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (herr : mvcc.api.errVars.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG)) :
    runner.checkStoreRange.spec (GF := GF) (hG := hG) := by
  intro x ks h γh i mp m ι kv qr lo clo q kk e dk de res err σ hlo hclo
  unfold runnerKeys runnerH
  wp_start as ⟨⟨%keys, #Hkeys, #Hks, %Hks⟩, #Hh, Hrd, Hlive, Hk, He, #HQ, %Hres, Hout, %Hlwf⟩
  ihave Hev := herr $$ Hpkg2
  icases Hev with ⟨#HeC, #HeF, -, -, #Hap⟩
  ihave #Hap1 := Hap $$ %go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted %go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev
  iunfold errorsNewVar at HeC
  icases HeC with ⟨%xc, #HeC, -⟩
  iunfold readQ at HQ
  icases HQ with ⟨%Hl, #Hlb, #Hrv, #Hcr, #Hnr, %Hq⟩
  obtain ⟨Hhist, Hreach, Hb⟩ := Hq
  obtain ⟨hl2, hc1, hc2⟩ := reach_bounds σ Hreach
  have hrv := rev_w64 σ Hb
  iunfold rangeOutcomeC at Hout
  icases Hout with (⟨%Hc, ⟨%ec, #Hec, %Herr⟩, Hr⟩ | ⟨%Hlive, Hout⟩)
  · -- compacted
    ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hec HeC
    subst Herr
    rw [Hag]
    have hpos : 0 < sint.Z q.ro'.Rev' ∧ sint.Z q.ro'.Rev' < σ.crev := by
      unfold rangeRev at Hc; split at Hc
      · rw [hrv] at Hc; omega
      · omega
    wp_auto
    simp only [show sint.Z (W64 0) < sint.Z q.ro'.Rev' from hpos.1, decide_true]
    wp_auto
    wp_apply_core sync.atomic.Int64.wp_Load (mF go!"cmpHi" mp) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    imod cmpHi_acc ks γh i mp m ι kv qr _ $$ [$Hlive $Hcr] with ⟨%vh, Hh', %Hvh, Hcl⟩
    imodintro
    inext
    iexists vh
    iframe Hh'
    iintro Hh'
    imod Hcl $$ Hh' with Hlive
    imodintro
    wp_auto
    wp_apply wp_check
    · ipureintro; simp only [decide_eq_true_eq]; omega
    simp only [Hres, decide_false, Bool.not_false]
    wp_auto
    wp_apply wp_check
    · itrivial
    try wp_auto
    iapply HΦ
    iframe
  · -- live
    icases outcome_acc res err σ.log (W64 (σ.rev : Int)) _ kk e q.ro' Hres $$ Hout
      with ⟨%v, Hr, %Hv, Hback, Herr⟩
    ihave #HerrNe : (⌜err = GoInterface.nil⌝ ∨ ∃ xf : Loc,
        ⌜err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xf ∧
          xf ≠ xc⌝ : IProp GF) $$ [Herr]
    · icases Herr with (%Hn | ⟨%ef, #Hef, %Hef⟩)
      · ileft; ipureintro; exact Hn
      iright
      iunfold errorsNewVar at HeF
      icases HeF with ⟨%xf, #HeF, -⟩
      ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hef HeF
      ihave Hap2 := Hap1 $$ []
      · ipureintro
        simp [mvcc.api.errVarNames, go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted,
          go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev]
      iunfold errVarApart at Hap2
      icases Hap2 with ⟨%e1, %e2, #H1, #H2, %Hne⟩
      ihave %Hag1 := typedPointsto_agree_wand _ _ _ _ _ $$ H1 HeC
      ihave %Hag2 := typedPointsto_agree_wand _ _ _ _ _ $$ H2 HeF
      iexists xf
      ipureintro
      refine ⟨by rw [Hef, Hag], ?_⟩
      rintro rfl
      apply Hne
      have := Hag1.trans Hag2.symm
      injection this
    icases HerrNe with (%Hn | %Hxf)
    rotate_left
    · obtain ⟨xf, rfl, hne⟩ := Hxf
      wp_auto
      simp only [hne, decide_false]
      wp_auto
      try simp only [Hres, decide_false, Bool.not_false]
      try wp_auto
      wp_apply wp_check
      · itrivial
      try wp_auto
      rw [Hv]
      have hlo' : sint.Z lo ≤ sint.Z (W64 (σ.rev : Int)) := by rw [hrv]; exact hlo
      wp_apply_core wp_inBounds lo (W64 (σ.rev : Int)) (mF go!"revHi" mp) _ hlo' $$ [] [-]
      · iPkgInit
      imod revHi_acc ks γh i mp m ι kv qr _ $$ [$Hlive $Hrv] with ⟨%vh, Hh', %Hvh, Hcl⟩
      imodintro
      inext
      iexists _, vh
      iframe Hh'
      isplitr
      · ipureintro; rw [hrv]; exact Hvh.1
      iintro Hh'
      imod Hcl $$ Hh' with Hlive
      imodintro
      wp_auto
      wp_apply (wp_snapshot h γh Hl) $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
      rw [Hv]
      ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
      · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
      ihave Hsts := statesP_statesAt ms Hs $$ Hst
      obtain ⟨c0, c1, c2⟩ := check_ok ks σ Hl Hs ms Hhist Hreach Hb Hpre.1 Hmlen (sint.Z clo)
      have hlog := logOk_read σ Hb Hreach Hlwf
      ihave Hout := Hback $$ Hr
      ihave Hout := rangeOutcomeC_lower res (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xf) σ.log (W64 (σ.rev : Int)) σ.crev (sint.Z clo) _ kk e
        q.ro' hclo Hlive $$ Hout
      wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs.map Prod.fst)
        (List.replicate Hs.length DFrac.discard) (W64 (σ.rev : Int)) clo q kk e dk de res
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xf) σ.log
        Hks.1 hlog c0 c1 c2) $$ [$Hks $Hms $Hsts $Hk $He $Hout] as ⟨-, -, -, Hk, He⟩
      · ipureintro; exact Hres
      try wp_auto
      iapply HΦ
      iframe
    · subst Hn
      wp_auto
      try simp only [Hres, decide_false, Bool.not_false]
      try wp_auto
      wp_apply wp_check
      · itrivial
      try wp_auto
      rw [Hv]
      have hlo' : sint.Z lo ≤ sint.Z (W64 (σ.rev : Int)) := by rw [hrv]; exact hlo
      wp_apply_core wp_inBounds lo (W64 (σ.rev : Int)) (mF go!"revHi" mp) _ hlo' $$ [] [-]
      · iPkgInit
      imod revHi_acc ks γh i mp m ι kv qr _ $$ [$Hlive $Hrv] with ⟨%vh, Hh', %Hvh, Hcl⟩
      imodintro
      inext
      iexists _, vh
      iframe Hh'
      isplitr
      · ipureintro; rw [hrv]; exact Hvh.1
      iintro Hh'
      imod Hcl $$ Hh' with Hlive
      imodintro
      wp_auto
      wp_apply (wp_snapshot h γh Hl) $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
      rw [Hv]
      ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
      · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
      ihave Hsts := statesP_statesAt ms Hs $$ Hst
      obtain ⟨c0, c1, c2⟩ := check_ok ks σ Hl Hs ms Hhist Hreach Hb Hpre.1 Hmlen (sint.Z clo)
      have hlog := logOk_read σ Hb Hreach Hlwf
      ihave Hout := Hback $$ Hr
      ihave Hout := rangeOutcomeC_lower res GoInterface.nil σ.log (W64 (σ.rev : Int)) σ.crev (sint.Z clo) _ kk e
        q.ro' hclo Hlive $$ Hout
      wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs.map Prod.fst)
        (List.replicate Hs.length DFrac.discard) (W64 (σ.rev : Int)) clo q kk e dk de res GoInterface.nil σ.log
        Hks.1 hlog c0 c1 c2) $$ [$Hks $Hms $Hsts $Hk $He $Hout] as ⟨-, -, -, Hk, He⟩
      · ipureintro; exact Hres
      try wp_auto
      iapply HΦ
      iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
