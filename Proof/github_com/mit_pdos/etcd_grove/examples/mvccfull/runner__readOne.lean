/- Lean-first (no Rocq counterpart). The proof of `runner.readOne`: Draft, to come.

The outline (member `i`'s part of `rdOwn`, its handles `isInc`, `isMvcc`'s shape by `shapes.law`):
the floors by `revLo_acc`/`cmpLo_acc` (`Int64.Load`), giving lower bounds `n ≥ lo`, `c ≥ clo + 1`;
`pick.specW` at `6` with `readMixOk` gives an alternative of positive weight, not `5`
(`readMixOk_ne5`). Each read's update is `reader_au` (`Q σ := ret share ∗ readQ σ ∗ n ≤ σ.rev ∧
c ≤ σ.crev + 1`), so the value read is in `[lo, ·]` and its ceiling (`inBounds` with
`revHi_acc`/`cmpHi_acc` at `readQ`'s lower bounds) holds:
- `Rev` (`KV.Rev.contract`: `W64 σ.rev`), `FirstRev` (`KV.FirstRev.contract`: `W64 σ.crev`,
  `-1 ≤ σ.crev`);
- a read transaction (`KV.Read.contract`, then `Txn.Rev`/`Txn.FirstRev` at `.read σ`): the bounds as
  above; the snapshot (`history.snapshot` from `readQ`'s lower bound) has the states up to `σ.rev`
  (`hist_match`); each `Txn.Range` gives `rangeOutcomeC` at `σ.log`, `σ.rev`, `σ.crev`, which is
  `checkRangeAt`'s premise at `(W64 σ.rev, W64 σ.crev)` (`txn.LogOk` from the range's `LogWf'` and
  `reach_bounds`); `Txn.End` returns the reader token;
- a read-only transaction: the same through `NewReadOnlyTxnWrite.spec` (`.read σ` kept), and
  `Txn.Changes` at `.read σ` gives `0` changes;
- the store's `Range` (`KV.Range.contract`, `todo`: `res ≠ null`): `checkStoreRange`'s premise
  with `Q` as above (`genRange` at the loaded `revHi`, any value). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__readOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkStoreRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pickW
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.context.TODO
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

/-- **One read of member `i`'s incarnation** (`readOne` at `mp`, with the member's part of a
reader's `rdOwn`). -/
theorem readOne_at
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_pickW : pick.specW (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_checkStoreRange : runner.checkStoreRange.spec (GF := GF) (hG := hG))
    (x : Loc) (cfg : Config) (wr : List w64) (ks : List GoString) (h : Loc) (γh : HistNames)
    (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface) (q : Qp)
    (hmix : readMixOk (wr.map sint.Z)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
        runnerKeys x ks ∗ runnerH x h ∗ runnerCfg x cfg wr ∗
        histRd h γh ∗ incRd ks γh i mp m ι kv q }}
      (App (x @!! go.GoType.PointerType runner.ty @!! go!"readOne") (Val #mp))
    {{ RET #(); histRd h γh ∗ incRd ks γh i mp m ι kv q }} := by
  haveI := hpers.1 kv ι.kv
  haveI : Persistent (isInc (GF := GF) ks γh i mp m ι kv) := by unfold isInc; infer_instance
  haveI : Persistent (runnerKeys (GF := GF) x ks) := by unfold runnerKeys; infer_instance
  haveI : Persistent (runnerH (GF := GF) x h) := by unfold runnerH; infer_instance
  haveI : Persistent (runnerRangeMix (GF := GF) x cfg) := by unfold runnerRangeMix; infer_instance
  haveI : Persistent (runnerCfg (GF := GF) x cfg wr) := by unfold runnerCfg; infer_instance
  unfold incRd
  wp_start as ⟨#HK, #HH, #HC, Hrd, #Hinc, Hrdr, Hq, Hkvf⟩
  ihave #HK' := HK
  iunfold runnerKeys at HK'
  icases HK' with ⟨%keys, #Hkeys, #Hks, %Hks⟩
  ihave #HC' := HC
  iunfold runnerCfg at HC'
  icases HC' with ⟨#HRM, #Hwr⟩
  ihave #HRM' := HRM
  iunfold runnerRangeMix at HRM'
  icases HRM' with ⟨#Hcfg, %wrr, #Hwrr⟩
  ihave #Hinc' := Hinc
  iunfold isInc at Hinc'
  icases Hinc' with ⟨#Hinv, #Hkv⟩
  ihave %Hsh := (hsh.1 kv ι.kv) $$ Hkv
  obtain ⟨tyK, vK, rfl, hRead, -, hRev, hFirst, hRange, -⟩ := Hsh
  ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
  · iunfold incLive; iframe Hq; iexact Hinc
  wp_auto
  -- the floors
  wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revLo" mp) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  imod revLo_acc ks γh i mp m ι _ q $$ Hlive with ⟨%lo, Hlo, Hcl⟩
  imodintro
  inext
  iexists lo
  iframe Hlo
  iintro Hlo
  imod Hcl $$ Hlo with ⟨Hlive, %n, #Hn, %Hlon⟩
  imodintro
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Load (mF go!"cmpLo" mp) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  imod cmpLo_acc ks γh i mp m ι _ q $$ Hlive with ⟨%clo, Hclo, Hcl⟩
  imodintro
  inext
  iexists clo
  iframe Hclo
  iintro Hclo
  imod Hcl $$ Hclo with ⟨Hlive, %c, #Hc, %Hcloc⟩
  imodintro
  wp_auto
  ihave #Hcf := typedPointsto_split _ _ _ $$ Hcfg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  ihave #Hmx := typedPointsto_split _ _ _ $$ Mix
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmx
  wp_auto
  wp_apply (wp_pickW _ wr DFrac.discard (W64 6)) $$ [$Hwr] as %sw ⟨-, %Hsw1, %Hsw2⟩
  have hsw : 0 ≤ sint.Z sw ∧ sint.Z sw < 6 ∧ sint.nat sw ≠ 5 := by
    obtain ⟨h0, h1, -⟩ := Hsw1
    have h6 : sint.Z (W64 6) = 6 := by decide
    refine ⟨h0, by rw [h6] at h1; exact h1 (by decide), ?_⟩
    obtain ⟨hm5, ⟨j, hj, hjw⟩, hsum⟩ := hmix
    have hn : sint.nat (W64 6) = 6 := by decide
    have hp := Hsw2 ⟨j, by rw [h6]; exact_mod_cast hj, hjw⟩ (by rw [hn]; exact hsum)
    exact readMixOk_ne5 ⟨hm5, ⟨j, hj, hjw⟩, hsum⟩ hp
  have hlo0 : 1 ≤ sint.Z lo ∧ sint.Z lo ≤ n := Hlon
  iunfold incLive at Hlive
  icases Hlive with ⟨-, Hq⟩
  -- each read's update: `reader_au`
  wp_if_destruct
  · -- `Rev`
    ihave Hau := reader_au hpers hreach ks γh i mp m ι _ q n c $$ [$Hinc $Hn $Hc]
    ihave Hau := Hau $$ Hq
    wp_apply (hRev ι.kv (fun σ => iprop(ghostVar ι.ret q () ∗ readQ ks γh m σ ∗
        ⌜n ≤ σ.rev ∧ c ≤ Int.toNat (σ.crev + 1)⌝))) $$ [$Hkv $Hrdr $Hau]
      as %rv ⟨Hrdr, %σ, ⟨Hq, #HQ, %Hnc⟩, %Hrv⟩
    subst Hrv
    ihave #HQ' := HQ
    iunfold readQ at HQ'
    icases HQ' with ⟨%Hl, #Hlb, #Hrv, #Hcr, #Hnr, %Hq'⟩
    have hrv := rev_w64 σ Hq'.2.2
    have hlo' : sint.Z lo ≤ sint.Z (W64 (σ.rev : Int)) := by rw [hrv]; omega
    wp_apply_core wp_inBounds lo (W64 (σ.rev : Int)) (mF go!"revHi" mp) _ hlo' $$ [] [-]
    · iPkgInit
    ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
    · iunfold incLive; iframe Hq; iexact Hinc
    imod revHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hrv] with ⟨%vh, Hh', %Hvh, Hcl⟩
    imodintro
    inext
    iexists _, vh
    iframe Hh'
    isplitr
    · ipureintro; rw [hrv]; exact Hvh.1
    iintro Hh'
    imod Hcl $$ Hh' with Hlive
    imodintro
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hq⟩
    try wp_auto
    iapply HΦ
    iframe
    iexact Hinc
  wp_if_destruct
  · -- `FirstRev`
    ihave Hau := reader_au hpers hreach ks γh i mp m ι _ q n c $$ [$Hinc $Hn $Hc]
    ihave Hau := Hau $$ Hq
    wp_apply (hFirst ι.kv (fun σ => iprop(ghostVar ι.ret q () ∗ readQ ks γh m σ ∗
        ⌜n ≤ σ.rev ∧ c ≤ Int.toNat (σ.crev + 1)⌝))) $$ [$Hkv $Hrdr $Hau]
      as %rv ⟨Hrdr, %σ, ⟨Hq, #HQ, %Hnc⟩, %Hrv⟩
    subst Hrv
    ihave #HQ' := HQ
    iunfold readQ at HQ'
    icases HQ' with ⟨%Hl, #Hlb, #Hrv, #Hcr, #Hnr, %Hq'⟩
    obtain ⟨-, hc1, hc2⟩ := reach_bounds σ Hq'.2.1
    have hrv := rev_w64 σ Hq'.2.2
    have hcr : sint.Z (W64 σ.crev) = σ.crev := by
      have : σ.rev ≤ σ.log.length := by unfold MvccState.rev; omega
      have := Hq'.2.2
      word
    have hlo' : sint.Z clo ≤ sint.Z (W64 σ.crev) := by rw [hcr]; omega
    wp_apply_core wp_inBounds clo (W64 σ.crev) (mF go!"cmpHi" mp) _ hlo' $$ [] [-]
    · iPkgInit
    ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
    · iunfold incLive; iframe Hq; iexact Hinc
    imod cmpHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hcr] with ⟨%vh, Hh', %Hvh, Hcl⟩
    imodintro
    inext
    iexists _, vh
    iframe Hh'
    isplitr
    · ipureintro; rw [hcr]; omega
    iintro Hh'
    imod Hcl $$ Hh' with Hlive
    imodintro
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hq⟩
    try wp_auto
    iapply HΦ
    iframe
    iexact Hinc
  ihave #HH' := HH
  iunfold runnerH at HH'
  wp_if_destruct
  · -- a read transaction, with 1 to 3 ranges
    ihave Hau := reader_au hpers hreach ks γh i mp m ι _ q n c $$ [$Hinc $Hn $Hc]
    ihave Hau := Hau $$ Hq
    wp_apply wp_traceTODO as %trc ⟨%Htrn, Htrc⟩
    wp_apply (hRead ι.kv _ trc true (fun σ => iprop(ghostVar ι.ret q () ∗ readQ ks γh m σ ∗
        ⌜n ≤ σ.rev ∧ c ≤ Int.toNat (σ.crev + 1)⌝))) $$ [$Hkv $Hrdr $Htrc $Hau]
      as %t0 ⟨Htrc, %σ, Htx, Hq, #HQ, %Hnc⟩
    · ipureintro; exact Htrn
    ihave #HQ' := HQ
    iunfold readQ at HQ'
    icases HQ' with ⟨%Hl, #Hlb, #Hrv, #Hcr, #Hnr, %Hq'⟩
    obtain ⟨Hhist, Hreach, Hb⟩ := Hq'
    obtain ⟨-, hc1, hc2⟩ := reach_bounds σ Hreach
    have hrv := rev_w64 σ Hb
    have hcr : sint.Z (W64 σ.crev) = σ.crev := by
      have : σ.rev ≤ σ.log.length := by unfold MvccState.rev; omega
      word
    icases mvccTxn_shape hsh t0 ι.kv trc (.read σ) $$ Htx with ⟨%Hsh, Htx⟩
    obtain ⟨tyT, vT, rfl, hTRev, hTFirst, hTRange, -, -, -, hTEnd⟩ := Hsh
    wp_apply (hTRev ι.kv trc (.read σ)) $$ [$Htx] as Htx
    wp_apply (hTFirst ι.kv trc (.read σ)) $$ [$Htx] as Htx
    simp only [MTxn.state]
    -- the two bounds
    have hlo' : sint.Z lo ≤ sint.Z (W64 (σ.rev : Int)) := by rw [hrv]; omega
    wp_apply_core wp_inBounds lo (W64 (σ.rev : Int)) (mF go!"revHi" mp) _ hlo' $$ [] [-]
    · iPkgInit
    ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
    · iunfold incLive; iframe Hq; iexact Hinc
    imod revHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hrv] with ⟨%vh, Hh', %Hvh, Hcl⟩
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
    have hclo' : sint.Z clo ≤ sint.Z (W64 σ.crev) := by rw [hcr]; omega
    wp_apply_core wp_inBounds clo (W64 σ.crev) (mF go!"cmpHi" mp) _ hclo' $$ [] [-]
    · iPkgInit
    imod cmpHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hcr] with ⟨%vh2, Hh', %Hvh2, Hcl⟩
    imodintro
    inext
    iexists _, vh2
    iframe Hh'
    isplitr
    · ipureintro; rw [hcr]; omega
    iintro Hh'
    imod Hcl $$ Hh' with Hlive
    imodintro
    wp_auto
    wp_apply (wp_snapshot h γh Hl) $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
    wp_apply wp_choose as %y %Hy
    ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
    · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
    obtain ⟨c0, c1, c2⟩ := check_ok ks σ Hl Hs ms Hhist Hreach Hb Hpre.1 Hmlen (sint.Z (W64 σ.crev))
    ihave #Hctx : mvcc.rangeCtx (GF := GF) true todoCtxVal todoCd $$ []
    · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
    ihave HJ : (∃ jv : w64, "j" ∷ j_ptr ↦ jv : IProp GF) $$ [j]
    · iexists W64 0; iframe
    wp_for HJ
    wp_if_destruct
    · -- a range
      wp_apply (wp_genRange x ks cfg (W64 (σ.rev : Int)) (W64 σ.crev)) $$ [] as %rq ⟨%kk, %e, Hk, He, %Hq'⟩
      · iframe #
      ipersist Hk
      ipersist He
      wp_apply wp_ctxTODO
      wp_apply (hTRange ι.kv trc true (.read σ) todoCtxVal todoCd true rq.key' rq.end' kk e rq.ro')
        $$ [$Htx $Htrc $Hctx $Hk $He] as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
      simp only [MTxn.readLog] at Hlwf
      ihave Hout : rangeOutcomeC (GF := GF) rr err σ.log (W64 (σ.rev : Int)) (sint.Z (W64 σ.crev))
          (decide (rq.end' = slice.nil)) kk e rq.ro' $$ [Hout]
      · rw [hcr]; simp only [MTxn.readLog, MTxn.readRev, MTxn.state]; iexact Hout
      have hlog := logOk_read σ Hb Hreach Hlwf
      ihave Hsts := statesP_statesAt ms Hs $$ Hst
      wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs.map Prod.fst)
        (List.replicate Hs.length DFrac.discard) (W64 (σ.rev : Int)) (W64 σ.crev) rq kk e
        DFrac.discard DFrac.discard rr err σ.log Hks.1 hlog c0 c1 c2) $$ [$Hks $Hms $Hsts $Hk $He $Hout]
        as -
      · ipureintro; exact Hrn rfl
      wp_for_post
      iframe
      iexists _
      iframe
    · wp_apply (end_read hTEnd ι.kv trc σ) $$ [$Htx] as Hrdr
      iunfold incLive at Hlive
      icases Hlive with ⟨-, Hq⟩
      try wp_auto
      iapply HΦ
      iframe
      iexact Hinc
  wp_if_destruct
  · -- a read-only transaction
    ihave Hau := reader_au hpers hreach ks γh i mp m ι _ q n c $$ [$Hinc $Hn $Hc]
    ihave Hau := Hau $$ Hq
    wp_apply wp_traceTODO as %trc ⟨%Htrn, Htrc⟩
    wp_apply (hRead ι.kv _ trc true (fun σ => iprop(ghostVar ι.ret q () ∗ readQ ks γh m σ ∗
        ⌜n ≤ σ.rev ∧ c ≤ Int.toNat (σ.crev + 1)⌝))) $$ [$Hkv $Hrdr $Htrc $Hau]
      as %t0 ⟨Htrc, %σ, Htx, Hq, #HQ, %Hnc⟩
    · ipureintro; exact Htrn
    ihave #HQ' := HQ
    iunfold readQ at HQ'
    icases HQ' with ⟨%Hl, #Hlb, #Hrv, #Hcr, #Hnr, %Hq'⟩
    obtain ⟨Hhist, Hreach, Hb⟩ := Hq'
    obtain ⟨-, hc1, hc2⟩ := reach_bounds σ Hreach
    have hrv := rev_w64 σ Hb
    have hcr : sint.Z (W64 σ.crev) = σ.crev := by
      have : σ.rev ≤ σ.log.length := by unfold MvccState.rev; omega
      word
    icases mvccTxn_shape hsh t0 ι.kv trc (.read σ) $$ Htx with ⟨%Hsh, Htx⟩
    obtain ⟨tyT, vT, rfl, -, hTFirst, -, -, -, -, -⟩ := Hsh
    wp_apply (hTFirst ι.kv trc (.read σ)) $$ [$Htx] as Htx
    wp_apply (wp_roTxn _ ι.kv trc σ) $$ [$Htx] as %t1 Htx
    icases mvccTxn_shape hsh t1 ι.kv trc (.read σ) $$ Htx with ⟨%Hsh, Htx⟩
    obtain ⟨tyT1, vT1, rfl, hTRev, -, hTRange, -, -, hTChanges, hTEnd⟩ := Hsh
    wp_apply (hTRev ι.kv trc (.read σ)) $$ [$Htx] as Htx
    simp only [MTxn.state]
    -- the two bounds
    have hlo' : sint.Z lo ≤ sint.Z (W64 (σ.rev : Int)) := by rw [hrv]; omega
    wp_apply_core wp_inBounds lo (W64 (σ.rev : Int)) (mF go!"revHi" mp) _ hlo' $$ [] [-]
    · iPkgInit
    ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
    · iunfold incLive; iframe Hq; iexact Hinc
    imod revHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hrv] with ⟨%vh, Hh', %Hvh, Hcl⟩
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
    have hclo' : sint.Z clo ≤ sint.Z (W64 σ.crev) := by rw [hcr]; omega
    wp_apply_core wp_inBounds clo (W64 σ.crev) (mF go!"cmpHi" mp) _ hclo' $$ [] [-]
    · iPkgInit
    imod cmpHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hcr] with ⟨%vh2, Hh', %Hvh2, Hcl⟩
    imodintro
    inext
    iexists _, vh2
    iframe Hh'
    isplitr
    · ipureintro; rw [hcr]; omega
    iintro Hh'
    imod Hcl $$ Hh' with Hlive
    imodintro
    wp_auto
    wp_apply (wp_snapshot h γh Hl) $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
    ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
    · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
    obtain ⟨c0, c1, c2⟩ := check_ok ks σ Hl Hs ms Hhist Hreach Hb Hpre.1 Hmlen (sint.Z (W64 σ.crev))
    ihave #Hctx : mvcc.rangeCtx (GF := GF) true todoCtxVal todoCd $$ []
    · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
    wp_apply (wp_genRange x ks cfg (W64 (σ.rev : Int)) (W64 σ.crev)) $$ [] as %rq ⟨%kk, %e, Hk, He, %Hq'⟩
    · iframe #
    ipersist Hk
    ipersist He
    wp_apply wp_ctxTODO
    wp_apply (hTRange ι.kv trc true (.read σ) todoCtxVal todoCd true rq.key' rq.end' kk e rq.ro')
      $$ [$Htx $Htrc $Hctx $Hk $He] as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
    simp only [MTxn.readLog] at Hlwf
    ihave Hout : rangeOutcomeC (GF := GF) rr err σ.log (W64 (σ.rev : Int)) (sint.Z (W64 σ.crev))
        (decide (rq.end' = slice.nil)) kk e rq.ro' $$ [Hout]
    · rw [hcr]; simp only [MTxn.readLog, MTxn.readRev, MTxn.state]; iexact Hout
    have hlog := logOk_read σ Hb Hreach Hlwf
    ihave Hsts := statesP_statesAt ms Hs $$ Hst
    wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs.map Prod.fst)
      (List.replicate Hs.length DFrac.discard) (W64 (σ.rev : Int)) (W64 σ.crev) rq kk e
      DFrac.discard DFrac.discard rr err σ.log Hks.1 hlog c0 c1 c2) $$ [$Hks $Hms $Hsts $Hk $He $Hout]
      as -
    · ipureintro; exact Hrn rfl
    wp_apply (hTChanges ι.kv trc (.read σ)) $$ [$Htx] as %chs ⟨Htx, %Hchs⟩
    wp_apply wp_check
    · ipureintro; simp only [decide_eq_true_eq]
      simp only [MTxn.pend, List.length_nil] at Hchs
      word
    wp_apply (end_read hTEnd ι.kv trc σ) $$ [$Htx] as Hrdr
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hq⟩
    try wp_auto
    iapply HΦ
    iframe
    iexact Hinc
  wp_if_destruct
  · -- the store's `Range`
    wp_apply_core sync.atomic.Int64.wp_Load (mF go!"revHi" mp) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
    · iunfold incLive; iframe Hq; iexact Hinc
    imod revHi_acc ks γh i mp m ι _ q _ $$ [$Hlive $Hn] with ⟨%vh, Hh', %Hvh, Hcl⟩
    imodintro
    inext
    iexists vh
    iframe Hh'
    iintro Hh'
    imod Hcl $$ Hh' with Hlive
    imodintro
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hq⟩
    wp_auto
    wp_apply (wp_genRange x ks cfg vh clo) $$ [] as %rq ⟨%kk, %e, Hk, He, %Hq'⟩
    · iframe #
    ipersist Hk
    ipersist He
    ihave Hau := reader_au hpers hreach ks γh i mp m ι _ q n c $$ [$Hinc $Hn $Hc]
    ihave Hau := Hau $$ Hq
    wp_apply wp_ctxTODO
    ihave #Hctx : mvcc.rangeCtx (GF := GF) true todoCtxVal todoCd $$ []
    · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
    wp_apply (hRange ι.kv todoCtxVal todoCd true rq.key' rq.end' kk e rq.ro'
        (fun σ => iprop(ghostVar ι.ret q () ∗ readQ ks γh m σ ∗
          ⌜n ≤ σ.rev ∧ c ≤ Int.toNat (σ.crev + 1)⌝))) $$ [$Hkv $Hrdr $Hctx $Hk $He $Hau]
      as %rr %err ⟨Hrdr, %Hrn, %σ, ⟨Hq, #HQ, %Hnc⟩, Hout, -, %Hlwf⟩
    ihave #HQ' := HQ
    iunfold readQ at HQ'
    icases HQ' with ⟨%Hl, -, -, -, -, %Hq''⟩
    obtain ⟨-, hc1, -⟩ := reach_bounds σ Hq''.2.1
    have hlo' : sint.Z lo ≤ σ.rev := by omega
    have hclo' : sint.Z clo ≤ σ.crev := by omega
    ihave Hlive : incLive (GF := GF) ks γh i mp m ι (interface.mkOk tyK vK) q $$ [Hq]
    · iunfold incLive; iframe Hq; iexact Hinc
    wp_apply (wp_checkStoreRange x ks h γh i mp m ι _ q lo clo rq kk e DFrac.discard DFrac.discard
        rr err σ hlo' hclo') $$ [$HK $HH $Hrd $Hlive $Hk $He $HQ $Hout] as ⟨Hrd, Hlive, -, -⟩
    · iframe
      ipureintro; exact ⟨Hrn rfl, Hlwf⟩
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hq⟩
    try wp_auto
    iapply HΦ
    iframe
    iexact Hinc
  · exfalso
    rename_i a0 a1 a2 a3
    obtain ⟨h0, h6, h5⟩ := hsw
    have hz : sint.Z sw = 0 ∨ sint.Z sw = 1 ∨ sint.Z sw = 2 ∨ sint.Z sw = 3 ∨ sint.Z sw = 4 ∨
        sint.Z sw = 5 := by omega
    rcases hz with h | h | h | h | h | h
    · exact a0 (by word)
    · exact a1 (by word)
    · exact a2 (by word)
    · exact a3 (by word)
    · exact Hif (by word)
    · exact h5 (by have : sint.nat sw = (sint.Z sw).toNat := rfl; omega)

theorem runner.readOne.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_pickW : pick.specW (GF := GF) (hG := hG))
    (wp_inBounds : inBounds.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_genRange : runner.genRange.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_checkStoreRange : runner.checkStoreRange.spec (GF := GF) (hG := hG)) :
    runner.readOne.spec (GF := GF) (hG := hG) := by
  intro x cfg wr ks h γ mp0 mp1 e0 e1 q i mp hmix hi
  have hat := readOne_at hsh hpers hreach wp_pickW wp_inBounds wp_traceTODO wp_snapshot wp_choose
    wp_genRange wp_ctxTODO wp_checkRangeAt wp_roTxn wp_check wp_checkStoreRange x cfg wr ks h γ.h
  unfold rdOwn incRdL
  iintro %Φ ⟨#P1, #P2, #P3, HK, HH, HC, Hrd, H0, H1⟩ HΦ
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    iapply (hat 0 mp0 γ.m0 e0.1 e0.2 q hmix) $$ [$P1 $P2 $P3 $HK $HH $HC $Hrd $H0]
    inext
    iintro ⟨Hrd, H0⟩
    iapply HΦ
    iframe
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    iapply (hat 1 mp1 γ.m1 e1.1 e1.2 q hmix) $$ [$P1 $P2 $P3 $HK $HH $HC $Hrd $H1]
    inext
    iintro ⟨Hrd, H1⟩
    iapply HΦ
    iframe
  · simp at hi

end proof

end mvccfull
end EtcdGrove
end Perennial
