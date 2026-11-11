/- Lean-first (no Rocq counterpart). The proof of `runner.restart` (Probe: proved, over
`inc_retire`, `memberState_split` and `WriterShares`' `shares_join`/`shares_split`).

The outline: `stopReaders` (the stock back, `rdStock`), `endEpoch` (the epoch's `epochTok`s back),
the shares joined (`lentOk`: the whole retirement token, `kv` field and `mvccReaderN` tokens),
`inc_retire`, `memberState_split`; `shut` (the lessor's and backend's parts from `memCore`); `open`;
the counter; `startEpoch` (new shares `qs'`, tokens), `startReaders` (`rdStock` at the members' current
incarnations, `rdStock_split`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__restart
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__stopReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__endEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startEpoch
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startReaders
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares
public import Perennial.Spec.sync.atomic.Int64__Add

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
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.restart.wp_proof
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_stopReaders : runner.stopReaders.spec (GF := GF) (hG := hG))
    (wp_endEpoch : runner.endEpoch.spec (GF := GF) (hG := hG))
    (wp_shut : runner.shut.spec (GF := GF) (hG := hG))
    (wp_open : runner.open.spec (GF := GF) (hG := hG))
    (wp_startEpoch : runner.startEpoch.spec (GF := GF) (hG := hG))
    (wp_startReaders : runner.startReaders.spec (GF := GF) (hG := hG)) :
    runner.restart.spec (GF := GF) (hG := hG) := by
  intro _ _ x ks cfg wr h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs j mp hj hdbo hdbc hck hlim hcbl
  haveI : Persistent (runnerMs (GF := GF) x mp0 mp1) := by unfold runnerMs; infer_instance
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  haveI := isInc_persistent hpers
  haveI := hpers.1
  haveI : Persistent (rnCtx (GF := GF) x ks cfg h γ.h) := by
    unfold rnCtx runnerKeys runnerH ctrInv; infer_instance
  haveI : Persistent (runnerCfg (GF := GF) x cfg wr) := by
    unfold runnerCfg runnerRangeMix; infer_instance
  haveI : Persistent (rdShared (GF := GF) x) := by unfold rdShared ctrInv; infer_instance
  haveI : Persistent (runnerKeys (GF := GF) x ks) := by unfold runnerKeys; infer_instance
  haveI : Persistent (runnerH (GF := GF) x h) := by unfold runnerH; infer_instance
  wp_start as ⟨#Hctx, #Hks, #Hvoff, Htok, Hw⟩
  iunfold writerOwn at Hw
  icases Hw with ⟨#Hms, #Hreg0, #Hreg1, Hlog, Hctrs, HhW, Hrd, %Hops, %Hnb, Hfiles,
    ⟨%qw0, %nw0, %k0, Hm0, %Hl0⟩, ⟨%qw1, %nw1, %k1, Hm1, %Hl1⟩, Hss0, Hss1, Hadd⟩
  ihave #HctxK : writerCtx x ks cfg wr h γ.h $$ []
  · iexact Hctx
  ihave #HrnK : rnCtx x ks cfg h γ.h $$ []
  · iunfold writerCtx at Hctx; icases Hctx with ⟨#H, -⟩; iexact H
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, #Hcfg, %Hmix, #Hrds, #Hpb, #Hps, #Hpl, #Hpt, %Hksl, #Hlg, #Hwo, #Hwc,
    #Hws, #Hcrev, #Hccmp, #Hcres, #Hcrst, %HOpsB⟩
  have hlen : ops.length < 2 ^ 38 := by have := Hops.2.2; have := HOpsB.2; omega
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hpm, #Hkeys, %Hkne, #HrH, #Hhist, #Hcfgp, #Hwa, #Hwst, #Hce, #Hcp, #Hcc, #Hccn⟩
  wp_auto
  wp_apply (lc := 1) wp_stopReaders $$ [Hadd] as ⟨Hadd, Hstock⟩
  · iframe; iexact Hrds
  imod lc_fupd_elim_later $$ Hlc1 Hstock with Hstock
  iunfold rdStock at Hstock
  icases Hstock with ⟨Hhrd, Hlent0, Hlent1⟩
  (try wp_auto)
  iunfold logOwn at Hlog
  icases Hlog with ⟨%lsl, %lps, Hlog1, Hlog2, Hlog3, %Hlogp, Hlog4⟩
  have hlogOk := Hlogp.2
  icases histW_lb γ.h _ _ $$ HhW with ⟨HhW, #Hlb⟩
  have hHs := runM_hs_len ks ops ops.length
  rcases j with _ | _ | j
  rotate_right
  · simp at hj
  · -- the leader restarts
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    obtain ⟨⟨hq0, hn0⟩, hnw0, hk0⟩ := Hl0
    iunfold memW at Hm0
    icases Hm0 with ⟨Hops0, Hhk0, Hc0⟩
    iunfold memCore at Hc0
    simp only []
    icases Hc0 with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, HhookIs, Hrdrs, Hbk, Hles, %HU⟩
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    have hR1 : mvccReaders (GF := GF) v0.ι.kv nw0 ⊣⊢
        mvccReaders v0.ι.kv (nw0 - 1) ∗ mvccReaders v0.ι.kv 1 := by
      have := hRdSplit v0.ι.kv (nw0 - 1) 1; rwa [Nat.sub_add_cancel hnw0] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    icases Hss0 with ⟨%sl0, %ss0, Hst0, Hsl0, Hcap0, %Hssl0, Hes0⟩
    have hrv : revAfter ks ops v0.ops < (histAt ks ops ops.length).length := by
      rw [Hops.1]; unfold revAfter MSt.rev histAt; omega
    have hrvZ : sint.Z (W64 (revAfter ks ops v0.ops : Int)) = revAfter ks ops v0.ops := by
      have : revAfter ks ops v0.ops < 2 ^ 63 := by
        have := runM_hs_len ks ops v0.ops; unfold revAfter MSt.rev; omega
      word
    wp_apply (wp_endEpoch ⟨x, h, ks, γ.h, cfg, 0, mp0, γ.m0, v0.ι, v0.kv⟩ qs qw0 sl0 ss0
        (W64 (revAfter ks ops v0.ops : Int)) (histAt ks ops ops.length)
        (by rw [hrvZ]; omega) (by rw [hrvZ]; exact_mod_cast hrv)
        (by rw [hrvZ]; have := runM_hs_len ks ops v0.ops; unfold revAfter MSt.rev; omega))
      $$ [Hst0 Hsl0 Hes0 Hrev Hrd Hr1 Hret] as ⟨Hst0, Hrev, Hrd, Hr1, Hlive, Htoks⟩
    · iunfold epCtx; iunfold rnCtx; dsimp only [epLive]; iunfold incLive; iframe #; iframe
      ipureintro; exact Hkne
    (try wp_auto)
    dsimp only [epLive]
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hret⟩
    ihave Hsh : incShare mp0 v0.ι v0.kv qw0 nw0 $$ [Hret Hkv Hrdrs Hr1]
    · iunfold incShare; iframe; iapply hR1.2; iframe
    rw [Hssl0]
    icases shares_join hpers hRdSplit ⟨x, h, ks, γ.h, cfg, 0, mp0, γ.m0, v0.ι, v0.kv⟩ qw0 q qs nw0 _ _
      hq0 hn0 $$ [Hsh Hlent0 Htoks] with ⟨Hsh, Hhrds⟩
    · iframe
    iunfold incShare at Hsh
    icases Hsh with ⟨Hret, Hkv, Hrdrs⟩
    imod inc_retire hpers ks γ.h 0 mp0 γ.m0 v0.ι v0.kv $$ [Hret] with Hms0
    · iframe #; iframe
    icases (memberState_split ks γ.h mp0 γ.m0 v0.ι.kv).1 $$ Hms0 with ⟨%σ', %b', %Hl', Hσ, Hcarry⟩
    iunfold memberCarry at Hcarry
    icases Hcarry with ⟨Hσc, Hc1, Hc2, Hc3, Hc4, Hbc, Hc5, Hc6, Hc7, Hc8, %Hcp⟩
    icombine Hσw Hσc gives %Hσeq
    icombine Hbw Hbc gives %Hbeq
    obtain ⟨-, rfl⟩ := Hσeq
    obtain ⟨-, rfl⟩ := Hbeq
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hrb, %Hrecs, Hstop, -⟩
    iunfold bkKeep at Hbk
    icases Hbk with ⟨%HbkP, #Hbk1, #Hbk2, Hbk3, Hbk4, Hbk5, Hbk6, Hbk7⟩
    ihave #Hmv : isMvcc v0.kv v0.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    wp_apply (wp_shut x ks cfg wr h γ.h mp0 v0.path v0.bk v0.lp v0.kv v0.ι.kv (σOf ks ops v0.ops)
        (leasesAfter ks ops v0.ops) r k0 hdbc rfl Hrecs)
      $$ [Hkv Hle Hbe Hopen Hrdrs Hback Hσ Hbk3 Hbk4 Hbk5 Hbk6 Hbk7 Hstop Hrb]
      as ⟨Hkv, Hle, Hbe, %D, %u, Hfile, Himg, %HrecD⟩
    · iframe #; iframe; iunfold bkKeep; iframe #; iframe; ipureintro; exact HbkP
    (try wp_auto)
    wp_apply (wp_open x ks cfg wr h γ.h ops 0 mp0 γ.m0 f0 v0.ops v0.path D u v0.b Hl'
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #v0.bk.be) (lease.lessorIface v0.lp) v0.kv hlogOk Hvops hlen hdbo hck hlim hcbl)
      $$ [Htok Hrd Hpath Hbe Hle Hkv Hrev Hcmp Hleases Hfile Himg HhookOk Hσc Hc1 Hc2 Hc3 Hc4 Hbc
        Hc5 Hc6 Hc7 Hc8 Hσw Hbw]
      as ⟨Htok, Hrd, %v', %k', %Hv', Hc'⟩
    · iframe #; iframe
      isplitr
      · rw [Hops.1]; iexact Hlb
      isplitr
      · ipureintro; rw [HbkP.1] at HrecD; exact HrecD
      iunfold memberCarry; iframe; ipureintro; exact Hcp
    (try wp_auto)
    wp_apply_core sync.atomic.Int64.wp_Add (rF go!"restarts" x) (W64 1) $$ [] [-]
    · iPkgInit
    iunfold ctrInv at Hcrst
    iinv Hcrst with ⟨%a, >Ha⟩ Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "restarts") from
      Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists a
    iframe
    iintro Ha
    imod Hcl with -
    imod Hclose $$ [Ha] with -
    · inext; iexists _; iframe
    imodintro
    (try wp_auto)
    obtain ⟨hv'ops, hv'path, hv'b, hk'⟩ := Hv'
    iunfold memCore at Hc'
    simp only []
    icases Hc' with ⟨#Hid', #Hhook', HhookOk', Hpath', Hbe', Hle', Hkv', Hrev', Hcmp', Hleases',
      %Hvops', Hinc', Hopen', Hback', HhookIs', Hrdrs', Hbk', Hles', %HU'⟩
    iunfold incW at Hinc'
    icases Hinc' with ⟨#Hisinc', Hret', Hσw', Hbw'⟩
    ihave Hsh : incShare mp0 v'.ι v'.kv 1 mvccReaderN $$ [Hret' Hkv' Hrdrs']
    · iunfold incShare; iframe
    icases shares_split hpers hRdSplit ⟨x, h, ks, γ.h, cfg, 0, mp0, γ.m0, v'.ι, v'.kv⟩ qw0 q qs nw0 _ _
      hq0 hn0 $$ [Hsh Hhrds] with ⟨Hsh, Hlent0, Htoks⟩
    · iframe #; iframe
    iunfold incShare at Hsh
    icases Hsh with ⟨Hret', Hkv', Hrdrs'⟩
    wp_apply (wp_startEpoch ⟨x, h, ks, γ.h, cfg, 0, mp0, γ.m0, v'.ι, v'.kv⟩ qs qw0)
      $$ [Hkv' Hst0 Htoks] as ⟨Hkv', %sl0', %ss0', Hst0, Hsl0, Hcap0', %Hssl0', Hes0⟩
    · iunfold epCtx; dsimp only; iframe #; iframe
    (try wp_auto)
    icases memW_isInc hpers ks γ.h ops 1 mp1 γ.m1 f1 v1 qw1 nw1 k1 $$ Hm1 with ⟨Hm1, #Hisinc1⟩
    wp_apply (wp_startReaders x cfg wr ks h γ mp0 mp1 (v'.ι, v'.kv) (v1.ι, v1.kv) q Hmix)
      $$ [Htok Hadd Hhrd Hlent0 Hlent1] as ⟨Htok, Hadd⟩
    · iframe #; iframe; iunfold rdStock; iframe
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iexists v', v1, q, qs
    isplitr
    · ipureintro; exact ⟨hv'ops, rfl⟩
    iunfold writerOwn
    dsimp only
    iframe #
    iframe Hctrs HhW Hrd Hfiles Hadd
    isplitl [Hlog1 Hlog2 Hlog3 Hlog4]
    · iunfold logOwn; iexists lsl, lps; iframe; ipureintro; exact Hlogp
    isplitr
    · ipureintro; rw [hv'ops]; exact Hops
    isplitr
    · ipureintro; rw [hv'ops]; exact Hnb
    isplitl [Hops0 Hhk0 HhookOk' Hpath' Hbe' Hle' Hkv' Hrev' Hcmp' Hleases' Hopen' Hback' HhookIs'
      Hrdrs' Hbk' Hles' Hσw' Hbw' Hret']
    · iexists qw0, nw0, k'
      isplitl
      · iunfold memW; iunfold memCore; dsimp only; iunfold incW
        rw [hv'ops] at *
        iframe #; iframe
        ipureintro; exact ⟨Hvops, HU'⟩
      · ipureintro; exact ⟨⟨hq0, hn0⟩, hnw0, by omega⟩
    isplitl [Hm1]
    · iexists qw1, nw1, k1; iframe; ipureintro; exact Hl1
    isplitl [Hst0 Hsl0 Hcap0' Hes0]
    · iexists sl0', ss0'; iframe; ipureintro; exact Hssl0'
    iexact Hss1
  · -- the follower restarts
    simp at hj
    subst hj
    obtain ⟨⟨hq1, hn1⟩, hnw1, hk0⟩ := Hl1
    iunfold memW at Hm1
    icases Hm1 with ⟨Hops1, Hhk1, Hc1x⟩
    iunfold memCore at Hc1x
    simp only []
    icases Hc1x with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, HhookIs, Hrdrs, Hbk, Hles, %HU⟩
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    have hR1 : mvccReaders (GF := GF) v1.ι.kv nw1 ⊣⊢
        mvccReaders v1.ι.kv (nw1 - 1) ∗ mvccReaders v1.ι.kv 1 := by
      have := hRdSplit v1.ι.kv (nw1 - 1) 1; rwa [Nat.sub_add_cancel hnw1] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    icases Hss1 with ⟨%sl1, %ss1, Hst1, Hsl1, Hcap1, %Hssl1, Hes1⟩
    have hrv : revAfter ks ops v1.ops < (histAt ks ops ops.length).length := by
      have hm := revAfter_mono ks ops v1.ops ops.length (by omega)
      unfold revAfter MSt.rev at hm ⊢; unfold histAt; omega
    have hrvZ : sint.Z (W64 (revAfter ks ops v1.ops : Int)) = revAfter ks ops v1.ops := by
      have : revAfter ks ops v1.ops < 2 ^ 63 := by
        have := runM_hs_len ks ops v1.ops; unfold revAfter MSt.rev; omega
      word
    wp_apply (wp_endEpoch ⟨x, h, ks, γ.h, cfg, 1, mp1, γ.m1, v1.ι, v1.kv⟩ qs qw1 sl1 ss1
        (W64 (revAfter ks ops v1.ops : Int)) (histAt ks ops ops.length)
        (by rw [hrvZ]; omega) (by rw [hrvZ]; exact_mod_cast hrv)
        (by rw [hrvZ]; have := runM_hs_len ks ops v1.ops; unfold revAfter MSt.rev; omega))
      $$ [Hst1 Hsl1 Hes1 Hrev Hrd Hr1 Hret] as ⟨Hst1, Hrev, Hrd, Hr1, Hlive, Htoks⟩
    · iunfold epCtx; iunfold rnCtx; dsimp only [epLive]; iunfold incLive; iframe #; iframe
      ipureintro; exact Hkne
    (try wp_auto)
    dsimp only [epLive]
    iunfold incLive at Hlive
    icases Hlive with ⟨-, Hret⟩
    ihave Hsh : incShare mp1 v1.ι v1.kv qw1 nw1 $$ [Hret Hkv Hrdrs Hr1]
    · iunfold incShare; iframe; iapply hR1.2; iframe
    rw [Hssl1]
    icases shares_join hpers hRdSplit ⟨x, h, ks, γ.h, cfg, 1, mp1, γ.m1, v1.ι, v1.kv⟩ qw1 q qs nw1 _ _
      hq1 hn1 $$ [Hsh Hlent1 Htoks] with ⟨Hsh, Hhrds⟩
    · iframe
    iunfold incShare at Hsh
    icases Hsh with ⟨Hret, Hkv, Hrdrs⟩
    imod inc_retire hpers ks γ.h 1 mp1 γ.m1 v1.ι v1.kv $$ [Hret] with Hms1x
    · iframe #; iframe
    icases (memberState_split ks γ.h mp1 γ.m1 v1.ι.kv).1 $$ Hms1x with ⟨%σ', %b', %Hl', Hσ, Hcarry⟩
    iunfold memberCarry at Hcarry
    icases Hcarry with ⟨Hσc, Hc1, Hc2, Hc3, Hc4, Hbc, Hc5, Hc6, Hc7, Hc8, %Hcp⟩
    icombine Hσw Hσc gives %Hσeq
    icombine Hbw Hbc gives %Hbeq
    obtain ⟨-, rfl⟩ := Hσeq
    obtain ⟨-, rfl⟩ := Hbeq
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hrb, %Hrecs, Hstop, -⟩
    iunfold bkKeep at Hbk
    icases Hbk with ⟨%HbkP, #Hbk1, #Hbk2, Hbk3, Hbk4, Hbk5, Hbk6, Hbk7⟩
    ihave #Hmv : isMvcc v1.kv v1.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H, -⟩; iexact H
    wp_apply (wp_shut x ks cfg wr h γ.h mp1 v1.path v1.bk v1.lp v1.kv v1.ι.kv (σOf ks ops v1.ops)
        (leasesAfter ks ops v1.ops) r k1 hdbc rfl Hrecs)
      $$ [Hkv Hle Hbe Hopen Hrdrs Hback Hσ Hbk3 Hbk4 Hbk5 Hbk6 Hbk7 Hstop Hrb]
      as ⟨Hkv, Hle, Hbe, %D, %u, Hfile, Himg, %HrecD⟩
    · iframe #; iframe; iunfold bkKeep; iframe #; iframe; ipureintro; exact HbkP
    (try wp_auto)
    wp_apply (wp_open x ks cfg wr h γ.h ops 1 mp1 γ.m1 f1 v1.ops v1.path D u v1.b Hl'
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #v1.bk.be) (lease.lessorIface v1.lp) v1.kv hlogOk Hvops hlen hdbo hck hlim hcbl)
      $$ [Htok Hrd Hpath Hbe Hle Hkv Hrev Hcmp Hleases Hfile Himg HhookOk Hσc Hc1 Hc2 Hc3 Hc4 Hbc
        Hc5 Hc6 Hc7 Hc8 Hσw Hbw]
      as ⟨Htok, Hrd, %v', %k', %Hv', Hc'⟩
    · iframe #; iframe
      isplitr
      · iapply (monoListLbOwn_le _ (runM_hs_prefix ks ops v1.ops ops.length (by omega))); iexact Hlb
      isplitr
      · ipureintro; rw [HbkP.1] at HrecD; exact HrecD
      iunfold memberCarry; iframe; ipureintro; exact Hcp
    (try wp_auto)
    wp_apply_core sync.atomic.Int64.wp_Add (rF go!"restarts" x) (W64 1) $$ [] [-]
    · iPkgInit
    iunfold ctrInv at Hcrst
    iinv Hcrst with ⟨%a, >Ha⟩ Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "restarts") from
      Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists a
    iframe
    iintro Ha
    imod Hcl with -
    imod Hclose $$ [Ha] with -
    · inext; iexists _; iframe
    imodintro
    (try wp_auto)
    obtain ⟨hv'ops, hv'path, hv'b, hk'⟩ := Hv'
    iunfold memCore at Hc'
    simp only []
    icases Hc' with ⟨#Hid', #Hhook', HhookOk', Hpath', Hbe', Hle', Hkv', Hrev', Hcmp', Hleases',
      %Hvops', Hinc', Hopen', Hback', HhookIs', Hrdrs', Hbk', Hles', %HU'⟩
    iunfold incW at Hinc'
    icases Hinc' with ⟨#Hisinc', Hret', Hσw', Hbw'⟩
    ihave Hsh : incShare mp1 v'.ι v'.kv 1 mvccReaderN $$ [Hret' Hkv' Hrdrs']
    · iunfold incShare; iframe
    icases shares_split hpers hRdSplit ⟨x, h, ks, γ.h, cfg, 1, mp1, γ.m1, v'.ι, v'.kv⟩ qw1 q qs nw1 _ _
      hq1 hn1 $$ [Hsh Hhrds] with ⟨Hsh, Hlent1, Htoks⟩
    · iframe #; iframe
    iunfold incShare at Hsh
    icases Hsh with ⟨Hret', Hkv', Hrdrs'⟩
    wp_apply (wp_startEpoch ⟨x, h, ks, γ.h, cfg, 1, mp1, γ.m1, v'.ι, v'.kv⟩ qs qw1)
      $$ [Hkv' Hst1 Htoks] as ⟨Hkv', %sl1', %ss1', Hst1, Hsl1, Hcap1', %Hssl1', Hes1⟩
    · iunfold epCtx; dsimp only; iframe #; iframe
    (try wp_auto)
    icases memW_isInc hpers ks γ.h ops 0 mp0 γ.m0 f0 v0 qw0 nw0 k0 $$ Hm0 with ⟨Hm0, #Hisinc0⟩
    wp_apply (wp_startReaders x cfg wr ks h γ mp0 mp1 (v0.ι, v0.kv) (v'.ι, v'.kv) q Hmix)
      $$ [Htok Hadd Hhrd Hlent0 Hlent1] as ⟨Htok, Hadd⟩
    · iframe #; iframe; iunfold rdStock; iframe
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iexists v0, v', q, qs
    isplitr
    · ipureintro; exact ⟨rfl, hv'ops⟩
    iunfold writerOwn
    dsimp only
    iframe #
    iframe Hctrs HhW Hrd Hfiles Hadd
    isplitl [Hlog1 Hlog2 Hlog3 Hlog4]
    · iunfold logOwn; iexists lsl, lps; iframe; ipureintro; exact Hlogp
    isplitr
    · ipureintro; rw [hv'ops]; exact Hops
    isplitr
    · ipureintro; rw [hv'ops]; exact Hnb
    isplitl [Hm0]
    · iexists qw0, nw0, k0; iframe; ipureintro; exact Hl0
    isplitl [Hops1 Hhk1 HhookOk' Hpath' Hbe' Hle' Hkv' Hrev' Hcmp' Hleases' Hopen' Hback' HhookIs'
      Hrdrs' Hbk' Hles' Hσw' Hbw' Hret']
    · iexists qw1, nw1, k'
      isplitl
      · iunfold memW; iunfold memCore; dsimp only; iunfold incW
        rw [hv'ops] at *
        iframe #; iframe
        ipureintro; exact ⟨Hvops, HU'⟩
      · ipureintro; exact ⟨⟨hq1, hn1⟩, hnw1, by omega⟩
    isplitl [Hss0]
    · iexact Hss0
    iexists sl1', ss1'; iframe; ipureintro; exact Hssl1'

end proof

end mvccfull
end EtcdGrove
end Perennial
