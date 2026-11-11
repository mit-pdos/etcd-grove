/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/newServerMode.lean` (2026-10-22, D33, as
`newServer`'s; the mode a parameter since 2026-11-02).
Lean-first (no Rocq counterpart).

The steps (putget3's `startMember`'s up to `NewServer`, which were putget's `Main`'s): the
configuration's literal (its client URLs, the feature gate); `NewServer` (at the member's storage
registry, D19r (B): each member's `bootstrap` joins its own; 2026-10-27, the server port: the
member's names', `memberBoot`, until then allocated here) (its premises from the literal, the member's
ghost state and `bootstrap`'s contract); on success, `memberBuilt` from its postcondition
(`isServerBuilt_of_gap`, the monitors off by the configuration's zero check intervals and the
gate's `CompactHashCheck`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServerMode
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- `newServerMode`: the glue over `NewServer.spec` in the compaction mode `cmp` (M2's item 14: one
spec in both modes; periodic mode, 2026-11-02). -/
theorem newServerMode.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG)) :
    newServerMode.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token mode retention snapCount catchUp peer cluster lg M iu Uok ps
    bootLog ctxs dir id γ ρ E₀ Φs γn cmp lm Htb Hrb48 HrbN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps
    HU HU8 Hmode Hck Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hfresh⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  iunfold bootPremise at Hboot
  iunfold commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Htd, #Hns, #Hnrl⟩
  iunfold memberBoot at Hmb
  icases Hmb with ⟨%Hρ, Hnboot, #Hsrl, #Hidc, #Hidk, #HNZ0, #Hpmint, #Hrdctx,
    Hids, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv, Hreg, %γd, %Hsloc, Hsdir⟩
  obtain ⟨hraft, hc0, hch, hlog, hpfx, hΦs, hcmp0, hkcmp, hNx, hslg⟩ := Hρ
  -- the imports' package facts
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- the configuration's client URLs
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  -- (2026-10-27, the server port) the member's storage registry (D19r (B)), its `bootstrap`'s to
  -- join, is the member's names' (`memberBoot`; until then allocated here)
  letI : MemStorReg GF := ⟨γ.reg⟩
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  have hblen' : γ.boot.length ≤ 2 ^ 60 := by rw [hboot]; exact hblen
  -- (step 6 of the hubs, 2026-11-03) `NewServer.specG` at auth off, in the member's mode `cmp`; its
  -- mode-indexed rows at `false` are today's (by definition)
  -- (sweep repairs 1, B4) `ETCD_VERIFY` off, from the member's fresh bundle
  icases memberFreshRes_verify _ _ _ $$ Hfresh with ⟨#Hvoff, Hfresh⟩
  have wpNS : NewServer.specG (GF := GF) (hG := hG) false cmp := wp_NewServer cmp
  simp only [NewServer.specG, kvInvM_false, srvErM_false, srvBuiltG_false, bootKVOf_false] at wpNS
  wp_apply (wpNS _ ⟨[httpURL peerAddr], [httpURL client], M, iu⟩
      γ id ctxs ρ E₀ N Φs γn dir γd lm hraft (by rw [hboot]; exact hrule) hc0 hch hlog hkcmp
      ⟨by simp, by simp [mvcc.rangeLimitMax]⟩
      (by simp [v3rpc.etcdMaxRequestBytesOk, v3rpc.etcdMaxRecvMsgSize, v3rpc.grpcOverheadBytes])
      v3rpc.maxTxnOpsOk_default Hmode (fun _ => trivial) hcmp0 hNx Htb Hrb48 HrbN
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩ Hdirok (peerURLsDir_httpURL dir id peerAddr Hdirok Hdir)
      -- (2026-11-03, the final whole-`bootOk` review) the raft node's and the transport's slots: the
      -- literal's clock, the directory of the peers
      (raftNode.bootCfg_of _ rfl) (by rw [hvs]; exact Hdirps)
      -- auth off: the auth mode's premise holds vacuously
      (fun h => absurd h (by decide))
      -- (2026-11-04, the lease-expiry plan's Part C) the lease slot, at the mode of `memberBoot`'s
      -- running-server premise (`lease.runCfg`), auth off
      (lease.bootCfg_of_run hslg (fun h => absurd h (by decide)) Hck)
      -- (2026-11-03, the whole-`bootOk` review) `bootstrap`'s configuration conditions, from the
      -- literal, and the write budget
      (bootCfgOk_of _ rfl rfl rfl rfl) ⟨rfl, discoveryZero_len, HU8⟩ HwbN)
    $$ [Htok Hnboot Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hsdir Hfresh] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, HU, hvs, hrule, hboot⟩
      unfold cfgOk; simp
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hcl; rfl
      iexact Hsls
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    -- the WAL's slot (`wal.bootRes`), from the member's fresh bundle
    isplitl [Hfresh]
    · iapply memberFreshRes_boot _ _ _ rfl rfl; iexact Hfresh
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hsloc
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hdbo
    ipureintro; exact storage.openMmapOk_of_quota_zero _ rfl
  icases Hres with (⟨⟨%Hsn, %Herr⟩, Htok⟩ | ⟨%Herr, Htok, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %HE, #Hwb,
    Hbuilt, Hgap, Hserve, Hsv, Hmon, Hrc, #Hnm, Htokp, HServeR, HWR, #Hlsrv, #Httl, -, -, Hkeep⟩)
  · -- `NewServer` failed: the error returned
    iapply HΦ; ileft; iframe Htok; ipureintro; exact Herr
  subst Herr
  -- what `Start` takes: the built server, the monitors off
  ihave Hsb := isServerBuilt_of_gap srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV N
    $$ [Hbuilt Hgap]
  · iframe
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    iexists _
    iframe Hmf Hfgc
  ihave #Hlr : srvLeaseRd srv E lm $$ []
  · iunfold srvLeaseRd; iexists _; iexact Hlsrv
  -- (the lease-expiry plan's E3 (c) stage 2) the lease-TTL row's raft part, at the peers
  ihave #Httl' : leaseTTLRowR srv ps $$ []
  · rw [← hvs]; iexact Httl
  -- (R2c-5) the data directory, the slot's (the literal's fields)
  icases srvStop.dataDir srv _ E γrn γk (name ++ go!".etcd") rfl rfl $$ Hkeep with ⟨#Hddir, Hkeep⟩
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iframe Htok Httl' Hddir
  iunfold memberBuilt
  iexists γA, ci, TM, E, γrn, b, _, γk, τ
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe
  iframe #
  ipureintro
  exact ⟨HE.1, HE.2.1, rfl, rfl, rfl⟩

end proof

end etcdstart
end EtcdGrove
end Perennial
