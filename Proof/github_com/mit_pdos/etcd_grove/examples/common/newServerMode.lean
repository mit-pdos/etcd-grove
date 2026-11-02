/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/newServerMode.lean` (2026-10-22, D33, as
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

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServerMode
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- `newServerMode`: the glue over `NewServer.spec` in the compaction mode `cmp` (M2's item 14: one
spec in both modes; periodic mode, 2026-11-02). -/
theorem newServerMode.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG)) :
    newServerMode.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token mode retention snapCount catchUp peer cluster lg M iu Uok ps
    bootLog ctxs dir id γ ρ E₀ Φs γn cmp Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir
    HU HU8 Hlg Hmode Hck Haf Hbuq Hdbo
  wp_start as ⟨Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet⟩
  iunfold bootPremise at Hboot
  iunfold commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hnrl⟩
  iunfold memberBoot at Hmb
  icases Hmb with ⟨%Hρ, Hnboot, #Hsrl, #Hidc, #HNZ0, #Hpmint, #Hrdctx,
    Hids, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv, Hreg, %γd, %Hsloc, Hsdir⟩
  obtain ⟨hraft, hc0, hch, hlog, hcok, hpfx, hΦs, hcmp0, hkcmp⟩ := Hρ
  -- `NewServer`'s compactor premise and the store's mode, from the mode's
  have Hacr : retention = W64 0 ∨
      (mode = go!"revision" ∧ 0 < sint.Z retention ∧ (ρ.rd.kv.cret : Int) ≤ sint.Z retention) ∨
      (mode = go!"periodic" ∧ 10 ≤ sint.Z retention ∧ ρ.rd.kv.cret = 0) := by
    cases cmp
    · exact Or.inl (by simpa using Hmode)
    · exact Or.inr (by simpa using Hmode)
  have Hdec : E₀.cmp = decide (retention ≠ W64 0) := by
    rw [hcmp0]
    cases cmp
    · have h0 : retention = W64 0 := by simpa using Hmode
      simp [h0]
    · have h0 : retention ≠ W64 0 := by
        rintro rfl
        simp only [↓reduceIte] at Hmode
        rcases Hmode with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> simp at h
      exact (decide_eq_true h0).symm
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
  wp_apply (wp_NewServer _ ⟨[httpURL peerAddr], [httpURL client], M, iu⟩
      γ id ctxs ρ E₀ N Φs γn dir γd hraft (by rw [hboot]; exact hrule) hc0 hch hlog hcok
      Hlg ⟨by simp, by simp [mvcc.rangeLimitMax]⟩
      (by simp [v3rpc.etcdMaxRequestBytesOk, v3rpc.etcdMaxRecvMsgSize, v3rpc.grpcOverheadBytes])
      v3rpc.maxTxnOpsOk_default Hacr Hdec
      (hkcmp.trans hcmp0.symm) Htb Hrb48 HrbN
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩ Hdirok (peerURLsDir_httpURL dir id peerAddr Hdirok Hdir))
    $$ [Htok Hnboot Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hsdir] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · rw [show (N + if E₀.cmp = true then N else 0) = (if cmp then N + N else N) by
        cases cmp <;> simp [hcmp0]]
      iapply Hboot
      ipureintro
      refine ⟨?_, HU, HU8, hvs, hrule, hboot⟩
      unfold cfgOk; simp
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hcl; rfl
      iexact Hsls
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hsloc
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hdbo
    isplitr; · ipureintro; exact storage.openMmapOk_of_quota_zero _ rfl
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨⟨%Hsn, %Herr⟩, Htok⟩ | ⟨%Herr, Htok, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %HE, #Hwb,
    Hbuilt, Hgap, Hserve, Hsv, Hmon, Hrc, #Hnm, Htokp, HServeR, HWR, -, #Hlrd, #Hpool⟩)
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
  ihave #Hlr : srvLeaseRd srv E $$ []
  · iunfold srvLeaseRd; iframe #
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iframe Htok
  iunfold memberBuilt
  iexists γA, ci, TM, E, γrn, b, _, γk, τ
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe
  iframe #
  ipureintro
  exact ⟨HE.1, HE.2, rfl, rfl, rfl⟩

end proof

end common
end EtcdGrove
end Perennial
