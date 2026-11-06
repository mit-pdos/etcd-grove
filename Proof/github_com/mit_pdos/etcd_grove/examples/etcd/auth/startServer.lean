/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth/startServer.lean` (the auth plan's
E3zb, 2026-10-28). Lean-first (no Rocq counterpart).

The steps (`etcdstart.StartServer`'s, `etcdstart.newServer`'s and `etcdstart.wp_Start_built`'s, with auth on):
the peer URL slice and the cluster's map `{authkv ↦ peer}` (read-only from here on, D19r (F)); the
configuration's client URLs and feature gate; `NewServer` with auth on (`NewServer.specM true`: the
simple provider, the TTL `300`), whose post gives the mode `.on γa`, the lessor finding no lease
(`srvLessorNil`) and the built part with auth on (`isServerBuilt_of_gapM true`); on success
`s.Start()` at the auth slot's `on γa` (`Start.spec`). An error of `NewServer` returns it, with the thread token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.startServer
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

theorem startServer.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.specM (GF := GF) (hG := hG) true)
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    startServer.spec (GF := GF) (hG := hG) := by
  intro CS N lg bootLog ctxs dir id γ ρ E₀ Φs γn Htb Hrb48 HrbN HwbN hvs hrule hboot hblen Hγn1 Hγn2
    Hdirok Hdir Hdirps Hlg Hck Haf Hbuq Hdbo
  wp_start as ⟨Htok, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hfresh⟩
  iunfold etcdstart.commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
  iunfold etcdstart.memberBootOn at Hmb
  icases Hmb with ⟨%Hρ, Hnboot, #Hsrl, #Hidc, #Hidk, #HNZ0, #Hpmint, #Hrdctx,
    Hids, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv, Hreg, %γd, %Hsloc, Hsdir⟩
  obtain ⟨hraft, hc0, hch, hlog, hcok, hpfx, hΦs, hcmp0, hkcmp, hslg, hlgf⟩ := Hρ
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- the peer URL slice and the cluster's map, read-only from here on (D19r (F))
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer ⟨Hpeer, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  (try wp_auto)
  -- the configuration's client URLs
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert go!"authkv" (slice.mk peer (W64 1) (W64 1)) ∅,
      sl ↦*□ (fun _ => [etcdstart.httpURL go!"127.0.0.1:23926"]) k $$ []
  · iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iExactEq Hpeer; rfl
    iapply BigSepM.bigSepM_empty.2; itrivial
  letI : MemStorReg GF := ⟨γ.reg⟩
  have hblen' : γ.boot.length ≤ 2 ^ 60 := by rw [hboot]; exact hblen
  -- `NewServer(cfg)` with auth on
  wp_apply (wp_NewServer _ ⟨[etcdstart.httpURL go!"127.0.0.1:23926"],
        [etcdstart.httpURL go!"127.0.0.1:23916"],
        GMap.insert go!"authkv" (slice.mk peer (W64 1) (W64 1)) ∅,
        fun _ => [etcdstart.httpURL go!"127.0.0.1:23926"]⟩
      γ id ctxs ρ E₀ N Φs γn dir γd .none hraft (by rw [hboot]; exact hrule) hc0 hch hlog hcok hkcmp
      Hlg ⟨by simp, by simp [mvcc.rangeLimitMax]⟩
      (by simp [v3rpc.etcdMaxRequestBytesOk, v3rpc.etcdMaxRecvMsgSize, v3rpc.grpcOverheadBytes])
      v3rpc.maxTxnOpsOk_default (v3compactor.bootCfg_off _ _ _ _ (by first | rfl | simp))
      (fun h => absurd h (by decide)) hcmp0 Htb Hrb48 HrbN
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩ Hdirok
      (etcdstart.peerURLsDir_httpURL dir id _ Hdirok Hdir)
      -- (2026-11-03, the final whole-`bootOk` review) the raft node's and the transport's slots: the
      -- literal's clock, the directory of the peers
      (raftNode.bootCfg_of _ rfl) (by rw [hvs]; exact Hdirps)
      (fun _ => ⟨rfl, by word, by word⟩)
      -- (2026-11-04, the lease-expiry plan's Part C) the lease slot: auth on grants no lease
      (lease.bootCfg_none _ _ (by simpa [KVNames.lg_eq] using hlgf) Hck)
      -- (2026-11-03, the whole-`bootOk` review) `bootstrap`'s configuration conditions, from the
      -- literal, and the write budget
      (etcdstart.bootCfgOk_of _ Hlg rfl rfl rfl rfl)
      ⟨rfl, etcdstart.discoveryZero_len, etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty⟩
      HwbN)
    $$ [Htok Hnboot Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hsdir Hfresh] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩, hvs, hrule, hboot⟩
      unfold cfgOk; simp
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hpm; rfl
      iexact Hsls
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    -- the WAL's slot (`wal.bootRes`), from the member's fresh bundle
    isplitl [Hfresh]
    · iapply etcdstart.memberFreshRes_boot go!"authkv" _ _ rfl rfl; iexact Hfresh
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hsloc
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hdbo
    ipureintro; exact storage.openMmapOk_of_quota_zero _ rfl
  icases Hres with (⟨⟨%Hsn, %Herr⟩, Htok⟩ | ⟨%Herr, Htok, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %HE, #Hwb,
    Hbuilt, Hgap, Hserve, Hsv, Hmon, Hrc, #Hnm, Htokp, -, HWR, #Hlsrv, -, #Hcca, #HBF, Hkeep⟩)
  · -- `NewServer` failed: the error returned, with the thread token
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- (the lease-grant plan's D1) the lessor finds no lease, auth being on
  ihave #HLnil := lease.srvInv_lessorNil true srv E .none rfl $$ Hlsrv
  obtain ⟨hagree, -, hγa⟩ := HE
  obtain ⟨γa, hγa⟩ := hγa trivial
  -- what `Start` takes: the built part with auth on (at the boot state `x₀` and the read loop's
  -- environment `Er`, named once), the monitors off
  obtain ⟨x₀, hx₀⟩ : ∃ x, x = bootKVOf true := ⟨_, rfl⟩
  obtain ⟨Er, hEr⟩ : ∃ Er, Er = srvErM true ρ E₀ (W64 0) (W64 0) x₀ id (srvTrKey γn γk) (srvTrStopK γk) := ⟨_, rfl⟩
  ihave Hsb : isServerBuiltOn srv γA ci TM E ρ ρ.rd Er γrn b (W64 0) (W64 0) (W64 0) x₀ N
      $$ [Hbuilt Hgap]
  · subst hEr hx₀
    rw [← isServerBuiltM_true]
    iapply isServerBuilt_of_gapM
    iframe
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    iexists _
    iframe Hmf Hfgc
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  -- `s.Start()` at the auth slot's `on γa`: the built part as the slot's row, the lessor's
  have hB := isServerBuiltM_C (GF := GF) (.on γa) srv γA ci TM E ρ ρ.rd Er γrn b (W64 0) (W64 0)
    (W64 0) x₀ N hγa
  have hL := acLessor_on (GF := GF) (.on γa) γa rfl srv
  dsimp only [AuthC.isOn] at hB
  rw [isServerBuiltM_true] at hB
  ihave Hsb := hB.1 $$ [Hsb Hkeep]
  · iframe Hsb
    iapply (srvStop.slot_intro (γk := γk) (Er := Er) (h := by rw [hEr]; rfl)) $$ Hkeep
  ihave #HLnil := hL.2 $$ HLnil
  have h' := wp_Start srv γA ci TM (.on γa) E ρ ρ.rd Er γrn b (W64 0) (W64 0) (W64 0) x₀ N
  simp only [AuthC.isOn] at h'
  wp_apply h' $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, #Hlb, Hgo, Hlg3, Hsr, -⟩
  · iframe; iframe #
    ipureintro; exact ⟨hγa, Hrb48, HrbN, by trivial⟩
  subst hEr hx₀
  iunfold srvStartReaders at Hsr
  icases Hsr with ⟨Hrslots, -⟩
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists γa
  iapply etcdstart.memberUpOn_intro _ _ _ _ _ _ _ E _ γw
  iframe
  iframe #
  isplitr
  · ipureintro; exact ⟨hagree, hγa, rfl, rfl, rfl⟩
  isplitl [Htokp]
  · iunfold etcdstart.srvPeerCtl
    iexists τ
    iframe Hnm Htokp
  -- the TLS fallback off: the configuration's `ClientCertAuthEnabled` is the default `false`
  isplitr
  · iintro !> #Ht
    iapply srvTLSId_false srv $$ [Ht]
    iframe Ht
    iExactEq Hcca; rfl
  iapply HBF; ipureintro; first | rfl | trivial

end proof

end etcd_auth
end EtcdGrove
end Perennial
