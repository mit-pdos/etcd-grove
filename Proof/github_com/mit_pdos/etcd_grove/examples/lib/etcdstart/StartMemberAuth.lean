/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/StartMemberAuth.lean`: auth3's
`startMember.wp_proof` at any token, URLs and snapshot settings (authN, 2026-11-15). Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMemberAuth
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Proof.net.http.Axioms
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

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

theorem StartMemberAuth.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.specM (GF := GF) (hG := hG) true)
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    StartMemberAuth.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn m Htb Hrb48
    HrbN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU HU8 HnL Haf Hbuq Hdbo Hcu
  wp_start as ⟨#Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hfresh⟩
  -- the peer address's listen right and raft protocol, out of the fresh bundle (to `net.Listen` and
  -- `http.Serve`); the rest to `NewServer`
  icases memberFreshRes_peer _ _ _ _ rfl $$ Hfresh with ⟨⟨Haddr, Hpown⟩, Hfresh⟩
  iunfold bootPremiseOn at Hboot
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  iunfold commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Htd, #Hns⟩
  iunfold memberBootOn at Hmb
  icases Hmb with ⟨%Hρ, Hnboot, #Hsrl, #Hidc, #Hpfxi, #Hidk, #HNZ0, #Hpmint, #Hrdctx,
    Hids, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv, Hreg, %γd, %Hsloc, Hsdir⟩
  obtain ⟨hraft, hc0, hch, hlog, hpfx, hΦs, hcmp0, hkcmp, hNx, hslg, hlgf⟩ := Hρ
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
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc, #Hflc⟩
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  letI : MemStorReg GF := ⟨γ.reg⟩
  have hblen' : γ.boot.length ≤ 2 ^ 60 := by rw [hboot]; exact hblen
  -- `NewServer(cfg)` with auth on
  -- (sweep repairs 1, B4) `ETCD_VERIFY` off, from the member's fresh bundle
  icases memberFreshRes_verify _ _ _ $$ Hfresh with ⟨#Hvoff, Hfresh⟩
  wp_apply (wp_NewServer _ ⟨[httpURL peerAddr], [httpURL client], M, iu⟩
      γ id ctxs ρ E₀ N Φs γn dir γd m hraft (by rw [hboot]; exact hrule)
      (fun h => by simpa using Hcu h) hc0 hch hlog hkcmp
      ⟨by simp, by simp [mvcc.rangeLimitMax]⟩
      (by simp [v3rpc.etcdMaxRequestBytesOk, v3rpc.etcdMaxRecvMsgSize, v3rpc.grpcOverheadBytes])
      v3rpc.maxTxnOpsOk_default (v3compactor.bootCfg_off _ _ _ _ (by first | rfl | simp))
      (fun h => absurd h (by decide)) hcmp0 hNx Htb Hrb48 HrbN
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩ Hdirok
      (peerURLsDir_httpURL dir id peerAddr Hdirok Hdir)
      -- (2026-11-03, the final whole-`bootOk` review) the raft node's and the transport's slots: the
      -- literal's clock, the directory of the peers
      (raftNode.bootCfg_of _ rfl) (by rw [hvs]; exact Hdirps)
      (fun _ => ⟨rfl, by word, by word⟩)
      -- (2026-11-04, the lease-expiry plan's Part C) the lease slot; (auth-lease S4) at the member's
      -- mode, with auth on no lease expiring in the revocable mode (`memberBootOn`'s row)
      (lease.bootCfg_of_run hslg (fun _ => hlgf))
      -- (2026-11-03, the whole-`bootOk` review) `bootstrap`'s configuration conditions, from the
      -- literal, and the write budget
      (bootCfgOk_of _ rfl rfl rfl rfl)
      ⟨rfl, discoveryZero_len, HU8, dirFits_memberDataDir name HnL⟩
      HwbN)
    $$ [Htok Hnboot Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hsdir Hfresh] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, HU, hvs, hrule, hboot⟩
      unfold cfgOkOn cfgOk; simp [memberDataDir]
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
    · iapply memberFreshRes_boot _ _ _ rfl (srvWalDirOf_lit _); iexact Hfresh
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hsloc
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hdbo
    ipureintro; exact storage.openMmapOk_of_quota_zero _ rfl
  icases Hres with (⟨⟨%Hsn, %Herr⟩, Htok⟩ | ⟨%Herr, Htok, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %HE, Hstk,
    #Hwb, Hbuilt, Hgap, Hserve, Hsv, Hmon, Hrc, #Hnm, Htokp, HServeR, #Hlsrv, -, #Hcca, #HBF, Hkeep⟩)
  · -- `NewServer` failed: the error returned, with the thread token
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `net.Listen("tcp", peerAddr)` (`NewMember`'s)
  wp_apply (wp_Listen go!"tcp" peerAddr) $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis, Hpleft⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Hlerr
  wp_auto
  -- the listener serves the peer address with the raft protocol (the program start's reservation)
  imod (http.register lis peerAddr (raftProto (netRh γn))) $$ Hlis Hpleft Hpown with Hlis
  -- `go http.Serve(l, s.RaftHandler())`: the member owns its peer address (the directory's)
  have Hown : (netRh γn).owner peerAddr = id := by
    rw [netRh_owner]
    exact netOwner_of_mem γn.dir (by rw [Hγn2]; exact Hdirok.2.1) id peerAddr (by rw [Hγn2]; exact Hdir)
  wp_apply (wp_RaftHandler srv γn id τ peerAddr Hown) as %h Hh
  · iframe #
  (try wp_auto)
  wp_apply wp_fork $$ [Hlis Hh HServeR]
  · wp_apply (http.Serve_ok (raftHttpNet (netRh γn)) lis h peerAddr (srvServeRes γn τ))
      $$ [Hlis Hh HServeR] as %serr -
    · iframe Hh HServeR
      rw [show (raftHttpNet (netRh γn)).proto peerAddr = raftProto (netRh γn) from rfl]
      iexact Hlis
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
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
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm, #Hmw⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    isplitr
    · iexists _
      iframe Hmf Hfgc
    -- (wal-link L2) no WAL purge: the literal leaves `MaxWALFiles` zero
    iExactEq Hmw; rfl
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlg1, Hlg2⟩
  -- `s.Start()` at the auth slot's `on γa`: the built part as the slot's row
  have hB := isServerBuiltM_C (GF := GF) (.on γa) srv γA ci TM E ρ ρ.rd Er γrn b (W64 0) (W64 0)
    (W64 0) x₀ N hγa
  dsimp only [AuthC.isOn] at hB
  rw [isServerBuiltM_true] at hB
  ihave Hsb := hB $$ [Hsb Hkeep]
  · iframe Hsb
    iapply (srvStop.slot_intro (γk := γk) (Er := Er) (h := by rw [hEr]; rfl)) $$ Hkeep
  have h' := wp_Start srv γA ci TM (.on γa) E ρ ρ.rd Er γrn b (W64 0) (W64 0) (W64 0) x₀ N
  simp only [AuthC.isOn] at h'
  wp_apply h' $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, #Hlb, Hgo, Hlg3, Hsr, -⟩
  · iframe; iframe #
    ipureintro; exact ⟨hγa, Hrb48, HrbN, by trivial⟩
  subst hEr hx₀
  iunfold srvStartReaders at Hsr
  icases Hsr with ⟨Hrslots, -⟩
  -- (per-type stage B2) the run pool's share of the read loop's slots
  icases srvStartReaders_split srv ρ.rd $$ Hrslots with ⟨Hrslots, Hrun⟩
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists γa
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [hγa]; rfl
  ihave #Hreq' : isServerReqM E.authOn srv E { ρ with wait := γw } $$ []
  · rw [hon]; iexact Hreq
  ihave #Hrd' : isServerReadM E.authOn srv E ρ.rd $$ []
  · rw [hon]; iexact Hrd
  iclear Hreq Hrd
  -- (auth-lease S4) the lessor's reader side at the member's mode
  ihave #Hlr : srvLeaseRd srv E m $$ []
  · iapply srvLeaseRd_of_srvInv srv E m _ $$ Hlsrv
  iapply memberUpOn_intro _ _ _ _ _ _ _ E _ γw m
  -- (per-type stage B2) the raw run-pool stocks first, framed explicitly; the pure part last (the
  -- configuration is found by the framing)
  isplitr
  rotate_left
  · isplitl [Hstk]
    · iexact Hstk
    isplitl [Hrun]
    · iexact Hrun
    iframe
    iframe #
    isplitl [Htokp]
    · iunfold srvPeerCtl
      iexists τ
      iframe Hnm Htokp
    -- the TLS fallback off: the configuration's `ClientCertAuthEnabled` is the default `false`
    isplitr
    · iintro !> #Ht
      iapply srvTLSId_false srv $$ [Ht]
      iframe Ht
      iExactEq Hcca; rfl
    -- (auth-lease S4) the lessor's reader side `Hlr` is framed by `iframe #` above
    iapply HBF; ipureintro; first | rfl | trivial
  ipureintro; exact ⟨hagree, hγa, rfl, rfl, rfl⟩

end proof

end etcdstart
end EtcdGrove
end Perennial
