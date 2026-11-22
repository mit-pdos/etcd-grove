/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Start.lean`. Lean-first (no Rocq
counterpart); see `InvStart.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.GoAttachTok
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__adjustTicks
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__publishV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__purgeFile
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.monitorFileDescriptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorClusterVersions
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorStorageVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorKVHash
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorCompactHash
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorDowngrade
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__LinearizableReadLoop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]



set_option maxHeartbeats 0 in
/-- **`Start.spec`**, in both auth modes (the auth component's 2c, 2026-11-04: one proof over the
component `C`; until then `wp_proofOff` and `wp_proofOn`, one per mode). -/
theorem EtcdServer.Start.wp_proof
    (hStart : EtcdServer.start.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hAdj : EtcdServer.adjustTicks.spec (GF := GF) (hG := hG))
    (hPub : EtcdServer.publishV3.spec (GF := GF) (hG := hG))
    (hReqT : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (hPurge : EtcdServer.purgeFile.spec (GF := GF) (hG := hG))
    (hMFD : monitorFileDescriptor.spec (GF := GF) (hG := hG))
    (hMCV : EtcdServer.monitorClusterVersions.spec (GF := GF) (hG := hG))
    (hMSV : EtcdServer.monitorStorageVersion.spec (GF := GF) (hG := hG))
    (hRL : read.Read.LinearizableReadLoop.spec (GF := GF) (hG := hG))
    (hKVH : EtcdServer.monitorKVHash.spec (GF := GF) (hG := hG))
    (hCH : EtcdServer.monitorCompactHash.spec (GF := GF) (hG := hG))
    (hDG : EtcdServer.monitorDowngrade.spec (GF := GF) (hG := hG)) :
    EtcdServer.Start.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr Er γn b ai₀ at₀ c₀ x₀ N
  wp_start as ⟨%hC, Hb, Htok, Hlg, Hlgm, Hsv, #Hoff, Hlgd, Hrc⟩
  obtain ⟨hm, hRB, Hrb, Hai0⟩ := hC
  -- (2026-11-02, the cluster-rows stage) the member id field, a voter: the monitors' permission
  icases isServerBuiltC_mid C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N $$ Hb with ⟨Hb, #HmidS, %HmidcS⟩
  -- (prove-ps2-srv) the raft wrapper's contract, for `adjustTicks`
  icases isServerBuiltC_rn C s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N $$ Hb with ⟨Hb, #HrnS⟩
  wp_auto
  wp_apply hStart s γ ci TM C E ρ γr Er γn b ai₀ at₀ c₀ x₀ N $$ [Hb]
    as ⟨%γw, #Hreq, #Hrd, #Hlb, Hst, %γp, %γg, #Hwp, #Hreg, Hgo, Hright⟩
  · iframe #; iframe Hb; ipureintro; exact ⟨hm, hRB, Hrb, Hai0⟩
  iunfold srvStarted at Hst
  iNamed Hst
  ihave Hgr : srvGoResAt s γg $$ [Hgo Htok]
  · iunfold srvGoResAt; iframe Hgo Htok
  ipersist s
  ihave #Hreq' := (isServerReqM_split C.isOn s E _).1 $$ Hreq
  icases Hreq' with ⟨⟨%vq, #Hvq⟩, -⟩
  iunfold srvReqFieldsAtM at Hvq
  icases Hvq with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %HcfgP⟩
  obtain ⟨Hcfg, -⟩ := HcfgP
  ihave #Hrd' := Hrd
  iunfold isServerReadM at Hrd'
  icases Hrd' with ⟨%vd, #Hvd⟩
  iunfold srvReadFieldsAtM at Hvd
  icases Hvd with ⟨-, -, -, -, -, -, -, -, -, #Hlgf, #Hlgn, -, -, -, -, -, -, -, -, -, -,
    #Hstpf, -⟩
  -- (premise-fixes-6) the server's logger a zap logger (the monitors' and `adjustTicks`'s)
  ihave #HlgOk : srvLoggerOk s $$ []
  · iunfold srvLoggerOk; iexists vd.lg; iframe Hlgf Hlgn
  -- (srvloops2, 2026-11-21, bounds B2 for `lgMu`) `GoAttach`'s pool of `lgMu` reader slots
  -- (`raftPool`), from which the goroutines that call `Logger()` borrow one with their level 1
  iunfold srvGoResAt at Hgr
  icases Hgr with ⟨Hwr, Hgt⟩
  iunfold srvWgReaderAt at Hwr
  icases Hwr with ⟨#Hgok, Hwm⟩
  ihave Hgr : srvGoResAt s γg $$ [Hwm Hgt]
  · iunfold srvGoResAt; iunfold srvWgReaderAt; iframe Hwm Hgt; iframe #
  ihave #Hgok' := Hgok
  iunfold srvGoAttachOk at Hgok'
  icases Hgok' with ⟨%gch, %gc, -, -, -, -, -, -, -, #HrP, -⟩
  -- `func() { s.adjustTicks() }`, with `GoAttach`'s `lgMu` pool and the goroutine's level 1
  wp_apply wp_GoAttach_tokT hGA s γg _ iprop(True) $$ [Hgr] as Hgr
  · iframe Hgr
    isplitr
    · itrivial
    iintro !> %Φ' ⟨-, Hrun, Htf⟩ HΦ'
    icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Htf with ⟨G1, Gt2⟩
    (try wp_auto)
    wp_apply hAdj C.isOn s E { wait := γw, rd := ρ.rd } Er γn $$ [G1] as G1
    · iframe #; iframe G1
    iapply HΦ'
    iframe Hrun
    iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
    iframe
  -- `func() { s.publishV3(s.Cfg.ReqTimeout()) }`, with the right to close `readych` (and the `lgMu`
  -- pool and the goroutine's level 1)
  wp_apply wp_GoAttach_tokT hGA s γg _ (srvReadyCloser s) $$ [Hgr Hrc] as Hgr
  · iframe Hgr Hrc
    iintro !> %Φ' ⟨Hrc, Hrun, Htf⟩ HΦ'
    icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Htf with ⟨G1, Gt2⟩
    (try wp_auto)
    wp_apply hReqT (structFieldRef EtcdServer go!"Cfg" s) vq.electionTicks vq.tickMs $$ [] as %d -
    · iframe #
    wp_apply hPub C.isOn s _ E { wait := γw, rd := ρ.rd } $$ [Hrc G1] as G1
    · iframe #; iframe Hrc G1; iapply srvMonitorPermitM_of C.isOn s E { wait := γw, rd := ρ.rd } γn.id HmidcS; iframe Hreq HlgOk HmidS
    iapply HΦ'
    iframe Hrun
    iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
    iframe
  -- `s.purgeFile` (wal-link L2): over `GoAttach`'s protocol and its goroutine's tokens, with no WAL
  -- purge (`srvMonitorsOff`'s `MaxWALFiles`)
  ihave #Hoff' := Hoff
  iunfold srvMonitorsOff at Hoff'
  icases Hoff' with ⟨-, -, -, #Hmwf, -⟩
  wp_apply wp_GoAttach_tokT hGA s γg _ iprop(True) $$ [Hgr] as Hgr
  · iframe Hgr
    isplitr
    · itrivial
    iintro !> %Φ' ⟨-, Hrun, Htf⟩ HΦ'
    wp_apply hPurge s γg $$ [Htf] as Htf
    · iframe #; iframe Htf
    iapply HΦ'
    iframe
  -- `func() { monitorFileDescriptor(s.Logger(), s.stopping) }`
  wp_apply wp_GoAttach_tok hGA s γg _ (srvLgReader s) $$ [Hgr Hlgm] as Hgr
  · iframe Hgr Hlgm
    iintro !> %Φ' ⟨HL, Hrun⟩ HΦ'
    ihave HΦ' := goRunning_frame γg _ $$ Hrun HΦ'
    wp_auto
    wp_apply hLg s vd.lg $$ [HL] as ⟨#Hlg', -⟩
    · iframe #; iframe HL
    wp_apply hMFD $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  -- `s.monitorClusterVersions`, `s.monitorStorageVersion` (each with the `lgMu` pool and
  -- the goroutine's level 1)
  wp_apply wp_GoAttach_tokT hGA s γg _ iprop(True) $$ [Hgr] as Hgr
  · iframe Hgr
    isplitr
    · itrivial
    iintro !> %Φ' ⟨-, Hrun, Htf⟩ HΦ'
    icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Htf with ⟨G1, Gt2⟩
    (try wp_auto)
    wp_apply hMCV C.isOn s E { wait := γw, rd := ρ.rd } $$ [G1] as G1
    · iframe #; iframe G1; iapply srvMonitorPermitM_of C.isOn s E { wait := γw, rd := ρ.rd } γn.id HmidcS; iframe Hreq HlgOk HmidS
    iapply HΦ'
    iframe Hrun
    iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
    iframe
  -- (H2, 2026-11-05) with its receipt at `γg`, the budget's registered name
  wp_apply wp_GoAttach_tokT hGA s γg _ (srvSVRes s E) $$ [Hgr Hsv] as Hgr
  · iframe Hgr Hsv
    iintro !> %Φ' ⟨HL, Hrun, Htf⟩ HΦ'
    icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Htf with ⟨G1, Gt2⟩
    (try wp_auto)
    iunfold goRunning at Hrun
    wp_apply hMSV C.isOn s E { wait := γw, rd := ρ.rd } γp γg.run $$ [HL Hrun G1] as ⟨Hrun, G1⟩
    · iframe #; iframe HL Hrun G1
    iapply HΦ'
    iunfold goRunning
    iframe Hrun
    iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
    iframe
  -- `s.read.LinearizableReadLoop`, verified
  icases Hrl with ⟨%rd, #Hrdf, #Hrlp⟩
  wp_auto
  wp_apply wp_GoAttach_tok hGA s γg _ iprop(isReadLoopPre rd γr Er.RQ (srvReadLR s) (idCred ρ.ids 1) (kvStM C.isOn γr.kv) ∗
      srvReadLR s ∗
      □ (|==> idCred ρ.ids 1)) $$ [Hgr HLR] as Hgr
  · iframe Hgr HLR Hrlp HNR
    iintro !> %Φ' ⟨⟨#Hpre, HL, #HN⟩, Hrun⟩ HΦ'
    ihave HΦ' := goRunning_frame γg _ $$ Hrun HΦ'
    ihave #Hpread : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
    · iPkgInit
    wp_apply hRL rd γr Er.RQ (srvReadLR s) (idCred ρ.ids 1) $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  -- `s.monitorKVHash`, `s.monitorCompactHash`, `s.monitorDowngrade`
  -- (audit B4a) off: `srvMonitorsOff`
  iunfold srvMonitorsOff at Hoff
  icases Hoff with ⟨#Hcct, #Hdct, ⟨%fg, #Hfgf, #Hfgo⟩, -, -⟩
  wp_apply wp_GoAttach_tok hGA s γg _ iprop(True) $$ [Hgr] as Hgr
  · iframe Hgr
    isplitr
    · itrivial
    iintro !> %Φ' ⟨-, Hrun⟩ HΦ'
    ihave HΦ' := goRunning_frame γg _ $$ Hrun HΦ'
    wp_apply hKVH s $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  wp_apply wp_GoAttach_tok hGA s γg _ iprop(True) $$ [Hgr] as Hgr
  · iframe Hgr
    isplitr
    · itrivial
    iintro !> %Φ' ⟨-, Hrun⟩ HΦ'
    ihave HΦ' := goRunning_frame γg _ $$ Hrun HΦ'
    wp_apply hCH s fg $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  wp_apply wp_GoAttach_tok hGA s γg _ (srvLgReader s) $$ [Hgr Hlgd] as Hgr
  · iframe Hgr Hlgd
    iintro !> %Φ' ⟨HL, Hrun⟩ HΦ'
    ihave HΦ' := goRunning_frame γg _ $$ Hrun HΦ'
    wp_apply hDG s vd.lg $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  ihave Hgr := srvGoResAt_close s γg $$ Hgr
  iapply HΦ
  iexists γw
  iunfold srvStartReaders
  iframe Hreq Hrd Hlb Hgr Hlg Hrds Hwgs Hlcs Hright

end proof

end EtcdGrove
end Perennial
