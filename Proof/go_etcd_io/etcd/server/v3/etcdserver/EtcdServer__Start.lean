/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Start.lean`. Lean-first (no Rocq
counterpart); see `InvStart.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorAutoPromoteLearners
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__FeatureEnabled
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
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
  intro s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N Hrb Hai0
  wp_start as ⟨Hb, Htok, Hlg, Hlgm, Hsv, #Hoff, Hlgd, Hrc⟩
  wp_auto
  wp_apply hStart s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N Hrb Hai0 $$ [Hb]
    as ⟨%γw, #Hreq, #Hrd, Hst, %γp, #Hwp⟩
  · iframe #; iframe Hb
  iunfold srvStarted at Hst
  iNamed Hst
  ihave Hgr : srvGoRes s $$ [Hgo Htok]
  · iunfold srvGoRes; iframe Hgo Htok
  ipersist s
  ihave #Hreq' := Hreq
  iunfold isServerReq at Hreq'
  icases Hreq' with ⟨%vq, #Hvq⟩
  iunfold srvReqFieldsAt at Hvq
  icases Hvq with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, -, -, -, -, -, -, -, -, %Hcfg⟩
  ihave #Hrd' := Hrd
  iunfold isServerRead at Hrd'
  icases Hrd' with ⟨%vd, #Hvd⟩
  iunfold srvReadFieldsAt at Hvd
  icases Hvd with ⟨-, -, -, -, -, -, -, -, -, -, #Hlgf, %Hlgn, -, -, -, -, -, -, -, -, -, -, -,
    #Hstpf, -⟩
  -- `func() { s.adjustTicks() }`
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply hAdj s
    iapply HΦ'
    try itrivial
  -- `func() { s.publishV3(s.Cfg.ReqTimeout()) }`, with the right to close `readych`
  wp_apply hGA s _ (srvReadyCloser s) $$ [Hgr Hlg Hrc] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hrc
    iintro !> %Φ' Hrc HΦ'
    wp_auto
    wp_apply hReqT (structFieldRef EtcdServer go!"Cfg" s) vq.electionTicks vq.tickMs $$ [] as %d -
    · iframe #
    wp_apply hPub s _ E { wait := γw, rd := ρ.rd } $$ [Hrc]
    · iframe #; iframe Hrc; iapply srvMonitorPermit_of $$ Hreq
    iapply HΦ'
    try itrivial
  -- `s.purgeFile`
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hPurge s
    iapply HΦ'
    try itrivial
  -- `func() { monitorFileDescriptor(s.Logger(), s.stopping) }`
  wp_apply hGA s _ (srvLgReader s) $$ [Hgr Hlg Hlgm] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hlgm
    iintro !> %Φ' HL HΦ'
    wp_auto
    wp_apply hLg s vd.lg $$ [HL] as ⟨%Hlg', -⟩
    · iframe #; iframe HL; ipureintro; exact Hlgn
    wp_apply hMFD $$ []
    · iframe #; ipureintro; exact Hlg'
    iapply HΦ'
    try itrivial
  -- `s.monitorClusterVersions`, `s.monitorStorageVersion`
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hMCV s E { wait := γw, rd := ρ.rd } $$ []
    · iframe #; iapply srvMonitorPermit_of $$ Hreq
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ (srvSVRes s E) $$ [Hgr Hlg Hsv] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hsv
    iintro !> %Φ' HL HΦ'
    wp_apply hMSV s E { wait := γw, rd := ρ.rd } γp $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  -- `s.read.LinearizableReadLoop`, verified
  icases Hrl with ⟨%rd, #Hrdf, #Hrlp⟩
  wp_auto
  wp_apply hGA s _ iprop(isReadLoopPre rd γr Er.RQ (srvReadLR s) (idCred ρ.ids 1) ∗ srvReadLR s ∗
      □ (|==> idCred ρ.ids 1)) $$ [Hgr Hlg HLR] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg HLR Hrlp HNR
    iintro !> %Φ' ⟨#Hpre, HL, #HN⟩ HΦ'
    ihave #Hpread : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
    · iPkgInit
    wp_apply hRL rd γr Er.RQ (srvReadLR s) (idCred ρ.ids 1) $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  -- `s.monitorKVHash`, `s.monitorCompactHash`, `s.monitorDowngrade`, and `AutoPromoteLearners`
  -- (audit B4a) off: `srvMonitorsOff`
  iunfold srvMonitorsOff at Hoff
  icases Hoff with ⟨#Hcct, #Hdct, %fg, #Hfgf, #Hfgo, #Hfga⟩
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hKVH s $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hCH s fg $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ (srvLgReader s) $$ [Hgr Hlg Hlgd] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hlgd
    iintro !> %Φ' HL HΦ'
    wp_apply hDG s vd.lg $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  -- `if s.FeatureEnabled(features.AutoPromoteLearners) { s.GoAttach(s.monitorAutoPromoteLearners) }`
  wp_apply (EtcdServer.FeatureEnabled.wp_is s fg go!"AutoPromoteLearners" false) $$ []
  · iframe #
  iapply HΦ
  iexists γw
  iframe Hreq Hrd Hgr Hlg Hrds Hwgs Hlcs

set_option maxHeartbeats 0 in
/-- **`s.Start()` with `AutoPromoteLearners` enabled** (`featureIs fg go!"AutoPromoteLearners" true`):
steps through `s.FeatureEnabled(features.AutoPromoteLearners)` returning `true` and attaches
`s.monitorAutoPromoteLearners` via `s.GoAttach`. -/
theorem EtcdServer.Start.wp_proof_autoPromote
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
    (hDG : EtcdServer.monitorDowngrade.spec (GF := GF) (hG := hG))
    (hMAPL : EtcdServer.monitorAutoPromoteLearners.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat)
    (fg : GoInterface) (lg fc stc : Loc)
    (Hrb : receiptBound GF ≤ N + 1) (Hai0 : ai₀ = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ threadTok ∗
        srvLgReader s ∗ srvLgReader s ∗
        srvSVRes s E ∗
        srvCfgFieldAddr s go!"CorruptCheckTime" ↦□ (W64 0) ∗
        srvCfgFieldAddr s go!"DowngradeCheckTime" ↦□ (W64 0) ∗
        srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ fg ∗
        featureIs fg go!"CompactHashCheck" false ∗
        featureIs fg go!"AutoPromoteLearners" true ∗
        srvMonitorAutoPromotePre s lg fc stc ∗
        srvLgReader s ∗ srvLgReader s ∗ notifyReader fc ∗
        srvReadyCloser s }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); ∃ γw : GName, isServerReq s E { ρ with wait := γw } ∗ isServerRead s E γr ∗
        srvGoRes s ∗ srvLgReader s ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          srvReadReader s γr) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 2) (),
          srvWgReader s) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
          ∃ n : Loc, srvLeaderChangedAddr s ↦□ n ∗ notifyReader n) }} := by
  wp_start as ⟨Hb, Htok, Hlg, Hlgm, Hsv, #Hcct, #Hdct, #Hfgf, #Hfgo, #Hfga, #Hmpre,
    Hlgd, Hlgap, Hfcr, Hrc⟩
  wp_auto
  wp_apply hStart s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N Hrb Hai0 $$ [Hb]
    as ⟨%γw, #Hreq, #Hrd, Hst, %γp, #Hwp⟩
  · iframe #; iframe Hb
  iunfold srvStarted at Hst
  iNamed Hst
  ihave Hgr : srvGoRes s $$ [Hgo Htok]
  · iunfold srvGoRes; iframe Hgo Htok
  ipersist s
  ihave #Hreq' := Hreq
  iunfold isServerReq at Hreq'
  icases Hreq' with ⟨%vq, #Hvq⟩
  iunfold srvReqFieldsAt at Hvq
  icases Hvq with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, -, -, -, -, -, -, -, -, %Hcfg⟩
  ihave #Hrd' := Hrd
  iunfold isServerRead at Hrd'
  icases Hrd' with ⟨%vd, #Hvd⟩
  iunfold srvReadFieldsAt at Hvd
  icases Hvd with ⟨-, -, -, -, -, -, -, -, -, -, #Hlgf, %Hlgn, -, -, -, -, -, -, -, -, -, -, -,
    #Hstpf, -⟩
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply hAdj s
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ (srvReadyCloser s) $$ [Hgr Hlg Hrc] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hrc
    iintro !> %Φ' Hrc HΦ'
    wp_auto
    wp_apply hReqT (structFieldRef EtcdServer go!"Cfg" s) vq.electionTicks vq.tickMs $$ [] as %d -
    · iframe #
    wp_apply hPub s _ E { wait := γw, rd := ρ.rd } $$ [Hrc]
    · iframe #; iframe Hrc; iapply srvMonitorPermit_of $$ Hreq
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hPurge s
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ (srvLgReader s) $$ [Hgr Hlg Hlgm] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hlgm
    iintro !> %Φ' HL HΦ'
    wp_auto
    wp_apply hLg s vd.lg $$ [HL] as ⟨%Hlg', -⟩
    · iframe #; iframe HL; ipureintro; exact Hlgn
    wp_apply hMFD $$ []
    · iframe #; ipureintro; exact Hlg'
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hMCV s E { wait := γw, rd := ρ.rd } $$ []
    · iframe #; iapply srvMonitorPermit_of $$ Hreq
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ (srvSVRes s E) $$ [Hgr Hlg Hsv] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hsv
    iintro !> %Φ' HL HΦ'
    wp_apply hMSV s E { wait := γw, rd := ρ.rd } γp $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  icases Hrl with ⟨%rd, #Hrdf, #Hrlp⟩
  wp_auto
  wp_apply hGA s _ iprop(isReadLoopPre rd γr Er.RQ (srvReadLR s) (idCred ρ.ids 1) ∗ srvReadLR s ∗
      □ (|==> idCred ρ.ids 1)) $$ [Hgr Hlg HLR] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg HLR Hrlp HNR
    iintro !> %Φ' ⟨#Hpre, HL, #HN⟩ HΦ'
    ihave #Hpread : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read $$ []
    · iPkgInit
    wp_apply hRL rd γr Er.RQ (srvReadLR s) (idCred ρ.ids 1) $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hKVH s $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ iprop(True) $$ [Hgr Hlg] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg
    isplitr
    · itrivial
    iintro !> %Φ' - HΦ'
    wp_apply hCH s fg $$ []
    · iframe #
    iapply HΦ'
    try itrivial
  wp_apply hGA s _ (srvLgReader s) $$ [Hgr Hlg Hlgd] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hlgd
    iintro !> %Φ' HL HΦ'
    wp_apply hDG s vd.lg $$ [HL]
    · iframe #; iframe HL
    iapply HΦ'
    try itrivial
  wp_apply (EtcdServer.FeatureEnabled.wp_is s fg go!"AutoPromoteLearners" true) $$ []
  · iframe #
  wp_apply hGA s _ iprop(srvLgReader s ∗ notifyReader fc) $$ [Hgr Hlg Hlgap Hfcr] as ⟨Hgr, Hlg⟩
  · iframe Hgr Hlg Hlgap Hfcr
    iintro !> %Φ' ⟨HL, HF⟩ HΦ'
    wp_apply (hMAPL s lg fc stc) $$ [HL HF] as ⟨_, _⟩
    · iframe #; iframe HL HF
    iapply HΦ'
    try itrivial
  iapply HΦ
  iexists γw
  iframe Hreq Hrd Hgr Hlg Hrds Hwgs Hlcs


end proof

end EtcdGrove
end Perennial
