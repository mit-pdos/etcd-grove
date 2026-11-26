/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/MainLogger.lean` (N5, `notes/etcd-dist-plan.md`
§19). Lean-first (no Rocq counterpart).

`MainLogger(c, lg)` on member `i`'s machine: `proxyEnvSet()` (its `false` gives `noProxyEnv`) and `inCluster(c)`
return at once otherwise. Member `i`'s share of the start (`memberShareD`) unpacked as putgetK's member does
(`putgetk/Member.lean`): its `memberBoot` from its slice (`etcdstart.memberBoot_of_slice`, at the member's record
`{ c.γ with reg := c.reg id }`), `bootstrap`'s contract from the interim axiom (`bootPremiseDist_of_specDist`, what
Go computes at its URLs `BootGoD`), the request names' KV names `kvCongr` to the cluster's view's (O1 option B,
`notes/etcd-dist-plan.md` §18.3, no publication). `serverConfig(c, lg)`'s
configuration (`memberCfg`, auth off) to `NewServer` on a member machine (`NewServer.specG_dist` at auth off and the
share's compaction mode; every other peer's address from the start's `peerAddrFactsAt`, of the same cluster; the
member's lessor at `c.ls id`, its half and slot from the share's `memberNamesShare`; `etcdURLsFit` from the
deployment's `addrOk`), its post made `memberBuiltL` (as `etcdstart.newServerMode`) and split (`memberBuiltL_split`)
before `s.Start()` (`wp_Start_builtL`); `net.Listen` at the member's own peer address (its `httpAddrAt`), etcd's peer handler served on
it by a goroutine (`NewPeerHandler_dist`, `PeerServe_dist`); `<-s.ReadyNotify()` (the broadcast idiom's receive);
`etcdstart.Serve` on a member machine (`Serve_dist`, at the view's lessor `c.ls id` and the start's lease mode `lm`);
`holdForever()` does not return.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainLogger
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.proxyEnvSet
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.inCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.serverConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.holdForever
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewPeerHandlerDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.PeerServeDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReadyNotify
public import Spec.net.ListenProto
public import Spec.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.raft.v3.BootMarshal
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Start
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberSplit
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 6400000 in
theorem MainLogger.wp_proof
    (wp_proxyEnvSet : proxyEnvSet.spec (GF := GF) (hG := hG))
    (wp_inCluster : inCluster.spec (GF := GF) (hG := hG))
    (wp_serverConfig : serverConfig.spec (GF := GF) (hG := hG))
    (wp_NewServer_dist : ∀ [π : NetProtoGS] (on cmp : Bool), NewServer.specG_dist (GF := GF) (hG := hG) on cmp)
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_ListenProto : net.Listen.specProto (GF := GF) (hG := hG))
    (wp_NewPeerHandler_dist : NewPeerHandler_dist.spec (GF := GF) (hG := hG))
    (wp_PeerServe_dist : PeerServe_dist.spec (GF := GF) (hG := hG))
    (wp_ReadyNotify : EtcdServer.ReadyNotify.spec (GF := GF) (hG := hG))
    (wp_Serve_dist : Serve_dist.spec (GF := GF) (hG := hG))
    (wp_holdForever : holdForever.spec (GF := GF) (hG := hG))
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG))
    (wp_bootstrap_dist : ∀ [π : NetProtoGS] [MemStorReg GF],
      _root_.Perennial.EtcdGrove.bootstrap.specDist (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    MainLogger.spec (GF := GF) (hG := hG) := by
  intro CS π TB RB cv lg d i m ps ctxs boot lm Hwf Hm Hauth Hfips Hbf Hbgo Hrun HLv Haf Hbuq Hrf Hdbo Hms
  have Htb : threadBound GF ≤ 2 ^ 28 := TB.threadBound_le
  have Hrb48 : receiptBound GF ≤ 2 ^ 48 := RB.receiptBound_le
  have HrbN : receiptBound GF ≤ (2 ^ 48 - 1) + 1 := by have := Hrb48; omega
  have HwbN : (2 ^ 48 - 1) + 7 + bootWB ≤ backend.wbInit := by unfold bootWB backend.wbInit; omega
  wp_start as ⟨#Hzlg, Htok, #Hcfg, %Hvoff, Hwa, Hshare⟩
  -- the configuration: member `i`'s
  iunfold configRepr at Hcfg
  icases Hcfg with ⟨%m', %Hm', #Hcl⟩
  obtain ⟨Hm'', Hcv⟩ := Hm'
  obtain rfl : m = m' := Option.some.inj (Hm.symm.trans Hm'')
  generalize hcl : cv.Cluster' = cl at Hcv
  subst Hcv
  -- the deployment's pure facts
  obtain ⟨-, Hnnd, Hnok, Hmlen, Hnlen⟩ := Hwf.members
  simp only [typed.maxMembers] at Hmlen
  have HnL : m.name.length ≤ 200 := by
    have h := Hnlen m (List.mem_of_getElem? Hm); unfold typed.maxNameLen at h; exact h
  obtain ⟨Hidnd, H0⟩ := Hwf.idsNodup
  have Hdok : netDirOk (dirD d) := dirD_ok Hwf
  -- the share of the start
  icases Hshare with ⟨%c, Hshare⟩
  iunfold memberShareD at Hshare
  isimp only [Hauth] at Hshare
  icases Hshare with ⟨%cmp, %cret, %Hsh, #Hcf, #Hpaf, Hsl, #Hat, Hnames⟩
  -- the member's lessor name's half and slot (`NewServer_dist`'s `Hlslot`); its auth names are unused (auth off)
  iunfold memberNamesShare at Hnames
  icases Hnames with ⟨Hlh, Hlslot, -⟩
  obtain ⟨Hcok, Hbcfg, -⟩ := Hsh
  obtain ⟨hvs, hrule, hboot, hc0, hch, hlog, hiss, hwn, hfs, hgen, hkc, hkr, hklg, hpo, hns, hgps, -⟩ := Hcok
  rw [members_getD d i m Hm]
  generalize hidm : d.ids.getD i (W64 0) = idm
  have hidm' : idm = memberId (go!"http://" ++ m.peer) d.token := by
    rw [← hidm]; exact ids_getD d i m Hm
  have hidmem : idm ∈ d.ids := by rw [hidm']; exact List.mem_of_getElem? (ids_getElem? d i m Hm)
  have Hdir : go!"http://" ++ m.peer ∈ dirD d idm := by rw [hidm', dirD_self d Hidnd i m Hm]; simp
  -- the member's addresses within etcd's URL bounds (`NewServer_dist`'s `etcdURLsFit`), from the deployment's
  -- `addrOk` (one URL per member, `http://` and the address)
  have Hmm : m ∈ d.members := List.mem_of_getElem? Hm
  have Hpf : addrFits m.peer := by
    refine etcd_dist.addrOk_addrFits (Hwf.addrs.2 m.peer ?_)
    unfold Deployment.addrs
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, Hmm, by simp⟩)
  have Hcf : addrFits m.client := by
    refine etcd_dist.addrOk_addrFits (Hwf.addrs.2 m.client ?_)
    unfold Deployment.addrs
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, Hmm, by simp⟩)
  have Hbc : rafthttp.bootCfg (dirD d) ps := rafthttp.bootCfg_of_le _ ps
    (fun f => by rw [dirD_ne_nil Hwf, Hbgo.perm.mem_iff])
    (by rw [Hbgo.perm.length_eq, ids_length]; unfold peersMax; exact Nat.le_trans Hmlen (by decide))
  obtain ⟨Hpfxnd, -, -⟩ := idPfxsOf_ok d.ids Hwf.idsLow.1 Hwf.idsLow.2
  have Hx : xsOf d.ids c.idx (idPfxOf (W16 (uint.Z idm))) = (c.idx idm).slog :=
    xsOf_at _ _ Hpfxnd _ hidmem
  have hblen : boot.length = d.ids.length := by rw [Hbf.boot.1, Hbgo.perm.length_eq]
  have Hbl : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen, ids_length]; omega
  -- `proto.Marshal`'s bytes at the bootstrap log's conf changes
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hbf.wire $$ Hpp
  -- the member's bootstrap contract, given the round tripper's, from the interim axiom
  ihave #Pesrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  haveI : ThreadBoundLe GF (2 ^ 29) := ⟨Nat.le_trans TB.threadBound_le (by decide)⟩
  haveI : ReceiptBoundLe GF (2 ^ 60) := ⟨Nat.le_trans RB.receiptBound_le (by decide)⟩
  obtain ⟨Hidr, HU⟩ := Hbgo.go (gmOf m) idm (by rw [hidm']; exact gms_zip_mem d i m Hm)
  ihave #Hbp := bootPremiseDist_of_specDist wp_bootstrap_dist (2 ^ 48 - 1) ps
      (LogEntry.toEntries boot 0) ctxs (dirD d) d.token (gmOf m).Name' (urlsN (gmsD d) (gmOf m)) idm Hfips
      Hidr HU ⟨boot, Hbf.boot, rfl⟩ $$ Pesrv
  -- the member's peer address and every other peer's, at its record
  ihave #Hown : httpAddrAt (Gg := hG.goose_globalGS) { c.γ with reg := c.reg idm } idm m.peer $$ []
  · iapply (peerFactAt c.γ { c.γ with reg := c.reg idm } rfl d idm m.peer Hdir)
    iexact Hpaf
  ihave #Hpeers : □ ∀ (pid : w64) (a : GoString),
      ⌜pid ∈ ({ c.γ with reg := c.reg idm } : SrvRaft).vs ∧ pid ≠ idm ∧ go!"http://" ++ a ∈ dirD d pid⌝ -∗
      httpAddrAt (Gg := hG.goose_globalGS) { c.γ with reg := c.reg idm } pid a $$ []
  · imodintro
    iintro %pid %a %ha
    iapply (peerFactAt c.γ { c.γ with reg := c.reg idm } rfl d pid a ha.2.2)
    iexact Hpaf
  -- the member's `memberBoot`, from its slice
  have γm : mvcc.api.MvccName := Classical.choice hne.1
  imod (etcdstart.memberBoot_of_slice c.γ ps ctxs (LogEntry.toEntries boot 0) (c.reg idm)
      c.issued c.cnt c.wn c.fs c.gen c.γk (fun _ => srvFloorFacts (GF := GF) (c.idx idm).slog)
      idm γm (c.idx idm) (c.cok idm) (c.rev idm)
      (xsOf d.ids c.idx (idPfxOf (W16 (uint.Z idm))))
      Hx hiss hwn hfs hgen hc0 hch hlog hvs cmp hkc lm Hrun hklg (fun h => hgps idm hidmem h)
      hpo rfl hns) $$ Hmarsh Hcf Hsl with ⟨%ρ, %Hρ, Hmb⟩
  -- the request names' KV names agree with the cluster's view's
  have Hcg : kvCongr ρ.rd.kv c.view.kv := Hρ.2.2.2.2.2
  have hcr : ρ.rd.kv.cret = cret := by
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := Hcg; rw [h]; exact hkr
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  (try wp_auto)
  -- `proxyEnvSet()`: return if set
  wp_apply wp_proxyEnvSet as %bp Hnp
  cases bp
  rotate_left
  · (try wp_auto)
    iapply HΦ; itrivial
  try simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hnp with #Hnp
  (try wp_auto)
  -- `!inCluster(c)`: return
  wp_apply (wp_inCluster _ (d.members.map peerOf)) $$ [] as %bc -
  · iExactEq Hcl; rfl
  cases bc
  · simp only [Bool.not_false]
    (try wp_auto)
    iapply HΦ; itrivial
  simp only [Bool.not_true]
  (try wp_auto)
  -- `serverConfig(c, lg)`
  wp_apply (wp_serverConfig _ (d.members.map peerOf) lg (by rw [peerOf_names]; exact Hnnd)) $$ []
    as %cfg ⟨%cluster, %M, %pu, %cu, %fgp, %Hsc, #Hclm, #Hsls, #Hpu, #Hcu, #Hfg, #Hfgc, #Hflc⟩
  · iExactEq Hcl; rfl
  obtain ⟨Hcfgeq, Hfgp, Hdom⟩ := Hsc
  rw [memberCfg_off (configOf d m cl) lg cluster pu cu _ Hauth] at Hcfgeq
  subst Hcfgeq
  have HU8 : ∀ k, (M.lookup k).isSome → utf8Valid k := by
    intro k hk
    have h := (Hdom k).1 hk
    rw [peerOf_names] at h
    obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 h
    exact utf8Valid_of_ascii _ (nameOk_ascii _ (Hnok mm hmm))
  have Hurls : urlsN (gmsD d) (gmOf m) ⟨[httpURL m.peer], [httpURL m.client], M, iuOf (gmsD d)⟩ :=
    ⟨rfl, rfl, fun n => by rw [Hdom n, peerOf_names, ← gms_names], rfl⟩
  ihave #Hsls' : [∗map] n ↦ sl ∈ M, sl ↦*□ iuOf (gmsD d) n $$ []
  · rw [← iuP_peerOf]; iexact Hsls
  have Hcmpcfg : v3compactor.bootCfg (if d.cfg.retention = W64 0 then go!"" else d.cfg.compactorMode)
      d.cfg.retention cmp ρ.rd.kv.cret := by
    rw [hcr]
    by_cases h0 : d.cfg.retention = W64 0
    · exact v3compactor.bootCfg_off _ _ _ _ h0
    · simp only [h0, ↓reduceIte]; exact Hbcfg
  iunfold memberBoot at Hmb
  icases Hmb with ⟨%Hρb, %Hnsn, Hnboot, #Hsrl, #Hidc, #Hpfxi, #Hidk, #HNZ0, #Hpmint, #Hrdctx,
    Hids, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv, Hreg, %γd, %Hsloc, Hsdir⟩
  obtain ⟨hraft, hc0', hch', hlog', hpfx, hΦs, hcmp0, hkcmp, hNx, hslg⟩ := Hρb
  have hblen' : ({ c.γ with reg := c.reg idm } : SrvRaft).boot.length ≤ 2 ^ 60 := by
    show c.γ.boot.length ≤ 2 ^ 60; rw [hboot]; exact Hbl
  have hrule' : ({ c.γ with reg := c.reg idm } : SrvRaft).rule =
      srvRule (W64 0) ({ c.γ with reg := c.reg idm } : SrvRaft).boot := by
    show c.γ.rule = srvRule (W64 0) c.γ.boot; rw [hboot]; exact hrule
  have Hbc' : rafthttp.bootCfg (dirD d) ({ c.γ with reg := c.reg idm } : SrvRaft).vs := by
    show rafthttp.bootCfg (dirD d) c.γ.vs; rw [hvs]; exact Hbc
  -- `NewServer` on a member machine, at auth off and the share's compaction mode, the member's lessor at `c.ls idm`
  ihave Hls : (ghostMapAuth (c.ls idm) (1 : Qp).half (∅ : GMap Bool lease.LessorGV) ∗ lease.lessorSlot (c.ls idm))
      $$ [Hlh Hlslot]
  · isplitl [Hlh]
    · iexact Hlh
    iexact Hlslot
  letI : MemStorReg GF := ⟨c.reg idm⟩
  have wpNS : NewServer.specG_dist (GF := GF) (hG := hG) false cmp := wp_NewServer_dist false cmp
  simp only [NewServer.specG_dist, kvInvM_false, srvErM_false, srvBuiltG_false, bootKVOf_false] at wpNS
  (try wp_auto)
  wp_apply (wpNS _ ⟨[httpURL m.peer], [httpURL m.client], M, iuOf (gmsD d)⟩
      { c.γ with reg := c.reg idm } idm ctxs ρ
      (env₀ γm (c.idx idm) (c.rev idm) (srvApi.kvNx ρ.rd false) cmp) (2 ^ 48 - 1)
      (fun _ => srvFloorFacts (GF := GF) (c.idx idm).slog) (dirD d) γd lm (c.au idm) (c.ls idm)
      hraft hrule' (fun h => absurd h Hnsn) hc0' hch' hlog' hkcmp
      (show mvcc.batchLimitOk (W64 0) from ⟨by simp, by simp [mvcc.rangeLimitMax]⟩)
      (show v3rpc.etcdMaxRequestBytesOk (uint.nat (W64 1572864)) by
        simp [v3rpc.etcdMaxRequestBytesOk, v3rpc.etcdMaxRecvMsgSize, v3rpc.grpcOverheadBytes])
      v3rpc.maxTxnOpsOk_default Hcmpcfg (fun _ => trivial) hcmp0 hNx Htb Hrb48 HrbN
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩ Hdok (peerURLsDir_httpURL _ idm m.peer Hdok Hdir)
      (etcdURLsFit_httpURL m.peer Hpf) (etcdURLsFit_httpURL m.client Hcf)
      (raftNode.bootCfg_of _ rfl) Hbc'
      (fun h => absurd h Bool.false_ne_true)
      (lease.bootCfg_of_run hslg (fun h => absurd h Bool.false_ne_true))
      (bootCfgOk_of _ rfl rfl rfl rfl ⟨rfl, rfl⟩ rfl)
      ⟨rfl, discoveryZero_len, HU8, dirFits_memberDataDir m.name HnL⟩ HwbN)
    $$ [Htok Hnboot Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hsdir Hwa Hls] as %srv %err Hres
  · iunfold bootPremiseDist at Hbp
    iframe
    iframe #
    isplitr
    · iExactEq Hfg; rfl
    isplitr
    · iExactEq Hflc; rfl
    isplitr
    · iapply Hbp
      · ipureintro
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, Hurls, hvs, hrule, hboot⟩
      · iunfold bootRTOk
        isplitr
        · iexact Hpeers
        · iexact Hnp
    isplitr
    · iExactEq Hzlg; rfl
    isplitr
    · ipureintro; exact Hvoff
    isplitr
    · iunfold bootCfgRO
      isplitr
      · iExactEq Hpu; rfl
      isplitr
      · iExactEq Hcu; rfl
      isplitr
      · iExactEq Hclm; rfl
      iExactEq Hsls'; rfl
    isplitl [Hreg]
    · iunfold memStorRegAuth; iExactEq Hreg; rfl
    isplitl [Hwa]
    · iapply memberCfg_bootRes
      iExactEq Hwa; rfl
    isplitr
    · ipureintro; exact Hsloc
    isplitr
    · ipureintro; exact Haf
    isplitr
    · ipureintro; exact Hbuq
    isplitr
    · ipureintro; exact Hdbo
    isplitr
    · ipureintro; exact storage.openMmapOk_of_quota_zero _ rfl
    -- `Hγa` at auth off
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  icases Hres with (⟨⟨%Hsn, %Herr⟩, Htok⟩ | ⟨%Herr, Htok, %γn, %γA, %ci, %TM, %E, %γrn, %b, %γk, %τ, %HE,
    Hstk, #Hwb, Hbuilt, Hgap, Hserve, Hsv, Hmon, Hrc, #Hnm, Htokp, HServeR, #Hlsrv, #Httl, -, -, Hkeep⟩)
  · -- `NewServer` failed: return
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; itrivial
  subst Herr
  obtain ⟨HγnN, Hγndir, HEa, HEon, -, HEl⟩ := HE
  -- `NewServer`'s post as `memberBuilt` (as `etcdstart.newServerMode`)
  ihave Hsb := isServerBuilt_of_gap srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV
      (2 ^ 48 - 1) $$ [Hbuilt Hgap]
  · iframe
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm, #Hmw⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr
    · iExactEq Hmc; rfl
    isplitr
    · iExactEq Hmd; rfl
    isplitr
    · iexists (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #fgp)
      isplitr
      · iExactEq Hmf; rfl
      iexact Hfgc
    iExactEq Hmw; rfl
  ihave #Hlr : srvLeaseRd srv E lm $$ []
  · iapply srvLeaseRd_of_srvInv srv E lm _ $$ Hlsrv
  ihave Hmb : memberBuiltL srv ρ (env₀ γm (c.idx idm) (c.rev idm) (srvApi.kvNx ρ.rd false) cmp) lg γn idm
      (2 ^ 48 - 1) false lm (c.ls idm) $$ [Hstk Hsb Hserve Hsv Hlgm Hrc Htokp HServeR Hkeep]
  · iunfold memberBuiltL
    iexists γA, ci, TM, E, γrn, b, _, γk, τ
    isplitr
    rotate_left
    isplitl [Hstk]
    · iexact Hstk
    isplitr
    · iexact Hwb
    isplitl [Hsb]
    · iexact Hsb
    isplitl [Hserve]
    · iexact Hserve
    isplitl [Hsv]
    · iexact Hsv
    isplitr
    · iexact Hoff
    isplitl [Hlgm]
    · iexact Hlgm
    isplitl [Hrc]
    · iexact Hrc
    isplitr
    · iexact Hnm
    isplitl [Htokp]
    · iexact Htokp
    isplitl [HServeR]
    · simp only [etcdstart.memberPeerServeRes, Bool.false_eq_true, ↓reduceIte]
      iexact HServeR
    isplitr
    · iexact Hlr
    iexact Hkeep
    ipureintro; exact ⟨HEa, HEon, rfl, rfl, rfl, HEl⟩
  -- split before `Start`: the ready channel's receiver share, the peer handler's server's resources
  icases memberBuiltL_split srv ρ (env₀ γm (c.idx idm) (c.rev idm) (srvApi.kvNx ρ.rd false) cmp) lg γn idm
    (2 ^ 48 - 1) lm (c.ls idm) $$ Hmb with ⟨Hmb, #Hrr, %τ', #Hnm', Hsr⟩
  (try wp_auto)
  -- `s.Start()`
  wp_apply (wp_Start_builtL wp_Start srv ρ (env₀ γm (c.idx idm) (c.rev idm) (srvApi.kvNx ρ.rd false) cmp) lg γn
      idm (2 ^ 48 - 1) true HrbN lm (c.ls idm) Hrb48) $$ [Hmb Htok] as Hup
  · isplitl [Hmb]
    · iexact Hmb
    iexact Htok
  (try wp_auto)
  -- `net.Listen("tcp", c.Peer)`: at the member's own peer address
  wp_apply (wp_ListenProto go!"tcp" m.peer (httpPeerSvc (GF := GF) c.γ.cl idm).1
      (httpPeerSvc (GF := GF) c.γ.cl idm).2) $$ [] as %pl %lerr Hl
  · isplitr
    · ipureintro; rfl
    iExactEq Hown; rfl
  icases Hl with (⟨%Hle, Hlo⟩ | %Hle)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hle
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hle
  (try wp_auto)
  -- `go http.Serve(pl, etcdhttp.NewPeerHandler(lg, s))`
  icases memberUpL_req srv ρ (env₀ γm (c.idx idm) (c.rev idm) (srvApi.kvNx ρ.rd false) cmp) lg γn idm lm (c.ls idm)
    $$ Hup with ⟨Hup, %Er, %ρr, #Hreq⟩
  wp_apply (wp_NewPeerHandler_dist lg srv γn idm τ' false Er ρr) $$ [] as %h #Hh
  · isplitr
    · iexact Hzlg
    isplitr
    · iexact Hnm'
    iexact Hreq
  (try wp_auto)
  wp_apply wp_fork $$ [Hsr Hlo]
  · (try wp_auto)
    wp_apply (wp_PeerServe_dist pl h m.peer srv γn idm τ' false Er ρr { c.γ with reg := c.reg idm } HγnN
        (by rw [Hγndir]; exact Hdir)) $$ [Hsr Hlo] as %perr -
    · isplitr
      · iexact Hown
      isplitl [Hlo]
      · iexact Hlo
      isplitr
      · iexact Hh
      isplitr
      · iexact Hnm'
      isplitr
      · iexact Hreq
      iexact Hsr
    ipureintro; exact isPanic_intoVal perr
  (try wp_auto)
  -- `<-s.ReadyNotify()`
  wp_apply (wp_ReadyNotify srv) $$ [] as %rdc ⟨%γrd, #Hbc⟩
  · iexact Hrr
  ihave #Hich := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
  wp_apply_core chan.wp_receive (V := Unit) rdc γrd $$ Hich
  iintro ⟨-, -, -, -⟩
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
  iintro ⟨-, -⟩
  (try wp_auto)
  -- `etcdstart.Serve(s, c.Client)` on a member machine
  wp_apply (wp_Serve_dist srv m.client ρ (env₀ γm (c.idx idm) (c.rev idm) (srvApi.kvNx ρ.rd false) cmp) lg γn
      idm c.view (fun h => absurd h Bool.false_ne_true)) $$ [Hup] as %serr -
  · isplitr
    · iexact Hzlg
    isplitr
    · ipureintro; exact ⟨Hms, Hbuq, Hrf, HLv, Hcg, Or.inl rfl⟩
    isplitl [Hup]
    · -- the auth-off branch, at the view's lessor `c.ls idm` and mode `c.γk.lm = lm` (`ClusterOk`'s)
      simp only [ClusterNames.view, Bool.false_eq_true, ↓reduceIte, hklg]
      iexact Hup
    iexact Hat
  cases serr with
  | ok ei =>
    (try wp_auto)
    iapply HΦ; itrivial
  | nil =>
  (try wp_auto)
  -- `holdForever()`: it does not return
  wp_apply wp_holdForever as HF
  iexfalso
  iexact HF

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial

end
