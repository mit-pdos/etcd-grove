/- Lean-first (no Rocq counterpart).

# `etcd/dist/server`: member `i`'s machine's boot (N5, `notes/etcd-dist-plan.md` §19)

`member_boot_dist`: member `i`'s boot program (`serverProg d i`: `server.initialize' #()`, then
`server.MainDeployment(d, i)`) of a well-formed deployment `d` is safe at `etcd_safe_nocrash`'s bounds
(`Net.DistBootWpSLT etcdThreads 0 etcdSteps`, what `EtcdBootNC` asks of each machine) from its share of the
cluster's start (`memberShareD`, `MemberDefs.lean`) and its whole start, as putgetK's `member_bootK`
(`dist/putgetk/AdequacyMember.lean`): the file extension's start, the member's WAL area from its machine's files
(`ServerStart`), the package's initialization (its registration rights allocated here, `server_regQsOk`), the
deployment's literal (`wp_deploymentLit`), then `MainDeployment.wp_proof` with every callee plugged in: the
proved ones (`MainDeploymentLogger`, `ConfigOf`, `MainLogger` and its leaves, `deployment`'s `wp_WellFormed`,
`EtcdServer.wp_Start`, `ReadyNotify`, `net.Listen.wp_proofProto` over Net's `Listen`, `holdForever` over
`time.Sleep`, `zap.NewNop`) and the interim trust-boundary axioms `NewServer_dist.wp_proof`,
`NewPeerHandler_dist.wp_proof`, `PeerServe_dist.wp_proof`, `Serve_dist.wp_proof`, `bootstrap.wp_proof_dist` and
`os.Getenv.wp_proofEnv` (and `proto.MarshalBootConfChange.wp_proof`, as putgetK's). Each interim axiom enters
here only, as its spec is a hypothesis of the proof that uses it.

Its one hypothesis beyond `EtcdBootNC`'s premises: the scope `Hauth : d.cfg.auth = true → lm = .revocable →
lease.leasesNoExpiry` (option (a), `notes/specs-only/ledger.md` 2026-11-26: with auth on, in the revocable lease mode
no lease expires). Go's values at the members' URLs (`BootGoD`) follow from the well-formed deployment at the
pinned `BootFacts` (`BootGoD.of_wf`, at `distPs d`, `distCtxs d`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainDeployment
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.BootGoD
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainDeploymentLogger
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainLogger
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.ConfigOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.serverConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.inCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.proxyEnvSet
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.holdForever
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewPeerHandlerDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.PeerServeDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReadyNotify
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapDist
public import Proof.net.ListenProto
public import Proof.os.GetenvEnv
public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.raft.v3 Net
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

set_option maxHeartbeats 3200000 in
/-- **Member `i`'s machine's boot** (see the file header): the form `EtcdBootNC` asks of each member machine,
from its share `∃ c, memberShareD c d (distPs d) (distCtxs d) boot i`. -/
theorem member_boot_dist [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
    (d : Deployment) (Hd : d.WellFormed)
    (boot : List LogEntry) (Hbf : BootFacts d boot) (Henv : EtcdEnv d) (HEnv : EtcdVerifyOff)
    (Hfips : crypto.fips140.GodebugFips140Off)
    (lm : lease.Mode) (Hlm : lm = .mono → lease.leasesNoExpiry)
    (Hauth : d.cfg.auth = true → lm = .revocable → lease.leasesNoExpiry)
    (i : Nat) (m : Member) (hm : d.members[i]? = some m) (σ : state) (Hσ : ServerStart m σ)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS] :
    Net.DistBootWpSLT etcdThreads 0 etcdSteps (serverProg d i) σ
      (iprop(∃ c : ClusterNames, memberShareD (GF := etcdDistGF) c lm d (distPs d) (distCtxs d) boot i)) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI : ReceiptBoundLe etcdDistGF (2 ^ 62) := ⟨by unfold etcdSteps at hrb; omega⟩
  haveI : ReceiptBoundLe etcdDistGF (2 ^ 48) := ⟨by unfold etcdSteps at hrb; omega⟩
  haveI : ThreadBoundLe etcdDistGF (2 ^ 28) := ⟨by rw [hT]; unfold etcdThreads; omega⟩
  haveI := etcdFsSemOk
  have HLv : srvLevels (GF := etcdDistGF) := by
    unfold srvLevels; rw [hT]; unfold etcdThreads srvLevelK srvRevokeK; omega
  -- the running server's lease premise at the start's mode (the revocable mode's open case by
  -- `revokeExpiredLeases`' linked result, as leaseexpiry's `MainLinked`)
  have Hrun : lease.runCfg (GF := etcdDistGF) lm lm := by
    cases lm with
    | none => exact lease.runCfg_none
    | mono => exact lease.runCfg_mono (Hlm rfl)
    | revocable =>
      exact lease.runCfg_revocable (srvRevokeLevels_of_srvLevels HLv)
        (srvRevokeOpen_intro EtcdServer.wp_revokeExpiredLeases)
  obtain ⟨-, -, -, -, hnames⟩ := Hd.members
  have hnl : m.name.length ≤ 200 := by
    have := hnames m (List.mem_of_getElem? hm); unfold typed.maxNameLen at this; exact this
  iintro Hshare Hls Hgs Htok
  -- the machine's registration rights (as `serverBadWp`)
  imod (prometheus.regKeys_alloc (GF := etcdDistGF) server.regQs server_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS etcdDistGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := etcdDistGF) server.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty (server.getIsPkgInit (GF := etcdDistGF)) $$ Hgs
  ihave #Hvoff : ⌜EtcdVerifyOff⌝ $$ []
  · ipureintro; exact HEnv
  imod etcdNetFs_start σ Hσ.1 $$ Hls with ⟨#Hos, -, Htree⟩
  imodintro
  -- the member's WAL area, from its machine's files
  iapply (wp_walAreas ⟨etcdDistGF_allG⟩ etcdFsExts_sat etcdFsExts_satL (extLocal Fs.fsExt σ.world) Hσ.1
    [memberDataDir m.name] (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) Hσ.2
    (fun dd hdd => by
      rw [List.mem_singleton.1 hdd]
      exact dirFits_srvWalDirOf_memberDataDir m.name hnl)
    inferInstance (serverProg d i) rfl _) $$ Hos Htree
  iintro Hareas
  icases BigSepL.bigSepL_cons.1 $$ Hareas with ⟨Hwa, -⟩
  -- `server.initialize' #()`
  unfold serverProg
  wp_apply (server.wp_initialize' _ server.getIsPkgInit_wf) $$ [Hown Hns] as ⟨-, #Hpkg⟩
  · iframe
  -- the deployment's literal
  wp_bind (deploymentLit d)
  iapply wp_deploymentLit
  iintro %v #Hrepr
  -- `MainDeployment(d, i)`, every callee plugged in
  wp_apply (MainDeployment.wp_proof zap.NewNop.wp_proof
      (MainDeploymentLogger.wp_proof wp_WellFormed ConfigOf.wp_proof
        (MainLogger.wp_proof (proxyEnvSet.wp_proof os.Getenv.wp_proofEnv) inCluster.wp_proof
          (serverConfig.wp_proof etcdstart.features.wp_NewDefaultServerFeatureGate)
          (fun on cmp => NewServer_dist.wp_proof on cmp) EtcdServer.wp_Start
          (net.Listen.wp_proofProto _root_.Perennial.net.Listen.wp_proof)
          NewPeerHandler_dist.wp_proof PeerServe_dist.wp_proof EtcdServer.ReadyNotify.wp_proof
          Serve_dist.wp_proof (holdForever.wp_proof time.Sleep.wp_proof)
          _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof
          (fun {_} {_} => _root_.Perennial.EtcdGrove.bootstrap.wp_proof_dist)
          mvcc.api.mvccApi_names_nonempty_law_holds))
      v d i m (distPs d) (distCtxs d) boot lm hm Hauth Hfips Hbf (BootGoD.of_wf Hd) Hrun HLv
      Henv.authRecords Henv.underQuota Henv.repliesFit Henv.disk inferInstance)
    $$ [Htok Hwa Hshare]
  · iframe; iframe #
    iintro -
    itrivial
  ipureintro
  rfl

end server
end etcd_dist
end EtcdGrove
end Perennial

end
