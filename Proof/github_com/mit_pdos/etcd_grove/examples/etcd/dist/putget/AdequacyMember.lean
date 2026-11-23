/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the member machine's boot, against phase 7 S2's draft names (`notes/putget-dist-plan.md`, section 10)

`member_boot`: the member machine's boot program (`putget.initialize' #()`, then `putget.Member(peer, client)`)
is safe from the member's share of the distributed start (`memberShare` at `Pub = putgetPub`) and its whole
start (`DistBootWpSL`: its files' and listeners' start resources, no package initialized, its main thread's
token, the logic's bounds with at least `srvLevelK` receipts), under S2's names (`S : S2Draft`) and the named
hypotheses `MemberBootHyps`. Linked: `Member.wp_proof` at its callees' linked results (`etcdstart`'s `Link`,
`zap.NewNop`'s, `time.Sleep`'s), `putget`'s `wp_initialize'`.

The steps: the file extension's start (`etcdNetFs_start`); the member's WAL area from its machine's files
(`wp_walAreas`, over `MemberFiles`: `FsInit` and `etcdWalAreasInit` of its data directory); the package's
initialization (`wp_initialize'`, from no package initialized and the metric names' rights); `Member`.

**The named hypotheses** (`MemberBootHyps`; no axiom): each a start resource with no source yet on a machine
of a distributed start, where in one process `goose_adequacy_start` hands it out:
* `clearProxy`: `env.ClearProxy`'s spec (`ETCD_VERIFY` off after it), until `os.Unsetenv` has a model
  (a Perennial change, `notes/perennial-changes.md`, 2026-11-23);
* `names`: the rights to register the closure's metric names (`prometheus.namesFree initNames`), until
  `prom-registry` puts the default registry on the machine's own heap;
* `dataDir`: the member's data directory fresh (`dataDirFresh`, an axiomatized token), until it is a
  definition over the machine's file tree (the WAL link, `notes/wal-link-scope.md`; blocked on the fs
  redesign, etcd-grove#15);
* `peerPlain`: a valid address's peer URL `http://a` is plain (`host:port`): a pure fact of `addrOk`, not
  proved yet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Member
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.holdForever
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreas
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Net.Statement.DistBridgeExts

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.raft.v3 Net

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **The member boot's named hypotheses** (see the file header): start resources with no source yet on a
machine of a distributed start. -/
structure MemberBootHyps [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions] : Prop where
  /-- `env.ClearProxy`'s spec, at every ghost state over the Go local context (until `os.Unsetenv` has a
  model). -/
  clearProxy : ∀ hG : HeapGS .hasLC putgetGF,
    dist_env.ClearProxy.spec (GF := putgetGF) (hG := putgetHeapAt hG lctx)
  /-- The rights to register `putget`'s closure's metric names (until `prom-registry`). -/
  names : ⊢@{IProp putgetGF}
    prometheus.namesFree github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.initNames
  /-- The member's data directory fresh (until `dataDirFresh` is defined over the machine's files). -/
  dataDir : ⊢@{IProp putgetGF} dataDirFresh (memberDataDir name)
  /-- A valid address's peer URL is plain (a pure fact, not proved yet). -/
  peerPlain : ∀ a : GoString, Net.addrOk a = true → types.plainPeerURL (go!"http://" ++ a)

set_option maxHeartbeats 1600000 in
/-- **The member machine's boot** (see the file header). -/
theorem member_boot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [log.NewModel] [net.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (HM : MemberBootHyps)
    (peer client : GoString) (hpeer : Net.addrOk peer = true)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : etcdstart.BootFacts id ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcdstart.premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) name peer client n id ctxs
          boot)
    (σm : state) (Hm : MemberFiles σm)
    [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (S : S2Draft putgetGF) (γE : GName) :
    DistBootWpSL srvLevelK (2 ^ 28 - 1) (bootMember peer client) σm
      (memberShare S client γE id (putgetPub S)) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC putgetGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI := Hctx hG
  haveI : ReceiptBoundLe putgetGF (2 ^ 62) := ⟨by omega⟩
  haveI : ReceiptBoundLe putgetGF (2 ^ 28) := ⟨by omega⟩
  haveI : ThreadBoundLe putgetGF (2 ^ 28) := ⟨by rw [hT]; omega⟩
  haveI := etcdFsSemOk
  iintro Hshare Hls Hgs Htok
  ihave Hown := ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.getIsPkgInit (GF := putgetGF)) $$ Hgs
  ihave Hns := HM.names
  ihave Hdd := HM.dataDir
  imod etcdNetFs_start σm Hm.1 $$ Hls with ⟨#Hos, -, Htree⟩
  imodintro
  -- the member's WAL area, from its machine's files
  iapply (wp_walAreas ⟨putgetGF_allG⟩ etcdFsExts_sat etcdFsExts_satL (extLocal Fs.fsExt σm.world) Hm.1
    [memberDataDir name] (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) Hm.2
    (fun d hd => by
      rw [List.mem_singleton.1 hd]
      exact dirFits_srvWalDirOf_memberDataDir name (by decide))
    inferInstance (bootMember peer client) rfl _) $$ Hos Htree
  iintro Hareas
  icases BigSepL.bigSepL_cons.1 $$ Hareas with ⟨Hwa, -⟩
  -- `putget.initialize' #()`
  unfold bootMember
  wp_apply (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.getIsPkgInit_wf) $$ [Hown Hns]
    as ⟨-, #Hpkg⟩
  · iframe; iexact Hns
  (try wp_auto)
  -- `putget.Member(peer, client)`
  ihave #Hpr := Hprem (2 ^ 28) (by decide) hG
  ihave #Hpub := memberPubOk_putgetPub (G := G') ⟨fl, lc, nh, gs, th, cr⟩ S
  wp_apply (Member.wp_proof (HM.clearProxy hG) zap.NewNop.wp_proof etcdstart.wp_StartServer
      (holdForever.wp_proof time.Sleep.wp_proof) mvcc.api.mvccApi_names_nonempty_law_holds
      S peer client id ctxs boot γE (putgetPub S) Hbf (HM.peerPlain peer hpeer)
      (by unfold srvLevels; rw [hT]; omega) Haf Hbuq Hrf Hdbo inferInstance)
    $$ [Htok Hdd Hwa Hshare]
  · iframe; iframe #
  ipureintro
  rfl

end etcd_putget_dist
end EtcdGrove
end Perennial

end
