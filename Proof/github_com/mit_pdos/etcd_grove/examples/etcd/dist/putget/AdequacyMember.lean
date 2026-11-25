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
initialization (`wp_initialize'`, from no package initialized and the registration rights of its packages' metric IDs,
allocated here as the machine's registry ghost state, `PromRegGS`, from `putget_regQsOk`; prom-registry,
2026-11-23); `Member`.

**The named hypotheses** (`MemberBootHyps`; no axiom): each a start resource with no source yet on a machine
of a distributed start, where in one process `goose_adequacy_start` hands it out:
* `dataDir`: the member's data directory fresh (`dataDirFresh`, an axiomatized token), until it is a
  definition over the machine's file tree (the WAL link, `notes/wal-link-scope.md`; blocked on the fs
  redesign, etcd-grove#15).

`ETCD_VERIFY` off (`EtcdVerifyOff`) is the statement's `HEnv`, passed in (`member_boot`'s `HEnv`).
That a valid address's peer URL `http://a` is plain (`host:port`) is proved (`etcd_dist.addrOk_plainPeerURL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Member
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
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
  /-- The member's data directory fresh (until `dataDirFresh` is defined over the machine's files). -/
  dataDir : ⊢@{IProp putgetGF} dataDirFresh (memberDataDir name)

/-- The IDs `putget`'s packages register (their metric names' label-free descriptor IDs and `v3rpc`'s
server metrics' IDs, in `regQs`' order; computed with xxhash64, checked by the kernel in `putget_regQsOk`;
prom-registry, 2026-11-23). -/
def putgetRegKeys : List w64 :=
  [0x12ecdedc778f3f77, 0x6ac118629bed5903, 0x4aa04489ac2b734b, 0x4ab58b8498228b63,
   0x31b044d75943f6dd, 0x5a080044ea5fdf1a, 0x958bb1c4f0e3d61, 0xd537c2a29197bfe6,
   0x38df0bda13eced78, 0xc5eca1b74fabe814, 0x714bc8e301bc1919, 0x7c09ff7fdc8bd9e2,
   0xca706d4e58b535eb, 0x7eaca73262315545, 0xcfa3e07e6efd0dda, 0x94a3ca5582a08ac8,
   0xf4dff1e237623d2, 0x9a0496b0ef986279, 0x6c3eea8e7dbd9701, 0x1c4edd07e42b3902,
   0xa41ef058a0a6b2e, 0x1ac7b57ed76461ba, 0xe6d60bdb6ca2ca2f, 0xe233596477e3f822,
   0xf4109d5f6085f482, 0x8d957e41d1d11d17, 0x1f7b18004d0507ca, 0x9e66b7f695a88383,
   0x606eb6c3266940a1, 0xccb7c98c879ff20c, 0xdca4bc9464724b6, 0xce41c40aa2166e13,
   0xe7cd4a7e1ce001f2, 0x6c80ca5a0a06a60f, 0xc415d620f8a840b3, 0xc174f386755af284,
   0x8e2ca5829b1415ca, 0xf76aa9ea6954a561, 0x79460c68f240b0ab, 0x50db1f551c79b595,
   0x84b7397632eb946f, 0x2b3902ff335816f9, 0x6a15a11de7b828c4, 0x342d1ac3e8fccf46,
   0x8652a92ef6ff21a5, 0x79b607416929bc6b, 0xb617c6d2d636f8d3, 0x8cdefdfd7fbe0f89,
   0x4d5dbff2abdff296, 0x2f589e3e7676603c, 0x7d293418f489e89, 0x1cf0310f1f3cbc4d,
   0xaf13cf18762e0410, 0xab20cb33e635a4d3, 0x4ea7aecf35604fe8, 0xdfccb0d5dbf98fee,
   0x1329a594e50076ed, 0xe21d9196734675f, 0x4f14727af435217b, 0x93f9374046090575,
   0x1f18f72ac56b959b, 0xb99f16de319e8327, 0x6f040a217f98b36f, 0x6e59011109180671,
   0x11c28b1620be2404, 0x7454d00abfa5eebd, 0x3990ae2951922721, 0xc6dbc11e1f9070ed,
   0xee70855f50c035a7, 0xe022592a562465ef, 0xc59e341e500edbf0, 0x4ff1a721c3c867d0,
   0xddb5f8a18722005e, 0x37b32b97f7de5f, 0x9c06bb0ca40cbda8, 0x23dbdcaf102f1686,
   0x1de4f1c3b13fe482, 0xe4ccc50c7daf4c9c, 0x9b8a677c6e6c1ef8, 0x7133d22463246355,
   0xaa607cdd4f5c0a9a, 0xb0bfadd1258d120e, 0xe5bc0e939f7dd45d, 0x35c8acd42298ce6b]

/-- A valid address is within etcd's URL bounds (`etcdstart.addrFits`, `Member.spec`'s premise): `http://`
and it is a plain peer URL (`etcd_dist.addrOk_plainPeerURL`) of at most `7 + 21` bytes
(`etcd_dist.addrOk_length_le`). -/
theorem addrOk_addrFits {a : GoString} (h : Net.addrOk a = true) : etcdstart.addrFits a := by
  refine ⟨etcd_dist.addrOk_plainPeerURL h, ?_⟩
  have := etcd_dist.addrOk_length_le h
  simp only [List.length_append, etcdURLLenMax]
  have : (go!"http://").length = 7 := rfl
  omega

/-- **The registering packages' IDs can have their rights** (prom-registry, route (b)): decided by the
kernel once, over the IDs as literals (`mvccfull_regQsOk`). -/
theorem putget_regQsOk :
    prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.regQs :=
  prometheus.regQsOk_of_keys _ putgetRegKeys (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1600000 in
/-- **The member machine's boot** (see the file header). -/
theorem member_boot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [log.NewModel] [net.FieldAssumptions]
    -- (wal-nostorageok: `NewStorage`'s contract proved, `etcdstart`'s linked results take `os`'s field steps)
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (HM : MemberBootHyps) (HEnv : EtcdVerifyOff)
    (peer client : GoString) (hpeer : Net.addrOk peer = true) (hclient : Net.addrOk client = true)
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
  -- (prom-registry) the machine's registration rights: a fresh ghost map of its packages' IDs, the
  -- machine's registry name
  imod (prometheus.regKeys_alloc (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.regQs putget_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS putgetGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.getIsPkgInit (GF := putgetGF)) $$ Hgs
  ihave Hdd := HM.dataDir
  ihave #Hvoff : ⌜EtcdVerifyOff⌝ $$ []
  · ipureintro; exact HEnv
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
  · iframe
  (try wp_auto)
  -- `putget.Member(peer, client)`
  ihave #Hpr := Hprem (2 ^ 28) (by decide) hG
  ihave #Hpub := memberPubOk_putgetPub (G := G') ⟨fl, lc, nh, gs, th, cr⟩ S
  wp_apply (Member.wp_proof zap.NewNop.wp_proof etcdstart.wp_StartServer
      (holdForever.wp_proof time.Sleep.wp_proof) mvcc.api.mvccApi_names_nonempty_law_holds
      S peer client id ctxs boot γE (putgetPub S) Hbf (etcd_dist.addrOk_plainPeerURL hpeer)
      (addrOk_addrFits hpeer) (addrOk_addrFits hclient)
      (by unfold srvLevels; rw [hT]; omega) Haf Hbuq Hrf Hdbo inferInstance)
    $$ [Htok Hdd Hwa Hshare]
  · iframe; iframe #
  ipureintro
  rfl

end etcd_putget_dist
end EtcdGrove
end Perennial

end
