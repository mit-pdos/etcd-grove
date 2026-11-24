/-
# kvnet's top level: a replica's program, from its generation's start (2026-11-22)

A linking module (its name: `*Linked`): `kvReplica_wp`, the WP of `kvnetReplicaProgram` (kvnet's package
initialization, then `RunNode`) from the generation's empty package state and `StartNode`'s start
resource at every address map (`kvNodeStart`, from `TopBoot.lean`'s `kvGen_boot`), through kvnet's
linked `wp_RunNode`. (`errors.IsPathErrnoNotExist.spec` is proved since 2026-11-22, `wal-safe-errors`, and
`durable`'s Link uses the proof, so neither theorem takes it.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Link
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PkgTable
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopPkg
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopBoot

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Net go_etcd_io.raft.v3

section replica
attribute [local instance] NetFs.kvnetExts NetFs.kvnetExtsSemantics NetFs.kvnetExtsInterp
  NetFs.kvnetExts_hasNet NetFs.kvnetExts_hasFs

variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS] [KdStor GF]
variable [sem : go.Semantics]
variable [github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [net.Assumptions]
variable [net.FieldAssumptions]
variable [go_etcd_io.raft.v3.Assumptions]
variable [github_com.mit_pdos.gokv.trusted_proph.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
variable [time.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]
variable [NaInvG GF]
variable [_root_.Perennial.internal.filepathlite.Assumptions]
variable [_root_.Perennial.path.filepath.Assumptions]
variable [os.Assumptions]
variable [os.fileStat.FieldAssumptions]
variable [os.file.FieldAssumptions]
variable [syscall.Assumptions]
variable [_root_.Perennial.errors.Assumptions]
variable [_root_.Perennial.log.NewModel]

/-- **A replica's program** (see the file header): from the generation's empty package state and,
if `RunNode`'s check passes (`runNodeOk`; otherwise it returns at once), the replica's address
protocols and the start resource at every address map holding exactly the addresses, given the
globals the package's imports' facts give (`TopPkg.lean`), which `RunNode` reads too. -/
theorem kvReplica_wp
    (γ : KdNames) (vs : List w64) (cl : ClusterConfig) (addrs dir : GoString) (id : w64) :
    ⊢ ownGoState (GF := GF) ∅ -∗
      (⌜runNodeOk (splitAddrs addrs) (uint.nat id) dir (uint.nat cl.voters)
        (uint.nat cl.maxSizePerMsg) (uint.nat cl.maxCommittedSizePerReady) (uint.nat cl.maxInflightMsgs)⌝ -∗
        (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
          addrProto a (kvP (kvFacts γ (fun _ => True)) id) (kvQ (kvFacts γ (fun _ => True)) id)) ∗
        (raft_kvcheck.connGlobals -∗ context.isClosedchanInit -∗ ∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗
          kvNodeStart γ vs dir id dir ⟨cl.voters, cl.preVote, cl.checkQuorum, cl.stepDownOnRemoval,
            cl.maxSizePerMsg, cl.maxCommittedSizePerReady, cl.maxInflightMsgs⟩ M)) -∗
      WP (kvnetReplicaProgram cl addrs dir id) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro Hgs Hres
  unfold kvnetReplicaProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.raft.kvnet.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getIsPkgInit_wf) $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  -- the globals `RunNode` reads, from the package's imports' facts
  ihave ⟨#Hnet, #Hctx⟩ := kvnet_pkg_deps $$ Hpkg
  ihave #Hcg := connGlobals_of_net $$ Hnet
  ihave #Hcc := context.isClosedchanInit_of_init $$ Hctx
  ihave Hcg' := connGlobals_of_net $$ Hnet
  unfold raft_kvcheck.connGlobals
  icases Hcg' with ⟨%eof, %ed, %et, #Heof, #Hed, -⟩
  wp_pures
  wp_apply (kvnetLink.raft_kvnet.wp_RunNode γ vs dir id addrs dir cl.voters cl.preVote
      cl.checkQuorum cl.stepDownOnRemoval cl.maxSizePerMsg cl.maxCommittedSizePerReady
      cl.maxInflightMsgs eof ed) $$ [Hres]
  · iframe Heof Hed Hcc
    iintro %h
    ihave ⟨Hproto, HS⟩ := Hres $$ %h
    iframe Hproto
    iapply HS $$ Hcg Hcc
  ipureintro; rfl

/-- **A replica's generation** (the body of `Net.CrashBootWp` for replica `id`), at the generation's
storage registry (the section's `KdStor`, whose invariant it takes): the boot (`kvGen_boot`), then
the program's WP
(`kvReplica_wp`) and the crash obligation (`kvGen_crash`, with one later credit), which gives the next
generation's `kvGen` at the same file. -/
theorem kvRep_gen
    (γ : KdNames) (vs : List w64) (cl : ClusterConfig) (addrs dir : GoString) (id : w64)
    (f : DurFs.DFile) (R : Fs.Roots)
    (hrun : runNodeOk (splitAddrs addrs) (uint.nat id) dir (uint.nat cl.voters)
      (uint.nat cl.maxSizePerMsg) (uint.nat cl.maxCommittedSizePerReady) (uint.nat cl.maxInflightMsgs))
    (hR : Fs.RootsOk R) (hr : (f.d, f.J) ∈ R) (hd : f.d = dir) (hf : f.Ok)
    (hname : f.name = kdFileName dir id) (hmax : uint.nat id ≤ γ.max)
    (hγ : γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧ Cluster.trace γ.r.cluster = none ∧
      γ.r.cluster.snapLoc = (fun _ => none) ∧ γ.r.cluster.maxData = none ∧ γ.max < 2 ^ 32)
    (hopts : kvOptsOk ⟨cl.voters, cl.preVote, cl.checkQuorum, cl.stepDownOnRemoval,
      cl.maxSizePerMsg, cl.maxCommittedSizePerReady, cl.maxInflightMsgs⟩)
    (hvs : vs = raft_kvreconf.bootVoters (uint.nat cl.voters)) :
    ⊢ kdStorInv (GF := GF) -∗ kdCluster γ vs -∗ readyFits γ.r.cluster kdRaftN -∗
      □ (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
        addrProto a (kvP (kvFacts γ (fun _ => True)) id) (kvQ (kvFacts γ (fun _ => True)) id)) -∗
      □ (∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗ kvPeerAddrs γ id M) -∗
      kvGen γ id f R -∗ ownGoState ∅ ={⊤}=∗
      (WP (kvnetReplicaProgram cl addrs dir id) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} ∗
        ∀ (L' : GooseLocalGS GF) (V' : Fs.Hist), £ 1 -∗
          crashed (hC := hG.goose_localGS.goose_crashGS) -∗ Fs.osInv (L := L') -∗
          Fs.crashRest (fun _ _ => True) (Fs.gooseOsGS (L := hG.goose_localGS))
            (Fs.gooseOsGS (L := L')) [] false V' ={⊤}=∗
          kvGen (hG := ⟨hG.goose_globalGS, L'⟩) γ id f R) := by
  iintro #Hsi #Hcl #Hrf #Hpr #Hpeer Hg Hgs
  imod kvGen_boot γ vs dir id f R hR hr hd hf hname ⟨hrun.2.1, hmax⟩ $$ Hcl Hg
    with ⟨%fl, ⟨%hfl1, %hfl2⟩, Hst, Hk⟩
  imodintro
  isplitl [Hgs Hst]
  · iapply kvReplica_wp γ vs cl addrs dir id $$ Hgs
    iintro %-
    isplitr
    · iexact Hpr
    iintro #Hcg #Hcc %M %hM
    unfold kvNodeStart
    isplitr
    · ipureintro; rfl
    iexists fl, (1 : Qp).half
    iframe Hst
    isplitr
    · unfold kvStartGlobals
      unfold raft_kvcheck.connGlobals
      icases Hcg with ⟨%eof, %ed, %et, -, #Hed, #Het⟩
      iframe Hrf Hsi Hcc
      isplitr
      · ipureintro; exact hγ
      isplitr
      · iexists et; iexact Het
      · iexists ed; iexact Hed
    isplitr
    · iapply Hpeer; ipureintro; exact hM
    ipureintro; exact ⟨hopts, hvs⟩
  · iintro %L' %V' Hlc #Hcr #Hos' Hrest
    -- (the rest of the file's directory, `kvDirRest`, and of the crash's file system are dropped:
    -- kvnet has no other file)
    imod kvGen_crash γ vs id fl L' V' $$ Hcl Hk Hlc Hcr Hrest Hos' with ⟨Hg', -, -⟩
    rw [hfl1, hfl2]
    imodintro
    unfold kvGen
    iexists V'
    iexact Hg'

end replica

end raft_kvnet
end EtcdGrove
end Perennial
