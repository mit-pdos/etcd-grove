/-
# kvnet's top level: a replica's program, from its generation's start (2026-11-22)

A linking module (its name: `*Linked`): `kvReplica_wp`, the WP of `kvnetReplicaProgram` (kvnet's package
initialization, then `RunNode`) from the generation's empty package state and `StartNode`'s start
resource at every address map (`kvNodeStart`, from `TopBoot.lean`'s `kvGen_boot`), through kvnet's
linked `wp_RunNode` (over `errors.IsPathErrnoNotExist.spec`, Perennial PR #677, a hypothesis).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Link
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PkgTable
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopPkg

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
variable [_root_.Perennial.log.NewModel]

/-- **A replica's program** (see the file header): from the generation's empty package state, the
replica's address protocols and the start resource at every address map holding exactly the
addresses, given the globals the package's imports' facts give (`TopPkg.lean`), which `RunNode`
reads too. -/
theorem kvReplica_wp
    (h_err : _root_.Perennial.EtcdGrove.errors.IsPathErrnoNotExist.spec (GF := GF) (hG := hG))
    (γ : KdNames) (vs : List w64) (cl : ClusterConfig) (addrs dir : GoString) (id : w64)
    (hvc : validCluster (splitAddrs addrs) (uint.nat cl.voters) (uint.nat cl.maxSizePerMsg)
      (uint.nat cl.maxCommittedSizePerReady) (uint.nat cl.maxInflightMsgs) = true)
    (hid1 : 1 ≤ uint.nat id) (hid2 : uint.nat id ≤ (splitAddrs addrs).length) :
    ⊢ ownGoState (GF := GF) ∅ -∗
      (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
        addrProto a (kvP (kvFacts γ (fun _ => True)) id) (kvQ (kvFacts γ (fun _ => True)) id)) -∗
      (raft_kvcheck.connGlobals -∗ context.isClosedchanInit -∗ ∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗
        kvNodeStart γ vs dir id dir ⟨cl.voters, cl.preVote, cl.checkQuorum, cl.stepDownOnRemoval,
          cl.maxSizePerMsg, cl.maxCommittedSizePerReady, cl.maxInflightMsgs⟩ M) -∗
      WP (kvnetReplicaProgram cl addrs dir id) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro Hgs Hproto HS
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
  ispecialize HS $$ Hcg Hcc
  unfold raft_kvcheck.connGlobals
  icases Hcg with ⟨%eof, %ed, %et, #Heof, #Hed, -⟩
  wp_pures
  wp_apply (kvnetLink.raft_kvnet.wp_RunNode γ vs dir h_err id addrs dir cl.voters cl.preVote
      cl.checkQuorum cl.stepDownOnRemoval cl.maxSizePerMsg cl.maxCommittedSizePerReady
      cl.maxInflightMsgs eof ed hvc hid1 hid2) $$ [Hproto HS]
  · iframe Hproto HS Heof Hed Hcc
  ipureintro; rfl

end replica

end raft_kvnet
end EtcdGrove
end Perennial
