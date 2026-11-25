/-
# kvraft's checking client's program, safe (2026-11-22)

The stable machine of kvraft's top-level theorem runs `kvcheckProgram cl addrs` (kvcheck's package
initialization, then `Check(addrs, voters)`). `kvcheck_wp_program`: from the empty package state
and, if the addresses are valid (`validAddrs`; otherwise `Check` returns at once), the store's global
pieces (`TopStart.lean`: its invariant, the client's half of its state at the empty map, the checker's
counters at `0`, the replicas' addresses' protocols), the program returns
`#()`: kvcheck's `wp_initialize'` over its program's table (`kvcheck/PkgTable.lean`), the package
facts `Check` reads (`TopPkg.lean`), then kvraft's linked `Check` (`kvraftLink.raft_kvcheck.wp_Check`).

A linking module (it uses a linked result; `etc/tier-linking.txt`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Link
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.PkgTable
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopPkg
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] kdStorageModel

section client
open NetFs in
attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExtsInterp kvraftExts_hasNet kvraftExts_hasFs
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS] [KdStor GF]
variable [sem : go.Semantics]
variable [github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
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
variable [log.NewModel]

/-- **The checking client's program returns** (see the file header). -/
theorem kvcheck_wp_program (γ : KdNames) (cl : ClusterConfig) (addrs : GoString)
    (hrb : receiptBound GF ≤ 2 ^ 63) :
    ⊢ (⌜validAddrs (splitAddrs addrs) (uint.nat cl.voters) = true⌝ -∗
        rkvInv γ ∗ rkvVal γ raft_kvreconf.kvEmpty ∗
        raft_kvcheck.kvCnt γ (splitAddrs addrs).length false (W64 0) ∗
        raft_kvcheck.kvCnt γ (splitAddrs addrs).length true (W64 0) ∗
        raft_kvcheck.addrsProto (kvFacts γ (fun _ => True)) (splitAddrs addrs)) -∗
      ownGoState ∅ -∗
      WP (kvcheckProgram cl addrs) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro Hres Hgs
  unfold kvcheckProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.getIsPkgInit_wf) $$ [Hgs]
    as ⟨-, #Hpkg⟩
  · -- no package is initialized
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave ⟨#Hnet, #Hctx⟩ := kvcheck_pkg_deps $$ Hpkg
  ihave #Hcg := connGlobals_of_net $$ Hnet
  ihave #Hcc := context.isClosedchanInit_of_init $$ Hctx
  wp_pures
  wp_apply (kvraftLink.raft_kvcheck.wp_Check γ addrs cl.voters hrb) $$ [Hres]
  · iframe Hcc Hcg Hres
  ipureintro; rfl

end client

end kvraft
end EtcdGrove
end Perennial
