/-
**M2, the apply side: the Probe's proofs** (`notes/m2-apply-plan.md`, "The Probe"; 2026-10-31).
Imported by nothing (as the Drafts): the first proofs over the approved drafted statements, to test
that they are provable before the switch.

* **The commit step (G4, item 6)**: a compaction proposal's update over the KV invariant in the
  cluster's mode (`kv_prop_au_cmp`, `reqPropOkD`'s compaction form). Its leading step
  (`cmpReach_reqLb`), at the caller's mask, reads the proposer's KV certificate through the
  certificates' invariant (`kvCertInv`) and turns it into a lower bound of the server's log of
  requested entries (`srvReqLogLb_of_rlogLb`); inside the update the lower bound is a prefix of the
  committed log (`srvReqLogLb_prefix`), where the invariant records the compaction's claim
  (`cmpLogOk`): its revision one of the model's before the entry.
* **The transfer (S3-3, item 8)**: an entry of the committed log gets its compaction claim from the
  KV invariant's (`kv_entry_claim`, at `kv_log_plain`'s hypotheses, which `applyEntryNormal`'s proof
  holds; its pure core `cmpEntryOk_transfer`).
* **G1**: the workload clause over the switch's invariant (`clusterWorkloadOk_ofD`, with
  `batchWaitOk_of_workD`): `clusterWorkloadOk_of`'s proof over `kvInvD` and the drafted shapes.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/- (`cmpEntryOk_transfer` moved to `ApplyCmpArm.lean`.) -/

end pure

section probe
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- (Stage 4c: `cmpReach_reqLb` and `kv_prop_au_cmp` moved to `KVLemmas.lean`.) -/

/- (`kv_entry_claim` moved to `ApplyCmpArm.lean`.) -/

end probe

end EtcdGrove
end Perennial
