/-
The vocabulary of the dist auth workload's orchestrator (`RunAuth`, `examples/etcd/dist/client/auth.go`; F7 stage
S6, `notes/etcd-dist-f7.md`, "Handoff RA-1"). Lean-first (no Rocq counterpart).

`akDistEnv addrs Γ γR`: what the orchestrator hands each principal's machine with its call (`remotePrincipals`,
the principal service's request; persistent): after the set-up froze the cluster's auth history at `hs` (a
committed prefix `Lset`, auth state `setupSt r`), the KV invariant at `Γ.kv`, the history invariant
`etcd_auth.akHistInv Γ.kv` (the client half of `etcdKV Γ.kv`: every write a principal makes keeps it), the frozen
history, `Lset`'s lower bound, and every endpoint's floor above `Lset` (the barriers': `watchFloorsD`). Auth.Work's
dist proof needs exactly these: each write's update under `akHistInv` (`akHist_writeAu`), each refusal at the
frozen state (`authFloorD_frozen`, `watchCheckedD_c_refuted`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthWatchRefusal
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.RootWatch

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd

section pure
variable [GooseExts]

/-- Root's watch `Watch("", WithPrefix(), WithRev(1))`: `WatchOn_dist`'s request premise. -/
theorem watch_all_okD :
    (opWatchModel ([] : GoString) [withPrefixM, withRevM (W64 1)]).isRangeWatchP (W64 1) = true ∧
      ¬ opWatchPanics ([] : GoString) [withPrefixM, withRevM (W64 1)] ∧ 1 ≤ sint.Z (W64 1) ∧
      watchSizeOk (opWatchModel ([] : GoString) [withPrefixM, withRevM (W64 1)]) := by
  refine ⟨?_, etcd_auth.watch_all_ok.2, by decide, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatchP]
  · unfold watchSizeOk
    simp [opWatchModel, op_simps]

/-- u's watch `Watch("a", WithRange("b"), WithRev(1))`: `WatchOn_dist`'s request premise. -/
theorem watch_ab_okD :
    (opWatchModel etcd_auth.lo [withRangeM etcd_auth.hi, withRevM (W64 1)]).isRangeWatchP (W64 1) = true ∧
      ¬ opWatchPanics etcd_auth.lo [withRangeM etcd_auth.hi, withRevM (W64 1)] ∧ 1 ≤ sint.Z (W64 1) ∧
      watchSizeOk (opWatchModel etcd_auth.lo [withRangeM etcd_auth.hi, withRevM (W64 1)]) := by
  refine ⟨?_, etcd_auth.watch_ab_ok.1.2, by decide, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatchP]
  · unfold watchSizeOk
    simp [opWatchModel, op_simps]

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The principals' environment** (see the file header). -/
def akDistEnv [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames) : IProp GF :=
  iprop(∃ (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat),
    kvInvOn γR Γ.kv srvAuthSt0 ∗ etcd_auth.akHistInv Γ.kv ∗ authHistFrozen Γ.kv γz hs ∗
    srvReqLogLb γR Lset ∗ watchFloorsD addrs Γ γR Lset ∗
    ⌜admStates Γ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r⌝)

instance akDistEnv_persistent [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames) :
    Persistent (akDistEnv (GF := GF) addrs Γ γR) := by
  unfold akDistEnv; infer_instance

end defs

end etcd_dist_client
end EtcdGrove
end Perennial
