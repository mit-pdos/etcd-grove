/-
`(*raftNode).stop()` (raft.go): stops the loop and waits for `done`.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.stop()`, from any goroutine, with the right to stop the transport (`E.ST`, which it sends on
`stopped` to the loop's `onStop`; D43 M5c): returns once `done` is closed. -/
abbrev raftNode.stop.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      E.ST ∗
      -- (2026-10-30, the repair) the apply side's half of the node's running token, which
      -- `stopped` carries to the loop (`rnStopBag`)
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      -- (2026-10-31) and its half of the WAL's open token, for `onStop`'s `Close`
      rnWalTok r (1 : Qp).half }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

/-- (DRAFT, R2b-1/R2b-2, 2026-11-02; `notes/restart-plan.md`, "R2b: the stop") **`r.stop()` at
the server's stop**: `spec`'s, with the claim on the loop's stop escrow (`rnStopClaim`) and the
apply side's token at the committed log `A` handed to it (`rnApplyTok`, `run`'s once the scheduler
has run every job), giving back what the loop's `onStop` left: the node's id vacant (`node.Stop`'s
`nodeVacant`), its durable state `S` (`raftState`) and the WAL closed with records `σ` holding it
(`StorageHolds`, R2b-1: the loop enters a batch at its WAL `Save`), between the WAL's snapshot
record and its stored commit the log handed to the apply thread (R2b-1: every snapshot record is
of an index the apply thread was handed, and the loop saves a `Ready`'s hard state after handing
its committed entries, with no stop between). -/
abbrev raftNode.stop.specStop : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (A : List EntryModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      E.ST ∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      rnWalTok r (1 : Qp).half ∗ rnStopClaim γ ∗ rnApplyTok γ A }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"stop")) (Val #()))
  {{ RET #(); nodeVacant γ.node.cl γ.id ∗
      ∃ (S : RaftState) (σ : StorContents), raftState γ.node.cl γ.id S ∗ rnWalClosed r σ ∗
        ⌜StorageHolds S σ ∧ σ.b ≤ (γ.pre ++ A).length ∧ (γ.pre ++ A).length ≤ σ.commit⌝ }}

end spec

end EtcdGrove
end Perennial
