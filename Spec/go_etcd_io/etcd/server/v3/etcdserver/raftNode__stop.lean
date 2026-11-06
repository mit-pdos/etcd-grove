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

/-- (R2b-1/R2b-2, 2026-11-02; `notes/restart-plan.md`, "R2b: the stop") **`r.stop()` at
the server's stop** (R2c review F2, 2026-11-06: the one spec; until then `specStop`, beside a
`spec` without the claim and the image, which only the `run.spec` R2c-4 removed used): from any
goroutine, with the right to stop the transport (`E.ST`, which it sends on `stopped` to the loop's
`onStop`; D43 M5c), the apply side's half of the node's running token (`rnStopBag`) and its share of
the WAL with its token (`rnWalTokA`, for `onStop`'s `Close`), with the claim on the loop's stop escrow (`rnStopClaim`) and the
apply side's token at the committed log `A` handed to it (`rnApplyTok`, `run`'s once the scheduler
has run every job), giving back what the loop's `onStop` left: the node's id vacant (`node.Stop`'s
`nodeVacant`), its durable state `S` (`raftState`) and the WAL closed with records `σ` holding it
(`StorageHolds`, R2b-1: the loop's `Save` moves the records to the entered state; the stop is at an
idle loop, where they hold the node's durable state), between the WAL's snapshot
record and its stored commit the log handed to the apply thread (R2b-1: every snapshot record is
of an index the apply thread was handed, and the loop saves a `Ready`'s hard state after handing
its committed entries, with no stop between).

(2026-11-03, R2b-3b: proved, `wp_proofStop`.) The loop's `done` announces the escrow
(`rnDoneEsc`), which `onStop` fills; the server enters a batch after its WAL `Save` (R2b-3a), so
the records hold the durable state at every stop exit; `applyc` is synchronous, so the log the
loop handed is the apply side's `A` (review M2). The image's order is at the backend's consistent
index, which equals `|pre ++ A|` once every job ran and the backend's last commit saved the index:
R2b-3c's. -/
abbrev raftNode.stop.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (A : List EntryModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      E.ST ∗
      (letI := srvStor (GF := GF) γ.node; nodeRunning γ.nl γ.node.cl srvClusterN (1 : Qp).half) ∗
      rnWalTokA γ r (1 : Qp).half ∗ rnStopClaim γ ∗ rnApplyTok γ A }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"stop")) (Val #()))
  {{ RET #(); nodeVacant γ.node.cl γ.id ∗
      ∃ (S : RaftState) (σ : StorContents), raftState γ.node.cl γ.id S ∗ rnWalClosed γ r σ ∗
        ⌜StorageHolds S σ ∧ σ.b ≤ (γ.pre ++ A).length ∧ (γ.pre ++ A).length ≤ σ.commit⌝ }}

end spec

end EtcdGrove
end Perennial
