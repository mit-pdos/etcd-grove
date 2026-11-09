/-
## `node.Advance()`

**Users.** etcd's `raftNode.start` (`raft.go:347`: after the WAL save, the `MemoryStorage` writes,
and the wait for the batch's conf changes to be applied, `notifyc`); the examples' run loops after
applying (`kvdurable/kv.go:511`). Snippet: `readyloop.go` (`ReqReadyLoop`).

**Proof sketch.** Send on `advancec`: the run goroutine calls `RawNode.Advance` (the steps queued at
`acceptReady`: the storage-append and apply responses -- the batch's entries are in the storage now,
`readyStor ... none k []`; the applied index moves to the delivered log, `appliedLb`; a snapshot's
configuration takes effect, `appliedSnap`: its `confAt` from `snapValid`). Or `done`.

**Changes.** The storage's receipt is `readyStor` with nothing left (was `advReceipt`); the snapshot's
batch is the driver's `lastSnap` (was the driver's `handling`); the conf entries not applied by
the view must have been decided skip, as before (`issues/raft-advance-before-applyconfchange.md`).

**Margin.** After a stop nothing moves. (Rounds 1-2) After a snapshot, the client names the view's
point: any committed `a ≥` the snapshot's index whose configuration the snapshot lists (it knows
which from its own record of the snapshot, `snapsMade`; etcd takes its consistent index); the
entries below it are not applied again.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- **Acknowledges the batch entered**: its storage writes done and its conf changes applied (or
decided skip). The node's applied index moves to the delivered log, and a snapshot's configuration
becomes the view's. -/
def node.Advance.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (st : Driver) (k : Nat) (v : ConfView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ nodeDriver n γ st ∗ readyStor n none k [] ∗ nodeConf n γ v ∗
      (match st.lastSnap with
       | none => confSkipped γ st.delivered v.applied st.delivered.length
       | some _ => iprop(True)) }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Advance")) (Val #()))
  {{ RET #(); nodeDriver n γ { st with lastSnap := none } ∗
      ((appliedLb n st.delivered.length ∗
        match st.lastSnap with
        | none => nodeConf n γ v
        | some s => (∀ a m, confAt γ a m -∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is m⌝ -∗
            |={⊤}=> nodeConf n γ ⟨a, m⟩)) ∨
       (nodeStopped n ∗ nodeConf n γ v)) }}

end spec
end Raft
end EtcdGrove
end Perennial
