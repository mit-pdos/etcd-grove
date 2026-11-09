/-
## `RawNode.Bootstrap(peers)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. `setupNode` (`StartNode`).

**Proof sketch.** The storage is empty (`LastIndex` 0: the driver's empty durable state, which the
storage holds); `becomeFollower(1)`; the bootstrap entries appended (unstable) and committed by
fiat -- they are the cluster's (`bootLog`); the voters' `AddNode`s applied to the tracker
(`confAt γ |boot|`, `cluster_alloc`); `prevHardSt` reset so the first `Ready` hands out the hard state.

**Changes.** Unchanged in substance. **Margin.** The errors (no peers, a non-empty storage) are
excluded by the premises; `proto.Marshal` of a `ConfChange` does not fail.
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

/-- **Bootstraps a fresh `RawNode`** with the cluster's bootstrap log: its view moves past it. -/
def RawNode.Bootstrap.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (peers : GoSlice) (dq : DFrac)
    (ps : List (w64 × List w8)) (boot : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id ∗ ⌜ps ≠ [] ∧ BootLog ps boot⌝ ∗ peersPts peers dq ps ∗
      bootLog γ boot ∗ nodeDriver rn γ (Driver.start [] HardState.empty Durable.init) ∗
      nodeConf rn γ ⟨0, Membership.empty⟩ }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Bootstrap")) (Val #peers))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ rawNode rn γ id ∗
      peersPts peers dq ps ∗ nodeDriver rn γ (Driver.start [] HardState.empty Durable.init) ∗
      nodeConf rn γ ⟨boot.length, Membership.simple (listToSet (ps.map (·.1)))⟩ }}

end spec
end Raft
end EtcdGrove
end Perennial
