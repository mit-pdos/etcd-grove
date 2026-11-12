/-
## `RawNode.Bootstrap(peers)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `setupNode`
(`StartNode`).

**Proof sketch.** The storage is empty (`LastIndex` 0: the driver's empty durable state, which the
storage holds); `becomeFollower(1)`; the bootstrap entries appended (unstable) and committed by
fiat -- they are the cluster's (`bootLog`): each entry's bytes are `proto.Marshal`'s output for the
`ConfChange{AddNode, id, ctx}` built (2a's `Marshal.spec` gives `marshalOut` under `noMaps`, which
raftpb's `noMaps_raftpb.spec` gives; raftpb's `bootEntryData_marshal.spec` equates that output with
`bootEntryData id ctx`, `BootLog`'s; verify-round, A5 F4); the empty hard state is `raft_init`'s
`emptyState`; the voters' `AddNode`s applied to the tracker
(`confAt γ |boot|`, `cluster_alloc`); `prevHardSt` reset so the first `Ready` hands out the hard state.

**Changes.** Unchanged in substance; (verify-round) the bytes' source and `emptyState` cited. **Margin.** The errors (no peers, a non-empty storage) are
excluded by the premises; `proto.Marshal` of a `ConfChange` does not fail.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (peers : GoSlice) (dq : DFrac)
    (ps : List (w64 × List w8)) (boot : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv ∗ ⌜ps ≠ [] ∧ BootLog ps boot⌝ ∗ peersPts peers dq ps ∗
      bootLog γ boot ∗ nodeDriver rn γ (Driver.start [] HardState.empty Durable.init) ∗
      nodeConf rn γ ⟨0, Membership.empty⟩ }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Bootstrap")) (Val #peers))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ rawNodeAt rn γ id k adv ∗
      peersPts peers dq ps ∗ nodeDriver rn γ (Driver.start [] HardState.empty Durable.init) ∗
      nodeConf rn γ ⟨boot.length, Membership.simple (listToSet (ps.map (·.1)))⟩ }}

end spec
end Raft
end EtcdGrove
end Perennial
