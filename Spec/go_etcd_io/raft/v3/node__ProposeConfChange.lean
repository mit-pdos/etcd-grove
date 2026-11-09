/-
## `node.ProposeConfChange(ctx, cc)`

**Users.** etcd's `EtcdServer.configure` (`server/etcdserver/server.go:1785`: a v1 `ConfChange`,
`AddNode`, `AddLearnerNode`, `RemoveNode`, `UpdateNode`, promotion as `AddNode`); the examples'
reconfiguration (`kvdurable/reconf.go:90`: v1 and v2 changes, joint transitions explicit and
automatic). Snippet: `confchange.go` (`ReqProposeV1`, `ReqProposeV2Joint`).

**Proof sketch.** `confChangeToMsg` (`MarshalConfChange`: the entry's type and bytes, which decode
back to `c`); `n.Step(ctx, msg)` -- not `stepWait`: the error does not say whether raft accepted it;
the update rides with the `MsgProp` as in `Propose`. A conf change the leader refuses (one pending,
`DisableConfChangeValidation` off: `ConfigOk`) is appended as an empty normal entry, a filler: the
update is not fired by it.

**Changes.** Unchanged in substance (over opaque predicates; v2 changes included).

**Margin.** As `Propose`'s, and the leader's refusal is silent.
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

/-- **Proposes conf change `c`**: the client's update fires when the entry (of `c`'s type, bytes
decoding to `c`) commits. -/
def node.ProposeConfChange.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (cc : GoInterface) (dq : DFrac) (c : ConfChangeI),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ context.isContext ctx cd ∗ confChangePts cc dq c ∗
      (□?γ.dup AU <{ ∃∃ (ops : List LogEntry), committedOps γ ops }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜decodeConfChange c.entryType bs = some c⌝ ∗
            committedOps γ (ops ++ opsOf [⟨t, c.entryType, bs⟩]), COMM True }>) }}
    (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"ProposeConfChange")) (Val #(interface.ok ctx))) (Val #cc))
  {{ (err : GoInterface), RET #err; confChangePts cc dq c ∗ nodeErr n err }}

end spec
end Raft
end EtcdGrove
end Perennial
