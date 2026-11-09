/-
`(*applierV3backend).newHeader()` (`backend.go:306-314`): a response header: the cluster and member ids, mvcc's current revision, the raft term, the leader.

**Users.** the backend applier's replies.

**Proof sketch.** The membership's `ID()` (2e), `statusOk`'s getters, 3e's `Rev()` at the store (`stAt`).

**Changes** from `specs-ref`'s file of the same name: restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** The ids, term and leader any.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **A fresh header at the store's revision.** -/
def applierV3backend.newHeader.spec : Prop :=
  ∀ (p : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ beAt p mc γ γc R ∗ stAt p σ ∗ threadTok }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; stAt p σ ∗ threadTok ∗ ∃ m : EtcdWire.HeaderM,
      EtcdWire.respHeaderOwn h (DFrac.own 1) m ∗ ⌜uint.nat m.revision = σ.kv.rev⌝ }}

end spec

end Apply
end EtcdGrove
end Perennial
