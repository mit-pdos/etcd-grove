/-
`(*EtcdServer).getCommittedIndex()` (`server.go:1710`): an atomic load.

**Users**: `CommittedIndex()`, `ApplyWaitCommit()` (`server.go:629`: leasehttp's wait), the request
path's gap check (`v3_server.go`, 2c), the ready handler. Snippet: none.

**Proof sketch**: the load in the invariant. **Changes**: over `committedLb`. **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The committed index**: the cluster has committed that far. -/
def EtcdServer.getCommittedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvNode s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"getCommittedIndex")) (Val #()))
  {{ (v : w64), RET #v; ∃ l, Raft.committedLb γ.raft l ∗ ⌜uint.nat v ≤ l.length⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
