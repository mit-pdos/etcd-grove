/-
## `(*BackendHooks).SetConfState(cs)` (`hooks.go:55-61`): translated

**Users.** 2d's `applyConfChange` (the configuration after the change, for the next commit).
**Proof sketch.** Under the hooks' lock, `proto.Clone` of `cs` (3h's `proto` boundary) stored as
pending. **Changes**: from `specs-ref`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **Records the configuration** the next commit writes. -/
def BackendHooks.SetConfState.spec : Prop :=
  ∀ (h : Loc) (ci : GoInterface) (p : Loc) (dq : DFrac) (cs : Raft.ConfState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isHooks h ci ∗ Raft.confStatePts p dq cs }}
    (App (Val (h @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty @!! go!"SetConfState")) (Val #p))
  {{ RET #(); Raft.confStatePts p dq cs }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
