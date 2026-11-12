/-
`(*EtcdServer).setAppliedIndex(v)` (`server.go:1714`): an atomic store.

**Users**: `apply` (`server.go:1946, 1954`), with the entry just applied. Snippet `apply.go`
(`ReqAppliedRead`).

**Proof sketch**: the store, with the invariant of `s.appliedIndex` (in `srvNode`: its value `a`
with `srvApplied s γ a`, the writer's half `appliedW s a`): the new value is applied (`srvApplied s γ
v`) and not below the old (so every reader's `srvApplied` stays true). **Changes** from `specs-ref`'s
spec (`appliedOwn`/`appliedAtLeast` over the read names): over `srvApplied`. **Margin**: none.
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

def EtcdServer.setAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (a v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ appliedW s a ∗ srvApplied s γ (uint.nat v) ∗ ⌜uint.nat a ≤ uint.nat v⌝ }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"setAppliedIndex")) (Val #v))
  {{ RET #(); appliedW s v }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
