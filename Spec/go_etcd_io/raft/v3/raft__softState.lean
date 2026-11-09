/-
## `raft.softState()`

**Users.** `NewRawNode` (`rawnode.go:69`: the first `prevSoftSt`), `readyWithoutAccept`,
`HasReady`, `getBasicStatus`. **Proof sketch.** Reads `lead`, `state`. **Changes.** Over the view.
**Margin.** Exact.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- The view's leader and role. -/
def raft.softState.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"softState")) (Val #()))
  {{ (s : go_etcd_io.raft.v3.SoftState), RET #s; raftCore r γ id ρ ∗
      ⌜s = go_etcd_io.raft.v3.SoftState.mk ρ.lead ρ.role⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
