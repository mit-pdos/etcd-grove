/-
## `raft.hardState()`

**Users.** `NewRawNode` (`rawnode.go:59`: the first `prevHardSt`), `readyWithoutAccept`, `HasReady`,
`getBasicStatus`. **Proof sketch.** A fresh `HardState` of `Term`, `Vote` and the log's `committed`.
**Changes.** Over the view. **Margin.** Exact; the pointer is fresh.
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

/-- A fresh `HardState` of the view's. -/
def raft.hardState.spec : Prop :=
  ∀ (r : Loc) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftRO r id ρ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"hardState")) (Val #()))
  {{ (p : Loc), RET #p; raftRO r id ρ ∗ hardStatePts p (DFrac.own 1) ρ.hs }}

end spec
end Raft
end EtcdGrove
end Perennial
