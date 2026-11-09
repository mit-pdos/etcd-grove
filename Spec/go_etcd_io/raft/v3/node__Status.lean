/-
## `node.Status()`

**Users.** etcd's `EtcdServer.getStatus`/`raftStatus` (`server.go:2471`, the expvar), the examples'
leader transfer (`kvdurable/reconf.go:114`: `Status().Lead`). Snippet: `readyloop.go` (`ReqDisrupt`).

**Proof sketch.** A fresh channel sent on `status`; the run goroutine answers `getStatus(r)` (fresh
copies of the configuration and the progress map: R2's `getStatus` spec, R4's `Config.Clone`). Or
`done`: the zero `Status`.

**Changes.** Unchanged. **Margin.** The leader, term and progress are a snapshot of a moving state;
nothing is said of them.
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

/-- **The node's status**: its own memory; the id is the node's (zero if it stopped). -/
def node.Status.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Status")) (Val #()))
  {{ (s : go_etcd_io.raft.v3.Status), RET #s; statusOwn s ∗
      ⌜s.BasicStatus'.ID' = id ∨ s.BasicStatus'.ID' = W64 0⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
