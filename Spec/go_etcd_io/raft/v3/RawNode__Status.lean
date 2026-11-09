/-
## `RawNode.Status()`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. `node.run`'s status case. **Proof sketch.** `getStatus(r)` (R2). **Changes.** New (no
old spec; `node.Status`'s needs it).
-/
module

public import Spec.go_etcd_io.raft.v3.Api
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
variable [ctx_sem : context.Assumptions]

/-- `RawNode.Status`: its own memory, the id. -/
def RawNode.Status.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAt rn γ id k adv }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Status")) (Val #()))
  {{ (s : go_etcd_io.raft.v3.Status), RET #s; rawNodeAt rn γ id k adv ∗ statusOwn s ∗
      ⌜s.BasicStatus'.ID' = id⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
