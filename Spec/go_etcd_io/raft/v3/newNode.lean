/-
## `newNode(rn)` (internal)

**Users.** `setupNode`, `RestartNode`. **Proof sketch.** Makes the channels (`tickc` buffered).
**Changes.** Mirrors the code.
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

/-- (internal) A node value over `RawNode` `rn`, its channels fresh. -/
def newNode.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id }}
    (App (Val (@! go_etcd_io.raft.v3.newNode)) (Val #rn))
  {{ (nv : go_etcd_io.raft.v3.node), RET #nv; nodeFresh nv rn γ id }}

end spec
end Raft
end EtcdGrove
end Perennial
