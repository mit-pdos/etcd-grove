/-
## `isHardStateEqual(a, b)` (internal)

`IsEmptyHardState`, `readyWithoutAccept`, `HasReady`. Mirrors the code.
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

/-- (internal) Equality of hard states (`nil` the empty one). -/
def isHardStateEqual.spec : Prop :=

  ∀ (a b : Loc) (ha hb : HardState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hsPtr a ha ∗ hsPtr b hb }}
    (App (App (Val (@! go_etcd_io.raft.v3.isHardStateEqual)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; ⌜r = decide (ha = hb)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
