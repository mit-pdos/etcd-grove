/-
## `IsResponseMsg(t)`

**Users.** `node.run`, `RawNode.Step`. **Proof sketch.** `isMsgInArray` over a package array: `int(msgt)` indexes it,
so a negative type panics (round 2: the premise; received messages have one by `msgSent_type`).
**Changes.** The premise `0 ≤ t` (was missing).
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

/-- `isResponseMsgType`. -/
def IsResponseMsg.spec : Prop :=

  ∀ (t : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ⌜0 ≤ sint.Z t⌝ }}
    (App (Val (@! go_etcd_io.raft.v3.IsResponseMsg)) (Val #t))
  {{ (b : Bool), RET #b; ⌜b = isResponseMsgType t⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
