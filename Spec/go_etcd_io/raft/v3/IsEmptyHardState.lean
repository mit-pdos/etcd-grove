/-
## `IsEmptyHardState(st)`

**Users.** etcd's `raftNode.start` (`raft.go:222`, `267`), the examples (`kvdurable/kv.go:464`),
`RawNode.acceptReady`. Snippet: `readyloop.go`. **Proof sketch.** `nil`, or `isHardStateEqual` with
the empty state. **Changes.** Unchanged.
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

/-- `true` iff the hard state is empty (or `nil`). -/
def IsEmptyHardState.spec : Prop :=

  ∀ (st : Loc) (dq : DFrac) (hs : HardState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hsPtr st dq hs }}
    (App (Val (@! go_etcd_io.raft.v3.IsEmptyHardState)) (Val #st))
  {{ (b : Bool), RET #b; hsPtr st dq hs ∗ ⌜b = decide (hs = HardState.empty)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
