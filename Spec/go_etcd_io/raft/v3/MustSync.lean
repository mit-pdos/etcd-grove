/-
## `MustSync(st, prevst, entsnum)`

**Users.** The examples' durability decision (`kvdurable/kv.go:465`); `RawNode.readyWithoutAccept`.
Snippet: `readyloop.go` (`ReqDurableLoop`). **Proof sketch.** Getters on possibly-`nil` pointers.
**Changes.** Unchanged.
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

/-- `true` iff there are entries or the term or vote changed. -/
def MustSync.spec : Prop :=

  ∀ (st prevst : Loc) (dq dq' : DFrac) (hs hs' : HardState) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hsPtr st dq hs ∗ hsPtr prevst dq' hs' }}
    (App (App (App (Val (@! go_etcd_io.raft.v3.MustSync)) (Val #st)) (Val #prevst)) (Val #n))
  {{ (b : Bool), RET #b; hsPtr st dq hs ∗ hsPtr prevst dq' hs' ∗
      ⌜b = decide (sint.Z n ≠ 0 ∨ hs.vote ≠ hs'.vote ∨ hs.term ≠ hs'.term)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
