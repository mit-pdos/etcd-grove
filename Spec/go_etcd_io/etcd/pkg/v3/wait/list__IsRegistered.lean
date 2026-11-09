/-
## `(*list).IsRegistered(id)`

**Users.** The apply (`apply/apply.go:40`, `Apply`: `false` skips a `Txn`'s range executions, or a
`Range`/`AuthUserGet`/`AuthRoleGet`/`AuthStatus` entry's result, which `applyEntryNormal` then
triggers, `server.go:2007`), with the entry's id: one this member registered before proposing
(`waitWasReg`, from the server's invariant) or another member's (`waitNever`, the token burnt).
Snippet: `examples/specreq/wait/wait.go` (`ReqIsRegistered`).

**Proof sketch.** `RLock` (a reader slot from the caller's thread token), the map lookup, `RUnlock`.

**Changes.** The reader slot is the thread token's (the bounds plan). Round 1 (completeness F7): the
answer means something: `false` for an id registered once (or never to be) is `waitDone`.

**Margin.** `true` says nothing (a racing `Trigger` may remove it at once).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wait

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- **Whether `id` is registered**, for an id registered once or never to be: `false` means no value
is owed (`waitDone`). -/
def list.IsRegistered.spec : Prop :=
  ∀ (l : Loc) (γw : WaitNames) (P : w64 → GoInterface → IProp GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ listAt l γw P ∗ threadTok ∗
      (waitWasReg γw id ∨ waitNever γw id) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.list'.ty @!! go!"IsRegistered"))
      (Val #id))
  {{ (b : Bool), RET #b; threadTok ∗ (⌜b = false⌝ -∗ waitDone γw id) }}

end spec
end Wait
end EtcdGrove
end Perennial
