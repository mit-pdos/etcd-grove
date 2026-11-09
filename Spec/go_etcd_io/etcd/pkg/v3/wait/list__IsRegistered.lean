/-
## `(*list).IsRegistered(id)`

**Users.** None in the request path; the server's tests. Kept as the old spec's (verified)
function. Mirrors the code: the shard's `RLock`, a lookup.

**Proof sketch.** `RLock` (a reader slot from the caller's thread token), the map lookup, `RUnlock`.

**Changes.** The reader slot is the thread token's (the bounds plan).

**Margin.** The answer is not specified: no caller relies on it (a racing `Trigger` may change it at
once).
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

/-- Whether `id` is registered at the moment of the lookup (unspecified: racy). -/
def list.IsRegistered.spec : Prop :=
  ∀ (l : Loc) (γw : WaitNames) (P : w64 → GoInterface → IProp GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ listAt l γw P ∗ threadTok }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.list'.ty @!! go!"IsRegistered"))
      (Val #id))
  {{ (b : Bool), RET #b; threadTok }}

end spec
end Wait
end EtcdGrove
end Perennial
