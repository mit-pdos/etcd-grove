/-
## `(*tokenSimple).genTokenPrefix()` (assumed: translated names only)

**Users.** `authStore.GenTokenPrefix`, `WithRoot` (the simple provider).

**Why true.** (`simple_token.go`, untranslated: `crypto/rand`, `math/big`) 16 letters drawn by `rand.Int(rand.Reader, 52)`, which never fails (Go 1.24's `crypto/rand`). No panic.

**Changes.** Unchanged.

**Margin.** Nothing about distinctness: two prefixes may collide (`nonissues/etcd-auth-withroot-token-collision-panic.md`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`t.genTokenPrefix()`**: 16 letters. -/
def tokenSimple.genTokenPrefix.spec : Prop :=
  ∀ (t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty @!! go!"genTokenPrefix")) (Val #()))
  {{ (s : GoString) (err : GoInterface), RET (PairV #s #err); ⌜err = GoInterface.nil ∧ s.length = 16⌝ }}

end spec
end Auth
end EtcdGrove
end Perennial
