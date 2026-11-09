/-
## `redactToken(token)` (assumed: translated names only)

**Users.** `Authenticate`, `AuthInfoFromCtx`, `assignSimpleTokenToUser` (logging).

**Why true.** (`auth/store.go:1249`, untranslated: `crypto/sha256`) the first 12 hex digits of the token's SHA-256 (64 digits): no panic.

**Changes.** Unchanged.

**Margin.** None.
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

/-- **`redactToken(tok)`**: some string. -/
def redactToken.spec : Prop :=
  ∀ (tok : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.redactToken)) (Val #tok))
  {{ (s : GoString), RET #s; True }}

end spec
end Auth
end EtcdGrove
end Perennial
