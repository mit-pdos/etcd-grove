/-
## `(*authStore).selectPassword(password, hashedPassword)` (assumed: translated names only)

**Users.** `UserAdd`, `UserChangePassword`.

**Why true.** (`auth/store.go:420-426`, untranslated: `bcrypt`, `encoding/base64`) a non-empty `hashedPassword`: `base64.StdEncoding.DecodeString(hashedPassword)`, the inverse of `b64` (a fresh slice). (A non-empty `password` with an empty `hashedPassword`, a pre-3.5 entry, is rehashed with a fresh salt: out of scope, `authReqAt`.) No panic.

**Changes.** New (the old one was an axiom over the request's shape, `userAddSure`). Round 1 (review F2, S3): the decoded credential is the request's `cred`; the legacy form dropped.

**Margin.** The other inputs are not stated: `authReqAt` rules them out.
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

/-- **`as.selectPassword(p, b64 cred)`**: the credential, decoded. -/
def authStore.selectPassword.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (p : GoString) (cred : Bytes),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ ⌜b64 cred ≠ []⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"selectPassword")) (Val #p)) (Val #(b64 cred)))
  {{ (h : GoSlice) (err : GoInterface), RET (PairV #h #err); ⌜err = GoInterface.nil⌝ ∗ h ↦* cred }}

end spec
end Auth
end EtcdGrove
end Perennial
