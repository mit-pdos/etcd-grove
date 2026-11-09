/-
## `bcrypt.GenerateFromPassword(password, cost)` (assumed)

**Users.** `EtcdServer.UserAdd`, `UserChangePassword` (`v3_server.go:893,918`, batch 2c: the hash the
proposal carries, base64-encoded); `authStore.selectPassword` (`auth/store.go:422`: the pre-3.5
log entries that carry a plain password, out of scope since round 1, `Auth.authReqAt`). Snippet: `examples/specreq/auth/admin.go`
(`ReqUserAddThenCheck`).

**Why true** (`bcrypt/bcrypt.go` at v0.57.0): a password over 72 bytes is refused
(`ErrPasswordTooLong`); a cost below `MinCost` is replaced by `DefaultCost`, one above `MaxCost`
(`31`) refused (`InvalidCostError`); the salt is read with `io.ReadFull(rand.Reader, ...)`, which
never fails (Go 1.24's `crypto/rand`: `Read` "never returns an error"); the result is a fresh slice,
a hash of the password (`EtcdModel.pwHash`). No panic.

**Changes.** New (the old tree had no bcrypt spec: `selectPassword` and `CheckPassword`'s compare
were axioms of the auth store).

Verify round (A9 3d F8): the error over 72 bytes is the package variable `ErrPasswordTooLong` (the
global's value, `errIs`; its shape from `init`): the server returns it to the client
(`EtcdServer.UserAdd`, outcome 2) and owes its shape. The length test comes first
(`bcrypt.go:96`), so it is that error whatever the cost.

**Margin.** The cost error's value (an `InvalidCostError`, `checkCost`) is not stated.
-/
module

public import Spec.golang_org.x.crypto.bcrypt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bcrypt

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A fresh hash of the password; `ErrPasswordTooLong` for a password over 72 bytes; another error
only for a cost over `31`. -/
def GenerateFromPassword.spec : Prop :=
  ∀ (pwsl : GoSlice) (dq : DFrac) (pw : List w8) (cost : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗ pwsl ↦*{dq} pw }}
    (App (App (Val (@! golang_org.x.crypto.bcrypt.GenerateFromPassword)) (Val #pwsl)) (Val #cost))
  {{ (h : GoSlice) (err : GoInterface), RET (PairV #h #err); pwsl ↦*{dq} pw ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ hb : List w8, h ↦* hb ∗ ⌜EtcdModel.pwHash pw hb⌝) ∨
       (⌜72 < pw.length⌝ ∗ errIs golang_org.x.crypto.bcrypt.ErrPasswordTooLong err) ∨
       ⌜err ≠ GoInterface.nil ∧ pw.length ≤ 72 ∧ 31 < sint.Z cost⌝) }}

end spec

end Bcrypt
end EtcdGrove
end Perennial
