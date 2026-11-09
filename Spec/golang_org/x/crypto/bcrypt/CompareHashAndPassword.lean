/-
## `bcrypt.CompareHashAndPassword(hashedPassword, password)` (assumed)

**Users.** `authStore.CheckPassword` (`auth/store.go:375`, this batch). Snippet:
`examples/specreq/auth/admin.go` (`ReqUserAddThenCheck`).

**Why true** (`bcrypt/bcrypt.go` at v0.57.0): it parses the hash (`newFromHash`: an error for a
malformed one), hashes `password` under the parsed cost and salt, and compares in constant time;
for a hash `GenerateFromPassword` made of `password` the two agree (bcrypt is deterministic given
the cost and the salt). No panic.

**Changes.** New.

**Margin.** Nothing is said of another password: bcrypt reads only its first 72 bytes, and hashes
collide (the header of `Api.lean`). A `nil` therefore does not mean the password is `pw`.
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

/-- `nil` for the password the hash was made of; anything otherwise. -/
def CompareHashAndPassword.spec : Prop :=
  ∀ (hsl pwsl : GoSlice) (dh dp : DFrac) (hb pw : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗ hsl ↦*{dh} hb ∗ pwsl ↦*{dp} pw }}
    (App (App (Val (@! golang_org.x.crypto.bcrypt.CompareHashAndPassword)) (Val #hsl)) (Val #pwsl))
  {{ (err : GoInterface), RET #err; hsl ↦*{dh} hb ∗ pwsl ↦*{dp} pw ∗
      ⌜hashOf hb pw → err = GoInterface.nil⌝ }}

end spec

end Bcrypt
end EtcdGrove
end Perennial
