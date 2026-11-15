/-
# `golang.org/x/crypto/bcrypt`: the trust boundary (batch 3d)

bcrypt (`golang.org/x/crypto` v0.57.0 at the pin) is translated names only (`Code/golang_org/x/
crypto/bcrypt.toml`): its two functions etcd calls are **assumed**, each file says why they are
true of the library's code at the pin.

Stated over W0's two opaque relations (`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`, which calls them
3d's boundary): `EtcdModel.pwHash pw h` (**`h` is a bcrypt hash of `pw`**: `$2a$<cost>$`, a salt and
the hash of `pw` under it; what `GenerateFromPassword` returns) and `EtcdModel.pwMatch h pw` (**`pw`
passes the check against `h`**: exactly when `CompareHashAndPassword(h, pw)` is `nil`).

The one fact etcd relies on is bcrypt's **correctness**, W0's law `pwHash_match` (a hash matches
its own password). Nothing is assumed about a password that is not `pw`: bcrypt reads at most
the first 72 bytes of a password (a longer password passes when bcrypt's key, `pw` with a NUL appended, cut at 72 bytes, is the same:
`nonissues/etcd-auth-password-72-byte-prefix.md`), and a hash function has collisions; "a wrong
password fails" would be a false universal (PRINCIPLES, "An assumption states the physical fact the
code relies on").

The package's error variables (`init`, verify round, A9 3d F8): `ErrPasswordTooLong`,
`ErrMismatchedHashAndPassword`, `ErrHashTooShort`, each `errors.New` of its message
(`errors.newVar`), distinct, given existentially (a fresh pointer: the sentinel encoding). The
server returns `GenerateFromPassword`'s `ErrPasswordTooLong` to its client as an unmapped error
(`EtcdServer.UserAdd`), whose shape (a leaf `*errors.errorString` with its message) it has from
here.
-/
module

public import GeneratedProof.golang_org.x.crypto.bcrypt
public import SpecPlan.Spec.PkgInit.golang_org.x.crypto.bcrypt
public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.State
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bcrypt

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`v` is the value of bcrypt's package variable `g`** (persistent: Go never writes it after
initialization). -/
def errIs (g : GoString) (v : GoInterface) : IProp GF := iprop(globalAddr g ↦□ v)

open golang_org.x.crypto.bcrypt in
/-- **bcrypt's error variables** (`bcrypt.go:29,33,87` at v0.57.0, `errors.New` at init; assumed, as
the package is translated names only): each holds a fixed `*errors.errorString` of its message,
the three distinct. -/
def init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ⊢
    ∃ e1 e2 e3 : GoInterface,
      errIs ErrPasswordTooLong e1 ∗ errIs ErrMismatchedHashAndPassword e2 ∗
      errIs ErrHashTooShort e3 ∗
      errors.newVar ErrPasswordTooLong go!"bcrypt: password length exceeds 72 bytes" ∗
      errors.newVar ErrMismatchedHashAndPassword
        go!"crypto/bcrypt: hashedPassword is not the hash of the given password" ∗
      errors.newVar ErrHashTooShort
        go!"crypto/bcrypt: hashedSecret too short to be a bcrypted password" ∗
      ⌜[e1, e2, e3].Nodup⌝

end init

end Bcrypt
end EtcdGrove
end Perennial
