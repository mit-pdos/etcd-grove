/-
`bcrypt.GenerateFromPassword` (`golang.org/x/crypto/bcrypt`, v0.57.0, the version etcd's
`server/go.mod` requires): the trust boundary of password hashing (the auth plan's D-AU6; E2x,
2026-10-26, for `EtcdServer.UserAdd` and `UserChangePassword`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`bcrypt.GenerateFromPassword(password, cost)`**: returns a fresh byte slice (the hash) and no
error, or one of its two leaf errors; it reads the password and keeps it. Nothing is promised of the
hash's bytes: the auth store's safety does not rest on them (D-AU6), and what the proofs read of the
handler's request is only that its `HashedPassword` is some base64 encoding
(`encoding.base64.stdEnc`). Faithful to the Go code (v0.57.0, under go1.27.3): an error for a
password longer than 72 bytes (`ErrPasswordTooLong`, an `errors.New` error: a pointer to an
`errorString`) or for a cost above `MaxCost` (`InvalidCostError`, an `int`: not a pointer, a safe
map key); either has no `Is` or `Unwrap` method, and its `Error()` returns (`errors.New`'s message,
`fmt.Sprintf`'s). No other error: reading the salt from `crypto/rand.Reader` does not fail (the
default reader, which etcd never replaces, `crypto/internal/rand.reader`, returns `len(b), nil` or
crashes the program), the salt it encodes decodes, and `blowfish.NewSaltedCipher`'s key (the
password and a trailing 0) is not empty. Otherwise `newFromPassword` and `p.Hash()`, which builds
a fresh slice (`expensiveBlowfishSetup` copies the key, `append(key[:len(key):len(key)], 0)`, so
the argument is not written); no panic. (The error facts since 2026-10-27, the auth plan's E3y:
what the gRPC layer needs of the error `UserAdd` hands it, `applyErrIs`.) -/
abbrev bcrypt.GenerateFromPassword.spec : Prop :=
  ∀ (pw : GoSlice) (p : List w8) (dp : DFrac) (cost : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗ pw ↦*{dp} p }}
    (App (App (Val (@! golang_org.x.crypto.bcrypt.GenerateFromPassword)) (Val #pw)) (Val #cost))
  {{ (h : GoSlice) (err : GoInterface), RET (PairV #h #err);
      pw ↦*{dp} p ∗
      ((∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei ∧ _root_.Perennial.errors.isLeafError ei ∧
          methodSet ei.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
          (_root_.Perennial.errors.IsPointerError ei ∨
            ((∀ T, ei.ty ≠ go.GoType.PointerType T) ∧ SafeMapKey (GF := GF) go.error err))⌝ ∗
          {{ True }} (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
            {{ (msg : GoString), RET #msg; True }}) ∨
        ⌜err = GoInterface.nil⌝ ∗ ∃ hs : List w8, h ↦* hs) }}

end spec

end EtcdGrove
end Perennial
