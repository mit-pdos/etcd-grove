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
`errorString`) or for a cost above `MaxCost` (`InvalidCostError(cost)`, an `InvalidCostError`
value: `type InvalidCostError int`, bcrypt.go:50, 301); either has no `Is`, `Unwrap` or `GRPCStatus` method (`GRPCStatus` since k8s etcd3 7c, HS-7, DRAFT:
bcrypt.go:50-52, 87), and its `Error()` returns (`errors.New`'s message,
`fmt.Sprintf`'s). No other error: reading the salt from `crypto/rand.Reader` does not fail (the
default reader, which etcd never replaces, `crypto/internal/rand.reader`, returns `len(b), nil` or
crashes the program), the salt it encodes decodes, and `blowfish.NewSaltedCipher`'s key (the
password and a trailing 0) is not empty. Otherwise `newFromPassword` and `p.Hash()`, which builds
a fresh slice (`expensiveBlowfishSetup` copies the key, `append(key[:len(key):len(key)], 0)`, so
the argument is not written); no panic. **Exactly when** (D3 follow-up (a), 2026-11-28): an error iff
the password is over 72 bytes or `cost > MaxCost` (31; `cost` as Go's signed `int`: one below
`MinCost` means `DefaultCost`, no error), the two checks of `GenerateFromPassword` and `checkCost`
(bcrypt.go:96, 300); witness `notes/axiom-review/pw-gotest/` (`TestBcryptExactError`). (The error facts since 2026-10-27, the auth plan's E3y:
what the gRPC layer needs of the error `UserAdd` hands it, `applyErrIs`.) (fromerror-stable,
2026-11-06) The error's `Error()` returns one string on every call (it returned some string): the
errors `GenerateFromPassword` returns are `ErrPasswordTooLong` (an `errors.New` value, its cell
never written again) and `InvalidCostError` (an `int`: `Error()` formats the value), so a stable
`Error()` is true of bcrypt, and grpc's `status.FromError` takes it as the description.
(premise-fixes-4) Neither has a `Format` method (`*errorString`'s method set is `{Error}`,
`InvalidCostError`'s `{Error}`), so `fmt` prints the error through `Error()`
(`examples/premisefix/fmtarg`, `TestNoFormatter`); (fmt soundness 2, 2026-11-18) each one's `Error` is
`Error() string` (`*errorString.Error`, `InvalidCostError.Error`, bcrypt.go:52, 87).
(prove-authcrypto, 2026-11-21) With an error the hash is `nil`: both error returns are
`return nil, err` (bcrypt.go:96-102); `authStore.selectPassword`'s proof returns it, with its
`b ↦*□ bs`. (ctx-leaf-fix, 2026-11-25) The non-pointer error is an `InvalidCostError` holding an
`int` (Go's typing: the value `InvalidCostError(cost)` of bcrypt's named type, bcrypt.go:301, which
the model, with no typing of interface values, does not give): what the server's `togRPCError` needs
to compare it with `context.DeadlineExceeded` (`errors.IsDeadlineExceeded`'s `deTyped`, through
`applyErrIs`) and to look it up in its error map (`errKeyOk`). Until then the branch said
`(∀ T, ty ≠ *T) ∧ SafeMapKey go.error err ∧ ty ≠ deadlineExceededError`, whose `SafeMapKey` no
non-pointer meets since Perennial's P8c: the axiom was false (a program calling it with cost 32
then panicking had a proof; `notes/bcrypt-invalidcost-false.md`). The new branch implies the old
one's other two conjuncts. -/
abbrev bcrypt.GenerateFromPassword.spec : Prop :=
  ∀ (pw : GoSlice) (p : List w8) (dp : DFrac) (cost : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗ pw ↦*{dp} p }}
    (App (App (Val (@! golang_org.x.crypto.bcrypt.GenerateFromPassword)) (Val #pw)) (Val #cost))
  {{ (h : GoSlice) (err : GoInterface), RET (PairV #h #err);
      pw ↦*{dp} p ∗
      ((∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei ∧ _root_.Perennial.errors.isLeafError ei ∧
          methodSet ei.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
          methodSet ei.ty !! go!"GRPCStatus" = none ∧
          (methodSet ei.ty !! go!"Format" = none ∧
            methodSet ei.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])) ∧
          (_root_.Perennial.errors.IsPointerError ei ∨
            (ei.ty = golang_org.x.crypto.bcrypt.InvalidCostError.ty ∧ ∃ c : w64, ei.v = #c))⌝ ∗
          (∃ m : GoString, □ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
            WP (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #())) {{ Φ }}) ∗ ⌜h = slice.nil⌝ ∗
          ⌜72 < p.length ∨ 31 < sint.Z cost⌝) ∨
        ⌜err = GoInterface.nil⌝ ∗ ⌜p.length ≤ 72 ∧ sint.Z cost ≤ 31⌝ ∗ ∃ hs : List w8, h ↦* hs) }}

end spec

end EtcdGrove
end Perennial
