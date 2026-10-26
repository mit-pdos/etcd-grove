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
error, or some error; it reads the password and keeps it. Nothing is promised of the hash's
bytes: the auth store's safety does not rest on them (D-AU6), and what the proofs read of the
handler's request is only that its `HashedPassword` is some base64 encoding
(`encoding.base64.stdEnc`). Faithful to the Go code: an error for a password longer than 72
bytes (`ErrPasswordTooLong`), for a cost above `MaxCost` (`InvalidCostError`) or when reading the
salt from `crypto/rand` fails; otherwise `newFromPassword` and `p.Hash()`, which builds a fresh
slice (`expensiveBlowfishSetup` copies the key, `append(key[:len(key):len(key)], 0)`, so the
argument is not written); no panic. -/
abbrev bcrypt.GenerateFromPassword.spec : Prop :=
  ∀ (pw : GoSlice) (p : List w8) (dp : DFrac) (cost : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗ pw ↦*{dp} p }}
    (App (App (Val (@! golang_org.x.crypto.bcrypt.GenerateFromPassword)) (Val #pw)) (Val #cost))
  {{ (h : GoSlice) (err : GoInterface), RET (PairV #h #err);
      pw ↦*{dp} p ∗ (⌜err ≠ GoInterface.nil⌝ ∨ ∃ hs : List w8, h ↦* hs) }}

end spec

end EtcdGrove
end Perennial
