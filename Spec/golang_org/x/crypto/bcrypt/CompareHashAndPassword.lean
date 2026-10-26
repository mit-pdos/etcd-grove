/-
`bcrypt.CompareHashAndPassword` (`golang.org/x/crypto/bcrypt`, v0.57.0, the version etcd's
`server/go.mod` requires): the trust boundary of password hashing (the auth plan's D-AU6, E2j,
2026-10-26). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`bcrypt.CompareHashAndPassword(hashedPassword, password)`**: returns some error (`nil` when
the password matches the hash), reading both slices and keeping them. Nothing is promised of the
answer: the auth store's safety does not rest on it (a wrong answer lets a client hold a token of
the user it names, which the auth plan treats as that user: D-AU6). Faithful to the Go code: it
parses the hash (`newFromHash`, an error for a hash shorter than `minHashSize` or with a bad
version or cost; the slicing after that is within the checked length), runs `bcrypt` (an error
from `expensiveBlowfishSetup` for a bad salt) and compares in constant time, with no panic and
no write to its arguments. -/
abbrev bcrypt.CompareHashAndPassword.spec : Prop :=
  ∀ (hash pw : GoSlice) (h p : List w8) (dh dp : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt ∗ hash ↦*{dh} h ∗
      pw ↦*{dp} p }}
    (App (App (Val (@! golang_org.x.crypto.bcrypt.CompareHashAndPassword)) (Val #hash)) (Val #pw))
  {{ (err : GoInterface), RET #err; hash ↦*{dh} h ∗ pw ↦*{dp} p }}

end spec

end EtcdGrove
end Perennial
