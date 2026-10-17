/-
`tokenJWT.keyFunc` (`server/v3/auth/jwt.go`; in the fork, `info`'s key function moved out of `info`
into a method, names only: its type switch names the crypto key types, which are not translated).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvJWT

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `t.keyFunc(token)` of a JWT provider (its `signMethod` and `key` read-only, `jwtProviderRO`),
on a token `jwt.Parse` owns, returns a key and an error. (It compares `token.Method.Alg()` with
`t.signMethod.Alg()`, both set: `Parse` fails before calling it on an unknown algorithm, and the
constructor sets `signMethod`; then a type switch on `t.key`.) -/
abbrev auth.tokenJWT.keyFunc.spec : Prop :=
  ∀ (t : Loc) (vo : Bool) (tok : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ jwtProviderRO t vo }}
    (App (Val (t @!! go.GoType.PointerType tokenJWT.ty @!! go!"keyFunc")) (Val #tok))
  {{ (k e : GoInterface), RET (PairV #k #e); True }}

end spec

end EtcdGrove
end Perennial
