/-
`redactToken` (`server/auth/store.go`): the trust boundary (names only:
`hex.EncodeToString(sha256.Sum256([]byte(token)))[:12]`; `crypto/sha256` is not translated).
Lean-first (no Rocq counterpart; unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `redactToken(token)`: some string (the hash's first twelve hex digits). -/
abbrev auth.redactToken.spec : Prop :=
  ∀ (token : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.redactToken)) (Val #token))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
