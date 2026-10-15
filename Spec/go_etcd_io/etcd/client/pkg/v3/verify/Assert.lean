/-
`verify.Assert(condition, msg, v...)`, of etcd's `client/pkg/v3/verify` (translated names-only).
The trust boundary. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

/-- `Assert(condition, msg, v...)`: panics (with the formatted message) unless `condition`;
whatever `ETCD_VERIFY` says. The spec is for a true condition: it returns. -/
abbrev verify.Assert.spec : Prop :=
  ∀ (msg : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify }}
    (App (App (App (Val (@! verify.Assert)) (Val #true)) (Val #msg)) (Val #v))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
