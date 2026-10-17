/-
`(*types.ID).String`, the method of `*ID` Go lifts from `ID.String`: the trust boundary
(`client/pkg/v3/types` is names-only, so goose generates no method set for `*ID`; etcd-io/etcd#19693's
pr-verify, 2026-10-17, for `bootstrapWALFromBackend`'s log line). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

/-- `l.String()` on `l : *ID`: `(*l).String()`, some string; `*l` is read. -/
abbrev types.ID.String_ptr.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (id : go_etcd_io.etcd.client.pkg.v3.types.ID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ l ↦{dq} id }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.ID.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} id }}

end spec

end EtcdGrove
end Perennial
