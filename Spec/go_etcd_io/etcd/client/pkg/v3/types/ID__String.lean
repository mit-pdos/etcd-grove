/-
`types.ID.String`: the trust boundary (`client/pkg/v3/types` is names-only). Lean-first (no Rocq counterpart).
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

/-- `id.String()` (a hexadecimal rendering) returns some string. -/
abbrev types.ID.String.spec : Prop :=
  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types }}
    (App (Val (id @!! go_etcd_io.etcd.client.pkg.v3.types.ID.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
