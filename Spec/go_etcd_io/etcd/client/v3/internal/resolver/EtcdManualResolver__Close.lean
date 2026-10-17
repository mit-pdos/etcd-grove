/-
`(*resolver.EtcdManualResolver).Close()` (`client/v3/internal/resolver`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

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

/-- `r.Close()` of a non-nil resolver returns (it closes grpc's manual resolver; the resolver's state is opaque here). -/
abbrev resolver.EtcdManualResolver.Close.spec : Prop :=
  ∀ (r : Loc), r ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty @!! go!"Close"))
      (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
