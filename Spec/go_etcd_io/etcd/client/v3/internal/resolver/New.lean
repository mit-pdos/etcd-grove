/-
`resolver.New(endpoints...)` (`client/v3/internal/resolver`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
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

/-- `resolver.New(eps...)` of read-only endpoints returns some resolver (`*EtcdManualResolver`, which
grpc owns from the dial on; opaque here). -/
abbrev resolver.New.spec : Prop :=
  ∀ (eps : GoSlice) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗ eps ↦*□ xs }}
    (App (Val (@! go_etcd_io.etcd.client.v3.internal.resolver.New)) (Val #eps))
  {{ (r : Loc), RET #r; True }}

end spec

end EtcdGrove
end Perennial
