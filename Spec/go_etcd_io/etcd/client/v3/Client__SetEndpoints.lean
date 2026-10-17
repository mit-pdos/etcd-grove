/-
`c.SetEndpoints(eps...)` (`client/v3/client.go`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvNewClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.SetEndpoints(eps...)`, its mutex and resolver fixed and non-nil, the endpoints read-only: under `c.epMu`
it sets `c.endpoints` (whose points-to the call takes: from here on the field is the mutex's, not
modeled) and the resolver's endpoints. -/
abbrev Client.SetEndpoints.spec : Prop :=
  ∀ (c : Loc) (mu r : Loc) (old eps : GoSlice) (xs : List GoString), mu ≠ null → r ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" c ↦□ mu ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"resolver" c ↦□ r ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"endpoints" c ↦ old ∗ eps ↦*□ xs }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"SetEndpoints")) (Val #eps))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
