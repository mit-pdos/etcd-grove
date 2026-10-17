/-
`c.SetEndpoints(eps...)` (`client/v3/client.go`; item 5, client construction: `newClient` sets the
configured endpoints). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.SetEndpoints(eps...)` (the endpoints `eps`, read-only) on a client whose `epMu` guards
nothing of the proof's (`isRWMutexGuard` of `True`) and whose resolver is not dialed yet: the
client's `endpoints` and the resolver's are `eps`. -/
abbrev Client.SetEndpoints.spec : Prop :=
  ∀ (c mu r : Loc) (esl0 : GoSlice) (eps0 : List GoString) (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientF c go!"epMu" ↦□ mu ∗
      sync.isRWMutexGuard mu (fun _ => iprop(True)) ∗ clientF c go!"endpoints" ↦ esl0 ∗
      clientF c go!"resolver" ↦□ r ∗ etcdResolverOwn r eps0 ∗ sl ↦*□ eps }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"SetEndpoints")) (Val #sl))
  {{ RET #(); clientF c go!"endpoints" ↦ sl ∗ etcdResolverOwn r eps }}

end spec

end EtcdGrove
end Perennial
