/-
`c.SetEndpoints(eps...)` (`client/v3/client.go:195`, PR #21765): acquires `c.epMu.Lock()`, sets
`c.endpoints = eps`, and iterates over `c.channels` calling `ch.resolver.SetEndpoints(eps)`.

We specify and prove both:
1. `Client.SetEndpoints.spec`: when `c.channels` is empty (`∅`, as at `newClient` line 471 before
   `c.channels[defaultChannelKey]` is populated — Finding 1), the loop executes 0 iterations,
   updating `c.endpoints` to `sl` without calling `SetEndpoints` on `c.resolver`.
2. `Client.SetEndpoints_singleton.spec`: when `c.channels` holds a channel `{[k₀ := channel.mk conn r]}`,
   the loop calls `r.SetEndpoints(eps)` and updates both `c.endpoints` and `etcdResolverOwn r eps`.
Lean-first (no Rocq counterpart).
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

/-- `c.SetEndpoints(eps...)` when `c.channels` is empty (`∅`, as in `newClient` before `c.channels`
is populated). -/
abbrev Client.SetEndpoints.spec : Prop :=
  ∀ (c mu mref : Loc) (dq : DFrac) (esl0 : GoSlice) (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientF c go!"epMu" ↦□ mu ∗
      sync.isRWMutexGuard mu (fun _ => iprop(True)) ∗ clientF c go!"endpoints" ↦ esl0 ∗
      clientF c go!"channels" ↦{dq} mref ∗
      mref ↦${dq} (∅ : GMap GoString go_etcd_io.etcd.client.v3.channel) ∗ sl ↦*□ eps }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"SetEndpoints")) (Val #sl))
  {{ RET #(); clientF c go!"endpoints" ↦ sl ∗
      clientF c go!"channels" ↦{dq} mref ∗
      mref ↦${dq} (∅ : GMap GoString go_etcd_io.etcd.client.v3.channel) }}

/-- `c.SetEndpoints(eps...)` when `c.channels` holds `{[k₀ := channel.mk conn r]}`: updates both
`c.endpoints` and `r`'s endpoints (`etcdResolverOwn r eps`). -/
abbrev Client.SetEndpoints_singleton.spec : Prop :=
  ∀ (c mu mref conn r : Loc) (dq : DFrac) (k₀ : GoString) (esl0 : GoSlice) (eps0 : List GoString)
    (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientF c go!"epMu" ↦□ mu ∗
      sync.isRWMutexGuard mu (fun _ => iprop(True)) ∗ clientF c go!"endpoints" ↦ esl0 ∗
      clientF c go!"channels" ↦{dq} mref ∗
      mref ↦${dq} ({[k₀ := go_etcd_io.etcd.client.v3.channel.mk conn r]} :
        GMap GoString go_etcd_io.etcd.client.v3.channel) ∗
      etcdResolverOwn r eps0 ∗ sl ↦*□ eps }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"SetEndpoints")) (Val #sl))
  {{ RET #(); clientF c go!"endpoints" ↦ sl ∗
      clientF c go!"channels" ↦{dq} mref ∗
      mref ↦${dq} ({[k₀ := go_etcd_io.etcd.client.v3.channel.mk conn r]} :
        GMap GoString go_etcd_io.etcd.client.v3.channel) ∗
      etcdResolverOwn r eps }}

end spec

end EtcdGrove
end Perennial
