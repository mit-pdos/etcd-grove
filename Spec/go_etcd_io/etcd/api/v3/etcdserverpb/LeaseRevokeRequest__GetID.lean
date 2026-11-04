/-
`etcdserverpb.LeaseRevokeRequest.GetID()` (`api/etcdserverpb/rpc.pb.go`, translated for the server's
`LeaseRevoke`: its trace attribute; the lease-expiry plan's X6, 2026-11-04). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `p.GetID()` on a `*LeaseRevokeRequest` returns its `ID` field, `0` on a nil `p` (the getter's
`x != nil` check), as `LeaseGrantRequest.GetTTL`. -/
abbrev LeaseRevokeRequest.GetID.spec : Prop :=
  ∀ (p : Loc) (v : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" p ↦{dq} v }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.LeaseRevokeRequest.ty @!! go!"GetID")) (Val #()))
  {{ RET #(if p = null then W64 0 else v);
      structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" p ↦{dq} v }}

end spec

end EtcdGrove
end Perennial
