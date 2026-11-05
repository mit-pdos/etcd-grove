/-
`etcdserverpb.LeaseGrantRequest.GetTTL()` (`api/etcdserverpb/rpc.pb.go`, translated for the server's
`LeaseGrant`: its trace attributes; the lease-grant stage, 2026-11-03). Lean-first (no Rocq counterpart).
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

/-- `p.GetTTL()` on a `*LeaseGrantRequest` returns its `TTL` field, `0` on a nil `p` (the getter's
`x != nil` check). Unlike its siblings it does not take `p ≠ null` (true at every `p`;
written before amendment (H) of the lease-grant plan gave its caller `leaseGrantReqOwn`'s `r ≠ null`). -/
abbrev LeaseGrantRequest.GetTTL.spec : Prop :=
  ∀ (p : Loc) (v : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" p ↦{dq} v }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty @!! go!"GetTTL")) (Val #()))
  {{ RET #(if p = null then W64 0 else v);
      structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" p ↦{dq} v }}

end spec

end EtcdGrove
end Perennial
