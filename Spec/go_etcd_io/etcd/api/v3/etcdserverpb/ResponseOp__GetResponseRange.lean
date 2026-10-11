/-
`etcdserverpb.ResponseOp.GetResponseRange()` (`api/etcdserverpb/rpc.pb.go`, translated for
`concurrency.Mutex`). Lean-first (no Rocq counterpart); see `InvEtcdTxn.lean` (`txnOpRespAt`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `p.GetResponseRange()` of a non-nil `*ResponseOp` whose `Response` oneof holds a
`*ResponseOp_ResponseRange` `w`: `w.ResponseRange` (read-only). -/
abbrev ResponseOp.GetResponseRange.spec : Prop :=
  ∀ (p w rr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.ResponseOp.ty @!! go!"GetResponseRange"))
      (Val #()))
  {{ RET #rr; True }}

end spec

end EtcdGrove
end Perennial
