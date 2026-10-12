/-
`v3rpc.kvServer.Range` (`key.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`kvServer.Range(ctx, r)`** of the range `o`: `checkRangeRequest`'s error, or the server's `Range` answer with the
header filled (`kvOut`). -/
abbrev v3rpc.kvServer.Range.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.kvServerIs p s A cid mid n ∗ A.call ctx ∗ txn.rangeRequestIs r o }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.kvServer.ty @!! go!"Range")) (Val #ctx))
      (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      match v3rpc.rangeCheck o with
      | some e => v3rpc.checkOut e resp err ∗ A.call ctx
      | none => v3rpc.kvOut A cid mid (.range o)
          (structFieldRef etcdserverpb.RangeResponse go!"Header" resp) resp err }}

end spec

end EtcdGrove
end Perennial
