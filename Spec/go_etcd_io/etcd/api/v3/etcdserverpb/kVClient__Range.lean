/-
`(*kVClient).Range` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated gRPC stub; names-only): the
trust boundary of the wire (the vertical slice's unit V1). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Wire.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Wire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`c.Range(ctx, in, opts...)`** on the stub `c` (`&kVClient{cc}`, `NewKVClient(cc)`), whose
connection `cc` leads to the KV service `p` of the server `s` (`connectedTo`): the server's
end-to-end theorem for `Range` transported to the client (`range_end_to_end`: the txn package's range at a certified log of at least two revisions, after the read index (committed index `0`: what a fresh handler knew) unless serializable (`rangeAnsOk`), the header filled; or a non-nil error (the check's, or the server's through `togRPCError`)). The response is the client's fresh
copy (the same formulas of its fields), every server-side resource removed; any call options.
`Wire.lean` has the transport's account and its premises (the server's per-call pool, the
transport's integrity, protobuf round-trips). -/
abbrev kVClient.Range.spec : Prop :=
  ∀ (c : Loc) (cc : GoInterface) (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid n : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (inp : Loc)
    (o : OpFull) (opts : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      structFieldRef etcdserverpb.kVClient go!"cc" c ↦□ cc ∗
      v3rpc.connectedTo cc p s E ρ γr cid mid n ∗ context.isContext ctx cd ∗
      txn.rangeRequestIs inp o }}
    (App (App (App (Val (c @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      v3rpc.rangeOutC E γr cid mid o resp err }}

end spec

end EtcdGrove
end Perennial
