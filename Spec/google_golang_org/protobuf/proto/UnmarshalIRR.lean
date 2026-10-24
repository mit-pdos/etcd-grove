/-
`proto.Unmarshal` of an `*etcdserverpb.InternalRaftRequest`: the trust boundary
(`google.golang.org/protobuf` is names-only; the decoding `apply.irrDecode` is opaque,
`apply/InvRequest.lean`). Lean-first (no Rocq counterpart).

In `apply.Apply` (`etcd#22634`), `proto.Unmarshal(e.Data, &raftReq)` either succeeds (`err == nil`,
when `apply.irrDecode bs = some rq`, populating `raftReq` as `apply.internalRaftRequestIs p rq`),
or fails (`err != nil`, when `apply.irrDecode bs = none`, leaving `p` writable so the legacy v2
fallback `*raftReq = legacyReq.toInternalRaftRequest(lg)` can overwrite it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `proto.Unmarshal(d, &raftReq)`: if `bs` decodes as an `InternalRaftRequest`
(`apply.irrDecode bs = some rq`), returns `nil` and makes `p` hold `rq`
(`apply.internalRaftRequestIs p rq`); otherwise (`apply.irrDecode bs = none`), returns a non-nil
error and leaves `p` writable (`∃ x', p ↦ x'`). -/
abbrev proto.UnmarshalIRR.spec : Prop :=
  ∀ (d : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (x : etcdserverpb.InternalRaftRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      d ↦*{dq} bs ∗ p ↦ x }}
    (App (App (Val (@! proto.Unmarshal)) (Val #d))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.InternalRaftRequest.ty) #p)))
  {{ (err : GoInterface), RET #err;
      d ↦*{dq} bs ∗
      match apply.irrDecode bs with
      | some rq => ⌜err = GoInterface.nil⌝ ∗ apply.internalRaftRequestIs p rq
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ ∃ x' : etcdserverpb.InternalRaftRequest, p ↦ x' }}

end spec

end EtcdGrove
end Perennial
