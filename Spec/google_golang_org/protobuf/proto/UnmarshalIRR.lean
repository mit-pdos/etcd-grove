/-
`proto.Unmarshal` on an `*etcdserverpb.InternalRaftRequest`: the trust boundary
(`google.golang.org/protobuf` is names-only; the decoding `apply.irrDecode` is opaque,
`apply/InvRequest.lean`). Lean-first (PR etcd#21401: `rafthttp.logRaftCommunication` unmarshals
a `MsgProp`'s first entry's `Data` into an `InternalRaftRequest` to log its `Header.ID`).
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

/-- `proto.Unmarshal(b, p)` of bytes `bs` into the `*etcdserverpb.InternalRaftRequest` at `p`
either returns `nil`, in which case `bs` decodes to some `rq` (`apply.irrDecode bs = some rq`)
and `p` holds `rq` (`apply.internalRaftRequestIs p rq`), or returns a non-nil error. -/
abbrev proto.UnmarshalIRR.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (p : Loc) (x : etcdserverpb.InternalRaftRequest) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      b ↦*{dq} bs ∗ p ↦ x }}
    (App (App (Val (@! proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.InternalRaftRequest.ty) #p)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ rq : apply.IRRModel,
        ⌜apply.irrDecode bs = some rq⌝ ∗ apply.internalRaftRequestIs p rq) ∨
       ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
