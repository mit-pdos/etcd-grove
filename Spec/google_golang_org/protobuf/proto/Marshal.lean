/-
`proto.Marshal` of an `mvccpb.KeyValue`: the trust boundary (`google.golang.org/protobuf` is
names-only; the encoding `kvEncode` is opaque, `Model.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Model
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Marshal(kv)` of the `*mvccpb.KeyValue` at `p` holding the model's key-value `kv`
(its key and value slices read at any fraction) returns a fresh slice of the encoding of
`kv` and `nil`; the message keeps its fields (its size cache as it likes). -/
abbrev proto.Marshal.spec : Prop :=
  ∀ (p : Loc) (x : mvccpb.KeyValue) (kv : EtcdKv) (dqk dqv : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      p ↦ x ∗ x.Key' ↦*{dqk} kv.key ∗ x.Value' ↦*{dqv} kv.value ∗
      ⌜x.CreateRevision' = kv.createRev ∧ x.ModRevision' = kv.modRev ∧
        x.Version' = kv.version ∧ x.Lease' = kv.lease⌝ }}
    (App (Val (@! proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType mvccpb.KeyValue.ty) #p)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      (∃ sc : w32, p ↦ ({ x with sizeCache' := sc } : mvccpb.KeyValue)) ∗
      x.Key' ↦*{dqk} kv.key ∗ x.Value' ↦*{dqv} kv.value ∗
      d ↦* mvcc.kvEncode kv ∗ ownSliceCap w8 d (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
