/-
`proto.Unmarshal` on an `mvccpb.KeyValue`: the trust boundary (`google.golang.org/protobuf` is
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

/-- `proto.Unmarshal(b, kv)` of the encoding of the model's key-value `kv` into the
`*mvccpb.KeyValue` at `p` (whatever it held) sets its key, revisions, version, value and lease
(the key and value as fresh read-only slices; the message's internal fields as it likes) and
returns `nil`. -/
abbrev proto.Unmarshal.spec : Prop :=
  ∀ (b : GoSlice) (kv : EtcdKv) (p : Loc) (x : mvccpb.KeyValue) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      b ↦*{dq} mvcc.kvEncode kv ∗ p ↦ x }}
    (App (App (Val (@! proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType mvccpb.KeyValue.ty) #p)))
  {{ RET #(GoInterface.nil); b ↦*{dq} mvcc.kvEncode kv ∗
      ∃ (ks vs : GoSlice) (st : internal.impl.MessageState) (uf : GoSlice) (sc : w32),
        p ↦ ({
          state' := st, Key' := ks, CreateRevision' := kv.createRev, ModRevision' := kv.modRev,
          Version' := kv.version, Value' := vs, Lease' := kv.lease, unknownFields' := uf,
          sizeCache' := sc } : mvccpb.KeyValue) ∗
        ks ↦*□ kv.key ∗ vs ↦*□ kv.value }}

end spec

end EtcdGrove
end Perennial
