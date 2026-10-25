/-
`pbutil.MustMarshalMessage(m)` of any message type at the bytes (`PbType`,
`Proof/google_golang_org/protobuf/proto/InvProto.lean`): rafthttp's message encoder marshals a
`*raftpb.Message` with it. Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`MustMarshalMessage(m)`** of a read-only-for-good `*T` holding `m`, a message that
`marshals`: a fresh slice of its encoding (`proto.Marshal`'s; it never panics). -/
abbrev pbutil.MustMarshalMessage.spec : Prop :=
  ∀ (T : PbType GF) (l : Loc) (m : T.M), T.marshals m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ T.ro l m }}
    (App (Val (@! pbutil.MustMarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l)))
  {{ (d : GoSlice), RET #d;
      d ↦* pbEnc T.ty l ∗ ownSliceCap w8 d (DFrac.own 1) ∗ ⌜T.wire m (pbEnc T.ty l)⌝ }}

end spec

end EtcdGrove
end Perennial
