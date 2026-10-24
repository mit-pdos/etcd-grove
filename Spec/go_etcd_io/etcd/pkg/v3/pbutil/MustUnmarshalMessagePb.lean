/-
`pbutil.MustUnmarshalMessage(um, data)` of any message type at the bytes (`PbType`,
`Proof/google_golang_org/protobuf/proto/InvProto.lean`): rafthttp's msgappv2 decoder unmarshals
entries and messages with it. Lean-first. (`MustUnmarshalMessage.lean` is the older per-type
statement, an axiom, for a `ConfChange` and an `InternalRaftRequest`.)
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

/-- **`MustUnmarshalMessage(um, data)`** of an encoding of some `m` into a zero `*T`: the `*T` holds
a message of which the bytes are an encoding (it does not panic). -/
abbrev pbutil.MustUnmarshalMessagePb.spec : Prop :=
  ∀ (T : PbType GF) (l : Loc) (d : GoSlice) (bs : List w8) (dq : DFrac) (m : T.M), T.wire m bs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ d ↦*{dq} bs ∗ T.blank l }}
    (App (App (Val (@! pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l))) (Val #d))
  {{ RET #(); d ↦*{dq} bs ∗ ∃ m' : T.M, T.dec l m' ∗ ⌜T.wire m' bs⌝ }}

end spec

end EtcdGrove
end Perennial
