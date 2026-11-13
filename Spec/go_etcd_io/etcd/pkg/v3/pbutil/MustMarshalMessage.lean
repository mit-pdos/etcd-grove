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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`MustMarshalMessage(m)` of a frozen `*T` of a registered type holding the wire content `c`**,
which marshals, of size below `2^48` (`proto.Marshal`'s allocation, Go's `maxAlloc`): a fresh slice
of its encoding (`pbEncC T c`, `proto.Marshal`'s; it never panics), an encoding of `c`'s model of
exactly `c`'s size (stage A of the per-type models: until then over any `PbType`, at the address's
encoding `pbEnc`). -/
abbrev pbutil.MustMarshalMessage.spec : Prop :=
  ∀ (T : PbTypeC GF), pbModelOf GF T.data.ty = some T →
  ∀ (l : Loc) (c : T.data.C), T.data.marshals (T.data.modelOf c) → T.data.size c < 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ T.data.roC l c }}
    (App (Val (@! pbutil.MustMarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType T.data.ty) #l)))
  {{ (d : GoSlice), RET #d;
      d ↦* pbEncC T c ∗ ownSliceCap w8 d (DFrac.own 1) ∗
      ⌜T.data.wire (T.data.modelOf c) (pbEncC T c) ∧ (pbEncC T c).length = T.data.size c⌝ }}

end spec

end EtcdGrove
end Perennial
