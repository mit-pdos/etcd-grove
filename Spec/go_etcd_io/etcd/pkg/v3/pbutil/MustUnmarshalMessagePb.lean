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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`MustUnmarshalMessage(um, data)`** into a zero `*T` of a registered type, of the encoding of a
wire content `c₀` that marshals with valid unknown fields (`pbEncC T c₀`): it does not panic, and
the `*T` holds, owned, a message at `c₀`'s model (`proto.Unmarshal`'s D2: the decode gives `c₀`
back, and `c₀` is one the type's `dec` describes, `decOk`; stage A of the per-type models: until
then of any bytes that are an encoding of some model of any `PbType`); (raft-entsize §4, 2026-11-10)
at `c₀` itself (the instance's `decC`, from which its `dec` follows: `decC_dec`), which is every
content of valid unknown fields that the bytes encode (D2). -/
abbrev pbutil.MustUnmarshalMessagePb.spec : Prop :=
  ∀ (T : PbTypeC GF), pbModelOf GF T.data.ty = some T →
  ∀ (l : Loc) (d : GoSlice) (bs : List w8) (dq : DFrac) (c₀ : T.data.C),
  T.data.marshals (T.data.modelOf c₀) → T.data.ufValid c₀ → T.data.decOk c₀ → bs = pbEncC T c₀ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ d ↦*{dq} bs ∗
      T.data.blank l }}
    (App (App (Val (@! pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType T.data.ty) #l))) (Val #d))
  {{ RET #(); d ↦*{dq} bs ∗ T.data.decC l c₀ ∗
      ⌜∀ c₁ : T.data.C, T.data.marshals (T.data.modelOf c₁) → T.data.ufValid c₁ →
        bs = pbEncC T c₁ → c₁ = c₀⌝ }}

end spec

end EtcdGrove
end Perennial
