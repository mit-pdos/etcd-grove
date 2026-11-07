/-
**Per-type prototype: one restated axiom and its one user** (stage A prototype; the Scope's E,
`[v5]` "The `*Pb` specs' premises"): `proto.Marshal` at a registered type (`proto.MarshalPbC.spec`,
the restated trust boundary: the registry premise, the wire content `c` from the caller, `roC l c`,
`marshals`, and `size c < 2^48`, Go's `maxAlloc`), and its one user, `pbutil.MustMarshalMessage`,
proved from it (`pbutil.MustMarshalMessageC.wp_proof`). The encoding's facts come from the generic
`pbEncC_ok` (a theorem), not from the spec: the restated spec says only which bytes `Marshal`
returns.

Prototype only: the restated spec is a definition here, taken as the proof's hypothesis, not an
axiom; the real stage replaces `proto.MarshalPb.spec` and its axiom.
-/
module

public import Proof.google_golang_org.protobuf.proto.PerType
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage
public import Spec.google_golang_org.protobuf.proto.MarshalPb

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

/-- **`proto.Marshal(m)` at a registered type** (the restated trust boundary): of a frozen `*T`
holding the wire content `c`, which marshals and is shorter than `maxAlloc`, a fresh slice of its
encoding `pbEncC T c`, and `nil`. -/
abbrev proto.MarshalPbC.spec : Prop :=
  ∀ (T : PbTypeC GF), pbModelOf GF T.data.ty = some T →
  ∀ (l : Loc) (c : T.data.C), T.data.marshals (T.data.modelOf c) → T.data.size c < 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ T.data.roC l c }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType T.data.ty) #l)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      d ↦* pbEncC T c ∗ ownSliceCap w8 d (DFrac.own 1) }}

/-- **`MustMarshalMessage(m)` at a registered type**: a fresh slice of the encoding, an encoding of
the model of exactly its size. -/
abbrev pbutil.MustMarshalMessageC.spec : Prop :=
  ∀ (T : PbTypeC GF), pbModelOf GF T.data.ty = some T →
  ∀ (l : Loc) (c : T.data.C), T.data.marshals (T.data.modelOf c) → T.data.size c < 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ T.data.roC l c }}
    (App (Val (@! pbutil.MustMarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType T.data.ty) #l)))
  {{ (d : GoSlice), RET #d;
      d ↦* pbEncC T c ∗ ownSliceCap w8 d (DFrac.own 1) ∗
      ⌜T.data.wire (T.data.modelOf c) (pbEncC T c) ∧ (pbEncC T c).length = T.data.size c⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

/-- The one user still proves: the wire facts from `pbEncC_ok`. -/
theorem pbutil.MustMarshalMessageC.wp_proof
    (wp_Marshal : proto.MarshalPbC.spec (GF := GF) (hG := hG)) :
    pbutil.MustMarshalMessageC.spec (GF := GF) (hG := hG) := by
  intro T hreg l c hm hs
  wp_start as #Hro
  ihave %Hok := pbEncC_ok T l c $$ Hro
  wp_auto
  wp_apply wp_Marshal T hreg l c hm hs $$ [$Hro] as %d ⟨Hd, Hcap⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro
  exact Hok hm (by omega)

end proof

end EtcdGrove
end Perennial
