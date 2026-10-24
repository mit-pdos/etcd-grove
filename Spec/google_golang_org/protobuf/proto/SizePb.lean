/-
`proto.Size` of any message type at the bytes: the trust boundary (`google.golang.org/protobuf` is
names-only), stated over a `PbType` (`InvProto.lean`). Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Size(m)` of a read-only-for-good `*T` holding `m` returns the length of its encoding,
an encoding of `m` if `m` marshals (`proto.MarshalPb.spec`'s result).

Against protobuf-go v1.36.11 (`proto/size.go`): `Size` is the length of the wire encoding `Marshal`
produces (the same, unchanged message); it stores the size cache, a hidden field the instance's `ro`
owns inside an invariant. -/
abbrev proto.SizePb.spec : Prop :=
  ∀ (T : PbType GF) (l : Loc) (m : T.M),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ T.ro l m }}
    (App (Val (@! google_golang_org.protobuf.proto.Size))
      (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l)))
  {{ (n : w64), RET #n;
      ⌜sint.Z n = (pbEnc T.ty l).length ∧ (T.marshals m → T.wire m (pbEnc T.ty l))⌝ }}

end spec

end EtcdGrove
end Perennial
