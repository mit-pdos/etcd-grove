/-
`proto.Clone` of any message type: the trust boundary (`google.golang.org/protobuf` is names-only),
stated over a `PbType` (`InvProto.lean`). Lean-first.
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

/-- `proto.Clone(m)` of a read-only-for-good `*T` holding `m` returns a fresh `*T` (as a
`proto.Message` of dynamic type `*T`) holding a message of the same wire content, owned.

Against protobuf-go v1.36.11 (`proto/merge.go`): `Clone` of a non-nil message makes a new message
of its type and merges it in (a deep copy of its fields and unknown fields). -/
abbrev proto.ClonePb.spec : Prop :=
  ∀ (T : PbType GF) (l : Loc) (m : T.M),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ T.ro l m }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType T.ty) #l)))
  {{ (l' : Loc), RET #(interface.mkOk (go.GoType.PointerType T.ty) #l');
      ∃ m' : T.M, T.dec l' m' ∗ ⌜T.eqv m m'⌝ }}

end spec

end EtcdGrove
end Perennial
