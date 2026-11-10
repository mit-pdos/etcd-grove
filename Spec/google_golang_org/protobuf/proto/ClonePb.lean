/-
`proto.Clone` of a registered message type at its wire content (per-type models, stage A;
`[v6a]` 2, the third `ufWire` producer): the trust boundary (`google.golang.org/protobuf` is
names-only), over a registered pair (`pbModelOf`, `InvProto.lean`). Next to today's
`proto.ClonePb.spec` (CP3 rewires the users). Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`proto.Clone(m)` of a frozen `*T` of a registered type holding the wire content `c`** returns
a fresh `*T` (as a `proto.Message` of dynamic type `*T`) owned, at a content `c'` of the same wire
content (`eqv` of the models), whose unknown fields are valid, and which is exactly `c` when `c`'s
model marshals (no nested pointers to renew: a `Message`'s responses are deep-copied to fresh
pointers, so only `eqv` holds of a message with responses).

Against protobuf-go v1.36.11 (`proto/merge.go:41`, `Clone`: a new message of the type, merged
into): `internal/impl/merge.go:40-80` copies each present field (a nil proto2 field, `isPointer`, is
skipped, so presence and nil-versus-empty `bytes` are kept: `codec_message.go:136`,
`merge.go:187-189`), and appends the unknown fields verbatim (`proto/merge.go:105-106`), so
`ufWire` is kept at every level. The clone is the post's owned decoded message at `c'`'s model (the
instance's `dec`) when `c'` is one `dec` describes (`decOk`); without `decOk` Go's clone is not
described (true of Go: the caller then owns nothing it can use). `c'`'s facts are pure. Go's stack exhaustion on a deep chain of `Message` responses (a recursion through `Responses`, a fatal error, not a panic) is outside the model, as memory exhaustion is (`notes/txn-nested.md`, the axiom review's note on very deep trees). -/
abbrev proto.ClonePb.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I →
  ∀ (l : Loc) (c : I.data.C),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ I.data.roC l c }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (l' : Loc), RET #(interface.mkOk (go.GoType.PointerType I.data.ty) #l');
      ∃ c' : I.data.C, (⌜I.data.decOk c'⌝ -∗ I.data.dec l' (I.data.modelOf c')) ∗
        ⌜I.data.eqv (I.data.modelOf c) (I.data.modelOf c') ∧ I.data.ufValid c' ∧
          (I.data.marshals (I.data.modelOf c) → c' = c)⌝ }}

end spec

end EtcdGrove
end Perennial
