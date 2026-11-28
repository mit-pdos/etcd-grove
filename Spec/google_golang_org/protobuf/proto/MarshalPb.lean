/-
`proto.Marshal` of a registered message type at its wire content (per-type models, stage A; the
stage A prototype's `pbutil/PerTypeMarshal.lean`, made the trust boundary in CP2): over a registered
pair (`pbModelOf`, `InvProto.lean`). Next to today's `proto.MarshalPb.spec` (CP3 rewires the
users). Lean-first.
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

/-- **`proto.Marshal(m)` of a frozen `*T` of a registered type holding the wire content `c`**, which
marshals and whose size is below `2^48` (Go's `maxAlloc`): a fresh slice of its encoding
`pbEncC I c`, and `nil`. What the encoding is comes from the generic `pbEncC_ok` (a theorem from
the instance's encoder axiom), not from this spec.

Against protobuf-go v1.36.12 (`proto/encode.go:105`, `:174`): `Marshal` sizes, allocates and
appends the encoding (`internal/impl/encode.go`); it fails only on a missing required field,
invalid UTF-8 in a proto3 string or a message changed while it is encoded, which `marshals` and
the frozen `roC` exclude; an allocation above `maxAlloc` panics, which the size premise excludes.
The result is not `nil`: an empty encoding is `emptyBytesForMessage(m)` (`proto/encode.go:119-146`),
the non-nil `emptyBuf[:]` for a valid message. A nil `*T` is an invalid message, for which `Marshal`
returns `nil` (so `d ↦* pbEncC I c` would be false for a non-empty encoding): the pre takes
`⌜l ≠ null⌝`, so the spec claims nothing of a nil `*T` and no instance's `roC` has to exclude it.
Evidence: Go test `examples/pbschema/marshalnonnil_test.go` (every registered type, empty and populated,
non-nil result; the nil `*T` gives `nil`, at v1.36.12); ledger `notes/specs-only/ledger.md` 2026-11-28.
Review (`axiom` skill, `notes/axiom-review/marshalpb-nonnil.md`): **survives** for the five registered
types (no Go program marshals a non-nil `*T` meeting the premises into a nil slice, an error, other
bytes or shared mutable memory); it suggested the `⌜l ≠ null⌝` premise. Approved, with that hardening,
by coordinator-E on Upamanyu's delegation (#50, 2026-11-28). -/
abbrev proto.MarshalPb.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I →
  ∀ (l : Loc) (c : I.data.C), I.data.marshals (I.data.modelOf c) → I.data.size c < 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ I.data.roC l c ∗
      ⌜l ≠ null⌝ }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      d ↦* pbEncC I c ∗ ownSliceCap w8 d (DFrac.own 1) ∗ ⌜d ≠ slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial
