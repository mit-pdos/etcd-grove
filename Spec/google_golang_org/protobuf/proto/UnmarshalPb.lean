/-
`proto.Unmarshal` into a registered message type at its wire content (per-type models, stage A; the Scope's `[v6]` §3, D1 and D2): the trust boundary (`google.golang.org/protobuf` is
names-only), stated over a registered pair (`pbModelOf`, `InvProto.lean`). Lean-first.
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

/-- **`proto.Unmarshal(b, m)` into a zero `*T` of a registered type** (`I`, under its registration:
the pair is never the caller's). It returns an error, or `nil` and some wire content `c` of the
decoded message, the `*T` owned at `c`'s model when `c` is one the instance's `dec` describes
(`(⌜decOk c⌝ -∗ dec l (modelOf c))`), such that:
- **D1** (what any successful decode is): `b`'s bytes are an encoding of `c`'s model, `c`'s size is
  at most twice the bytes' length, and `c`'s unknown fields are as the decoder leaves them at every
  level (`ufValid`, at the instance's trusted schemas);
- **D2** (the exact round trip): if the bytes are the encoding of a content `c₀` that marshals with
  valid unknown fields, the decode succeeds and gives back exactly `c₀`.
`b` is read, not kept.

Against protobuf-go v1.36.12 (the version `examples/go.mod` selects): `proto/decode.go:61` (`Unmarshal`: reset, then decode; `bytes` fields
copied out of the buffer, `internal/impl/codec_gen.go:5418`), the unknown fields kept verbatim on
the `errUnknown` path (`internal/impl/decode.go:95-101`, `:176-255`). Measured by the harness
whose home is `examples/pbschema` (`c9_d1post_test.go`; raft at `565c2bd`, protobuf-go v1.36.12),
all passing: the whole D1 post (wire, size and `ufValid`, and the decoded heap against `dec`) over
17.7M adversarial inputs of which 1.06M decode, at `Message` (`TestC9D1PostMessage`), and over 17.7M
of which 1.08M decode, at `Entry` (`TestC9D1PostEntry`); the encoders' round trip (P2, D2's
direction: `Unmarshal(Marshal(c))` gives back `c` and `proto.Size` is the instance's `size`) over
300,000 `Entry` and 200,000 `Message` contents (`TestC9P2EntryEncoder`, `TestC9P2MessageEncoder`).
The size bound's ratio 2 is the worst case of packed repeated scalars re-encoded unpacked and of
open proto2 enums' negative values; it holds while no registered type has an unpacked repeated
`int32` or enum field (at any field number), nor any other unpacked repeated scalar numbered 16 or
more (`[v6a]` 6), enforced by `examples/pbschema` (`TestSchemas`, `TestSizeBoundCondition`) through
`etc/pbschema-check.py`. The decoded message is the post's
owned decoded message at `c`'s model (the instance's `dec`) when `c` is one `dec` describes
(`decOk`); without `decOk` Go's decoded message is not described (true of Go: the receiver then owns
nothing it can use). `c`'s facts are pure. -/
abbrev proto.UnmarshalPb.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF I.data.ty = some I →
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ b ↦*{dq} bs ∗
      I.data.blank l }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗
      ⌜(∃ c₀ : I.data.C, I.data.marshals (I.data.modelOf c₀) ∧ I.data.ufValid c₀ ∧
          bs = pbEncC I c₀) → err = GoInterface.nil⌝ ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ c : I.data.C, (⌜I.data.decOk c⌝ -∗ I.data.dec l (I.data.modelOf c)) ∗
        ⌜I.data.wire (I.data.modelOf c) bs ∧ I.data.size c ≤ 2 * bs.length ∧ I.data.ufValid c ∧
          ∀ c₀ : I.data.C, I.data.marshals (I.data.modelOf c₀) → I.data.ufValid c₀ →
            bs = pbEncC I c₀ → c = c₀⌝) }}

end spec

end EtcdGrove
end Perennial
