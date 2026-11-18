# The conf change codecs of the noax raft (`raft-noax-codec`)

Part of the raft-noax track (`notes/raft-noax.md`: the Go changes; `notes/raft-noax-part.md`: the part
`RaftNoAx/`). Branch `raft-noax-codec` (off `raft-noax`, merged back from it after stage 3a).

## Stage 3b (2026-11-18): the codecs proved, `ccDecodeV2_nil` a theorem

What was left after stage 3a (the clones and `EntrySize`): the four `sorry`s of
`raftpb.{Marshal,Unmarshal}ConfChangeV{1,2}.wp_proof` and the axiom `ccDecodeV2_nil`. All gone: the
part's `raft_kvdurable_porcupine_safe` reaches neither.

**The model is the Go code.** `ccDecodeV1`/`ccDecodeV2` (`CCModel.lean`, the part's own now: opaque
in the main tree) are definitions that follow `UnmarshalConfChangeV1/V2` (`raftpb/noax.go`)
statement by statement, over the pure functions of `RaftNoAx/Proof/go_etcd_io/raft/v3/CCCodec.lean`:

- `ccVarintLoop`/`ccVarintL` (`consumeVarint`: the loop's state `n`, `i`, `v`, `shift`, fuel `10 - n`),
  `ccEnumL` (`consumeEnum`), `ccFieldL` (`consumeField`, and `consumeBytes`, whose copy holds the same
  bytes), each from an index, `none` where Go returns `false`;
- `ccOptField b i tag f`: one `if i < len(data) && data[i] == tag { v, j, ok := f(data, i+1); ... }`
  block (the field's value if its tag is next, and the index after it);
- `ccDecodeSingle` (`unmarshalConfChangeSingle`), `ccChangesLoop` (`UnmarshalConfChangeV2`'s loop over
  the changes, with fuel; `ccDecodeV2` gives it `len + 1`, more than the iterations, each of which
  consumes at least two bytes);
- the encoders `ccVarint` (`appendVarint`: `varintEnc` of `UfWire.lean`), `ccEnumEnc`, `ccBytesEnc`,
  `ccEncOpt` (one `if c.F != nil` block), `ccEncodeV1`, `ccEncodeSingle`, `ccEncChanges`,
  `ccEncodeV2`, over the presence of each field (`Option`).

So the decoders' proofs relate each Go block or loop iteration to one equation of the model, and
`Unmarshal*`'s specs (unchanged: "it computes `ccDecodeV*`") hold by construction.

**The pure theorems** (`CCCodecLemmas.lean`, `CCCodecLen.lean`): the round trips
`ccDecodeV1 (ccEncodeV1 id ty nid ctx) = some ⟨ty.getD 0, nid.getD 0, ctx.getD [], id.getD 0⟩`
(`ccDecodeV1_enc`), `ccDecodeSingle_enc`, `ccDecodeV2_enc` (over `CCSingleEnc`, what
`marshalConfChangeSingle` writes for a change), from `ccVarintLoop_enc` (the varint loop reads back
`varintEnc w` from any iteration, by strong induction on `w`; the bit facts `cc_w64_or_shiftl`,
`cc_w8_and_127`, `cc_w8_or_128`); the decoders' index bounds (`ccVarintL_bound`, ...,
`ccChangesLoop_bound`); the encodings' lengths against `ccLenMax` (`ccEncodeV1_length_le`,
`ccEncodeV2_length_le`), unconditionally (the spec's premise `ccSize + 64 < 2^63` is not needed).
`ccDecodeV2_nil` (`RaftNoAx/Spec/google_golang_org/protobuf/proto/UnmarshalConfChangeV2Empty.lean`,
the part's own now) is a theorem by `simp`.

**The Go proofs** (`RaftNoAx/{Spec,Proof}/go_etcd_io/raft/v3/raftpb/`): new specs and proofs for the
helpers `appendVarint`, `appendEnum`, `appendBytes`, `marshalConfChangeSingle`, `consumeVarint`,
`consumeEnum`, `consumeField`, `consumeBytes`, `unmarshalConfChangeSingle` (each stated as its pure
model: `s ↦* (B ++ ccVarint v)`, `⌜match ccVarintL bs i with ...⌝`, ...), linked in
`etc/link-lean-first-raft-noax.txt` (the Link regenerated). The specs of the four codec functions
are unchanged. Patterns used:

- an `if` block that may `return` is joined with `wp_join (Q := ...)`, `Q` a disjunction of the fall
  through (the block's state) and the return (the error stored, the decoding `none`, the struct's
  field not yet written);
- the decoders split the target struct into its fields at the start (`iStructNamed`, or
  `typedPointsto_split` where a `wp_for` follows: `iStructNamed`'s `"_" ∷ True` breaks `wp_for`'s
  `iNamed`) and put it back on every error path (`ccV1_combine`, `ccV2_combine`); on success the
  hidden fields go to `pbMsg_alloc` (the merged stage 3a `pbMsg`, persistent points-tos);
- `word` only once per fact, before case splits (its cache leaks between sibling branches and the
  kernel then rejects the proof: `notes/perennial-changes.md`; it bit `consumeVarint`).

No spec changed. The tcb collection `etc/tcb-collections/raft-noax.txt` lost `ccDecodeV2_nil` and the
four `sorry`s.
