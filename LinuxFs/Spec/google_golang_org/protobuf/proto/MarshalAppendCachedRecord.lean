/-
`proto.MarshalOptions{UseCachedSize: true}.MarshalAppend` of a `walpb.Record` at its wire content
(what the WAL's `encode` calls, `server/storage/wal/encoder.go:78-91`): the trust boundary (protobuf-go
is names-only), at the registered pair of `walpb.Record` (`pbModelOf`, the part's `InvProto.lean`).
Lean-first; **pending the user's review**.
-/
module

public import LinuxFs.Proof.google_golang_org.protobuf.proto.InvProto
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit
public import LinuxFs.Code.go_etcd_io.etcd.server.v3.storage.wal.walpb

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

/-- The options `encode` builds: `proto.MarshalOptions{UseCachedSize: true}`. -/
def cachedSizeOpts [GooseExts] : google_golang_org.protobuf.proto.MarshalOptions :=
  ⟨zero_val _, false, false, true⟩

/-- **`o.MarshalAppend(b, m)`, `o` holding `{UseCachedSize: true}`, of a frozen `*walpb.Record` holding
the wire content `c`** (the registered pair `I` of `walpb.Record`), with the result's length below
`2^47`: appends `c`'s encoding to `b` and returns the result and `nil`. As
`proto.MarshalAppendPb.spec` (the zero options), at this one type, with a weaker in-place clause: a
stale cached size can make `marshal` reallocate though the result fits. **Ownership of `b`'s array**:
either the result reuses it (`b'.ptr = b.ptr`, `b'.cap = b.cap`; the points-to of `b'` covers it), or
the result is a fresh array and `b`'s whole array comes back to the caller, its contents arbitrary
(`∃ ys, b ↦* ys ∗ ownSliceCap w8 b 1`: with a stale size, `marshal` may append into `b`'s capacity
before Go's `append` reallocates; `b`'s first `len b` bytes are in fact unchanged, not claimed).
`encode` needs this to keep its 1 MiB `e.buf` across calls (`encoder.go:89`). Against protobuf-go
v1.36.12: `MarshalAppend` (`proto/encode.go:153-161`) returns `marshal(b, …).Buf`; `marshal`
(`:174-210`) passes `b` itself, or a fresh `make` + `copy` of it when `cap(b) < len(b) + size`
(`:189-192`), to the generated fast path (`internal/impl/encode.go:135-146`,
`marshalAppendPointer`), which only appends (Go's `append`, `protowire.Append*`) and returns the
slice; no []byte argument is stored anywhere. Measured: `examples/stdlib/walpb/marshalappend_test.go`
(`TestMarshalAppendOwnership`: 50,000 random records and buffers, the result is in `b`'s array with
`b`'s capacity or shares nothing with it, and in place whenever it fits with an up-to-date cache;
`TestMarshalAppendStaleCache`: a stale size, `b`'s array written past `len b`, then a fresh result).

Against protobuf-go v1.36.12 (`proto/encode.go:153`, `:174`; `internal/impl/encode.go`,
`sizePointer`): `UseCachedSize` makes the sizer return the size cached in the message's
`sizeCache` (+1, `0` meaning none) instead of recomputing it; `marshal` uses that size only to grow
the output buffer before appending (a wrong one only changes when Go's `append` reallocates), and
nested messages' length prefixes, which a stale cache would make wrong. **That is why the spec is
stated at `walpb.Record` only**: it has no message field (`record.proto`: two varints and `bytes`),
so its bytes do not depend on the cache, whatever value the hidden-field invariant holds there. Not
stated for registered types in general: at a type with message fields a stale cache gives other
bytes. Measured: `examples/stdlib/walpb` (`TestRecordEncoder`: after `proto.Size`, the bytes equal
`recEnc`). -/
abbrev proto.MarshalAppendCachedRecord.spec : Prop :=
  ∀ (I : PbTypeC GF), pbModelOf GF go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty = some I →
  ∀ (o : Loc) (dq : DFrac) (l : Loc) (c : I.data.C) (b : GoSlice) (xs : List w8),
  I.data.marshals (I.data.modelOf c) → xs.length + I.data.size c < 2 ^ 47 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      o ↦{dq} cachedSizeOpts ∗ I.data.roC l c ∗
      b ↦* xs ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (o @!! go.GoType.PointerType google_golang_org.protobuf.proto.MarshalOptions.ty
      @!! go!"MarshalAppend")) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType I.data.ty) #l)))
  {{ (b' : GoSlice), RET (PairV #b' #(GoInterface.nil));
      o ↦{dq} cachedSizeOpts ∗
      b' ↦* (xs ++ pbEncC I c) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
      (⌜b'.ptr = b.ptr ∧ b'.cap = b.cap⌝ ∨
        ∃ ys : List w8, b ↦* ys ∗ ownSliceCap w8 b (DFrac.own 1)) }}

end spec

end EtcdGrove
end Perennial
