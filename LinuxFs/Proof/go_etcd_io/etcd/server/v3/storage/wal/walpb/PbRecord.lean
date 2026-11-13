/-
**`walpb.Record` as a registered protobuf message type at its wire content** (the per-type pattern
of raft's `PbEntryType.lean`, for the WAL: W6 of `notes/wal-fsext-plan.md`, §2.3 "Record bytes").

- The wire content is `WalEnc.RecC` (`Proof/go_etcd_io/etcd/server/v3/storage/WalPbWire.lean`):
  `Type`, `Crc` nil or set (zero included), `Data` nil or not, the unknown fields. Its model is the
  decoder's view `WalEnc.WalRec` (`RecC.model`).
- `recHidden l uf`: the hidden fields (`state`, `sizeCache`, `unknownFields`) in an invariant, as
  raft's `pbMsg`, with the unknown fields as protobuf-go's decoder leaves them at `record.proto`'s
  schema (`ufWire recSchema uf`). (raft's `pbMsg` is not reachable from the part: it lives over the
  main raft root package, whose names the part's raft root declares too.)
- `recPtsCC l dq c`: a `*walpb.Record` at `l` holding exactly `c`, its fields at `dq` (cells and
  bytes persistent); `recRoC l c` its frozen form (`dq = □`), what `Size`/`Marshal` read; the
  decoded object (`decC`) is the owned form.
- **The encoder is a transparent Lean function** (`WalEnc.recEnc`, the wire format), and the
  decoder `recDecode` opaque: what `proto.Unmarshal` makes of the bytes.
- **The decoded object is owned whole** (`recOwnC l c`, the instance's `decC`; 2026-11-13, W3a):
  every field, the hidden ones (`state`, `sizeCache`, `unknownFields`) included, at `1`, and `Data`'s
  bytes owned. Unlike raft's types, whose decoded objects put the hidden fields in an invariant
  (`pbMsg`): the WAL's decoder reuses one `*walpb.Record` (`rec.Reset()`, then `proto.Unmarshal`
  into it, decoder.go:82/:125), and `Reset` writes the whole struct (`*x = Record{}`), which an
  invariant holding the hidden fields (at fixed unknown fields) would not survive. Faithful: the
  decoded message is fresh (`Data` copied out of the input), and protobuf-go keeps no reference to
  it after `Unmarshal` returns. A frozen record (`recRoC`, what `Marshal` reads) keeps the invariant.

**Trusted, pending the user's review** (two axioms, as for every registered type):
- `recEncC_ok`: protobuf-go decodes `recEnc c` back to `c`'s model when `c`'s unknown fields are
  valid at the schema. With `recEnc`'s definition this is the claim that `recEnc` is protobuf-go's
  encoding. Measured: `examples/stdlib/walpb` (`TestRecordEncoder`: 200,000 random contents,
  `proto.Marshal`, `MarshalOptions{UseCachedSize: true}.MarshalAppend` and `proto.Size` against
  `recEnc`/`recSize`, and `proto.Unmarshal(recEnc c)` giving back exactly `c`; `TestRecordSchema`:
  the descriptor against `recSchema`; protobuf-go v1.36.12, go1.27.3).
- `pbRecordC_reg`: the registration, of the exact shape `pbModelOf GF walpb.Record.ty = some …`.
`etc/pbschema-check.py` does not see this registration (it walks `Proof/` and `Spec/` only, and
its schema table is the main tree's `pbSchemaOf`): `TestRecordSchema` is its descriptor check.
-/
module

public import LinuxFs.Proof.google_golang_org.protobuf.proto.InvProto
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal.walpb
public import Proof.go_etcd_io.etcd.server.v3.storage.WalPbWire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.wal WalEnc

/-- **Decoding a `walpb.Record`'s bytes** (opaque: `proto.Unmarshal`): the decoder's view, or
`none`. -/
opaque recDecode (bs : List w8) : Option WalRec

/-- **The trust boundary: `walpb.Record`'s encoding** (pending the user's review; see the file
header). -/
axiom recEncC_ok (c : RecC) : ufWire recSchema c.uf → recSize c < 2 ^ 63 →
    recDecode (recEnc c) = some c.model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The hidden fields of a `*walpb.Record`** (see the file header). -/
def recHidden (l : Loc) (uf : List w8) : IProp GF :=
  iprop(inv (nroot.@"protobuf") iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[walpb.Record, go!"state"] ↦ st ∗ l.[walpb.Record, go!"sizeCache"] ↦ sc ∗
      l.[walpb.Record, go!"unknownFields"] ↦ us ∗ us ↦* uf) ∗ ⌜ufWire recSchema uf⌝)

instance recHidden_persistent (l : Loc) (uf : List w8) : Persistent (recHidden (GF := GF) l uf) := by
  unfold recHidden; infer_instance

/-- A proto2 optional scalar's cell, frozen: `nil`, or set (possibly to zero). -/
def recCell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) : Option V → IProp GF
  | none => iprop(⌜p = null⌝)
  | some v => iprop(p ↦□ v)

/-- A `bytes` field, frozen: `nil`, or a non-nil slice holding the bytes. -/
def recBytes (ds : GoSlice) : Option (List w8) → IProp GF
  | none => iprop(⌜ds = slice.nil⌝)
  | some bs => iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦*□ bs)

instance recCell_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (o : Option V) : Persistent (recCell (GF := GF) p o) := by
  cases o <;> unfold recCell <;> infer_instance

instance recBytes_persistent (ds : GoSlice) (o : Option (List w8)) :
    Persistent (recBytes (GF := GF) ds o) := by
  cases o <;> unfold recBytes <;> infer_instance

/-- **A `*walpb.Record` at `l` holding exactly `c`**, its fields at `dq`. -/
def recPtsCC (l : Loc) (dq : DFrac) (c : RecC) : IProp GF :=
  iprop(∃ (pt pc : Loc) (ds : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[walpb.Record, go!"Type"] ↦{dq} pt ∗ recCell pt c.typ ∗
    l.[walpb.Record, go!"Crc"] ↦{dq} pc ∗ recCell pc c.crc ∗
    l.[walpb.Record, go!"Data"] ↦{dq} ds ∗ recBytes ds c.data ∗
    recHidden l c.uf)

/-- A `bytes` field, owned: `nil`, or a non-nil slice holding the bytes. -/
def recBytesOwn (ds : GoSlice) : Option (List w8) → IProp GF
  | none => iprop(⌜ds = slice.nil⌝)
  | some bs => iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦* bs)

/-- **A decoded `*walpb.Record` at `l` holding exactly `c`, owned whole** (see the file header). -/
def recOwnC (l : Loc) (c : RecC) : IProp GF :=
  iprop(∃ v : walpb.Record,
    l ↦ v ∗ recCell v.Type' c.typ ∗ recCell v.Crc' c.crc ∗ recBytesOwn v.Data' c.data ∗
    v.unknownFields' ↦* c.uf ∗ ⌜ufWire recSchema c.uf⌝)

/-- **A frozen `*walpb.Record` holding exactly `c`**. -/
abbrev recRoC (l : Loc) (c : RecC) : IProp GF := recPtsCC l DFrac.discard c

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance recRoC_persistent (l : Loc) (c : RecC) : Persistent (recRoC (GF := GF) l c) := by
  unfold recRoC recPtsCC; infer_instance

/-- The frozen record's unknown fields are valid at the schema. -/
theorem recRoC_uf (l : Loc) (c : RecC) : recRoC (GF := GF) l c ⊢ ⌜ufWire recSchema c.uf⌝ := by
  unfold recRoC recPtsCC recHidden
  iintro ⟨%pt, %pc, %ds, -, -, -, -, -, -, -, -, %Hu⟩
  ipureintro; exact Hu

/-- **The store of a record** (`Store.lean`): each scalar `nil` if zero, `Data` `nil` if empty. -/
def recTree (r : WalRec) : VTree :=
  .strct walpb.Record.ty
    [(go!"Type", go.GoType.PointerType go.int64), (go!"Crc", go.GoType.PointerType go.uint32),
     (go!"Data", go.GoType.SliceType go.byte)]
    [cellTree go.int64 r.typ, cellTree go.uint32 r.crc, bytesTree go.byte r.data]

/-- **`walpb.Record` at its wire content: the data** (no axiom). -/
def pbRecordM : PbModelC GF where
  ty := walpb.Record.ty
  M := WalRec
  ro l r := iprop(∃ c, recRoC l c ∗ ⌜c.model = r⌝)
  ro_persistent _ _ := inferInstance
  marshals _ := True
  wire r bs := recDecode bs = some r
  eqv r r' := r = r'
  blank l := iprop(l ↦ (zero_val walpb.Record))
  dec l r := iprop(∃ c, recOwnC l c ∗ ⌜c.model = r⌝)
  C := RecC
  roC := recRoC
  roC_persistent _ _ := inferInstance
  modelOf := RecC.model
  levels c := [(recSchema, c.uf)]
  size := recSize
  tree := recTree
  decOk _ := True
  ro_iff _ _ := .rfl
  roC_ufValid l c := by
    iintro #H
    ihave %Hu := recRoC_uf l c $$ H
    ipureintro
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact Hu
  decC l c := recOwnC l c
  decC_dec l c _ := by
    iintro H
    iexists c
    iframe H
    ipureintro; rfl

/-- **`walpb.Record` at its wire content** (the registered instance): the data and the encoder
`recEnc`, whose `enc_ok` is `recEncC_ok` with `recEnc_length`. -/
def pbRecordC : PbTypeC GF where
  data := pbRecordM
  encd := { enc := recEnc
            enc_ok := fun c _ hu hs =>
              ⟨recEncC_ok c (hu _ (List.mem_singleton.2 rfl)) hs, recEnc_length c⟩ }

@[simp] theorem pbEncC_pbRecordC (c : RecC) : pbEncC (pbRecordC (GF := GF)) c = recEnc c := rfl
@[simp] theorem pbRecordC_ty : (pbRecordC (GF := GF)).data.ty = walpb.Record.ty := rfl
@[simp] theorem pbRecordC_roC : (pbRecordC (GF := GF)).data.roC = recRoC := rfl
@[simp] theorem pbRecordC_C : (pbRecordC (GF := GF)).data.C = RecC := rfl
@[simp] theorem pbRecordC_modelOf : (pbRecordC (GF := GF)).data.modelOf = RecC.model := rfl
@[simp] theorem pbRecordC_size : (pbRecordC (GF := GF)).data.size = recSize := rfl
@[simp] theorem pbRecordC_marshals (r : WalRec) : (pbRecordC (GF := GF)).data.marshals r = True :=
  rfl
@[simp] theorem pbRecordC_decC (l : Loc) (c : RecC) :
    (pbRecordC (GF := GF)).data.decC l c = recOwnC l c := rfl
@[simp] theorem pbRecordC_blank (l : Loc) :
    (pbRecordC (GF := GF)).data.blank l = iprop(l ↦ (zero_val walpb.Record)) := rfl
theorem pbRecordC_ufValid (c : RecC) :
    (pbRecordC (GF := GF)).data.ufValid c ↔ ufWire recSchema c.uf := by
  simp [PbModelC.ufValid, pbRecordC, pbRecordM]
theorem pbRecordC_wire (r : WalRec) (bs : List w8) :
    (pbRecordC (GF := GF)).data.wire r bs ↔ recDecode bs = some r := Iff.rfl

end defs

/-- **The registration** of `pbRecordC` (exact shape; pending the user's review). -/
axiom pbRecordC_reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] :
    pbModelOf GF walpb.Record.ty = some (pbRecordC (GF := GF))

end EtcdGrove
end Perennial
