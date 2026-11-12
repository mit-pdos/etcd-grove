/-
**raft's message at the bytes** (2026-10-22, rafthttp stage 3): the `PbType` of a `*raftpb.Message`
(`pbMessage`), the trusted wire model the codecs' proofs use with the generic protobuf specs
(`Proof/google_golang_org/protobuf/proto/InvProto.lean`). Lean-first.

Read it against `raftpb/raft.proto` (raft v3.7, `syntax = "proto2"`):
- the wire content (`MsgWire`) is the getter view of every field but `responses` (`MessageM`'s
  scalars, the entries' `EntryM`s, the snapshot and the context): what decoding gives back. A
  getter view is what survives the wire: an unset optional field and one set to its zero value
  read alike, and so do a nil sub-message and an empty one (`SnapshotM`'s metadata), so the
  model need not say which was sent; a present `snapshot` stays present (`some`);
- the messages that marshal (`MsgMarshals`): no `responses` (they would be encoded from messages
  `msgOwn` does not own; raft sets them only on its local storage messages). Any enum value
  marshals and decodes back: protobuf-go treats proto2's closed enums as open, so a `MessageType`
  or `EntryType` outside the declared values is kept, not moved to the unknown fields
  (`notes/rafthttp-plan.md`, "Open enums", with the Go test that checks it). (Until 2026-10-22 the
  model required declared values, `MessageType` `0`-`23` and `EntryType` `0`-`2`, as proto2's
  closed enums would);
- a decoded or cloned copy (`eqv`) has the original's wire content, and no responses if the
  original had none (2026-10-23, rafthttp stage 4: an encoding of a message without responses
  carries none, and `proto.Clone` of one makes none), what the receiver's `netRecv` needs;
- decoding (`msgDecode`, opaque) is a function of the bytes: two messages of which the same bytes
  are an encoding agree on the wire (`pbMessage_wire_eq`, `wireEq`). The unknown fields of the
  message, its entries and snapshot are not in the model: an encoding carries them, and decoding
  puts them back in the copy's unknown fields, which the predicates leave existential (`pbMsg`).
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.raft.v3.InvPbMsg

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A message's wire content**: what decoding its encoding gives back. -/
structure MsgWire where
  msg : MessageM
  ents : List EntryM
  snap : Option SnapshotM
  ctx : List w8

instance : Inhabited MsgWire := ⟨⟨zero_val _, [], none, []⟩⟩

/-- The wire content of a message. -/
def wireOf (st : MsgSt) : MsgWire := ⟨st.msg, st.ents, st.snap, st.ctx⟩

/-- **Decoding a `raftpb.Message`'s bytes** (opaque): the wire content, or `none` if they do not
decode. -/
opaque msgDecode (bs : List w8) : Option MsgWire

/-- **The messages that marshal** (see the file header): no `responses`. -/
def MsgMarshals (st : MsgSt) : Prop :=
  st.resps = []

/-- **`bs` is an encoding of the message `st`**: it marshals, and `bs` decodes to its wire
content. -/
def MsgWireOk (st : MsgSt) (bs : List w8) : Prop :=
  MsgMarshals st ∧ msgDecode bs = some (wireOf st)

/-- **A `*raftpb.Message` at the bytes** (a trusted wire model, see the file header): read-only
for good, a frozen message (`msgOwn` at `□`); decoded, an owned message with its `Entries`
capacity (what `netRecv` hands `Process`); blank, a zero struct. -/
def pbMessage : PbType GF where
  ty := raftpb.Message.ty
  M := MsgSt
  ro l st := msgOwn l DFrac.discard st
  ro_persistent l st := msgOwn_persistent l st
  marshals := MsgMarshals
  wire := MsgWireOk
  eqv st st' := wireOf st = wireOf st' ∧ (st.resps = [] → st'.resps = [])
  blank l := iprop(l ↦ (zero_val raftpb.Message))
  dec l st := msgPtsC l (DFrac.own 1) (DFrac.own 1) true st

@[simp] theorem pbMessage_ty : (pbMessage (GF := GF)).ty = raftpb.Message.ty := rfl
@[simp] theorem pbMessage_M : (pbMessage (GF := GF)).M = MsgSt := rfl
@[simp] theorem pbMessage_ro (l : Loc) (st : MsgSt) :
    (pbMessage (GF := GF)).ro l st = msgOwn l DFrac.discard st := rfl
@[simp] theorem pbMessage_marshals : (pbMessage (GF := GF)).marshals = MsgMarshals := rfl
@[simp] theorem pbMessage_wire : (pbMessage (GF := GF)).wire = MsgWireOk := rfl
@[simp] theorem pbMessage_eqv (st st' : MsgSt) :
    (pbMessage (GF := GF)).eqv st st' = (wireOf st = wireOf st' ∧ (st.resps = [] → st'.resps = [])) :=
  rfl
@[simp] theorem pbMessage_blank (l : Loc) :
    (pbMessage (GF := GF)).blank l = iprop(l ↦ (zero_val raftpb.Message)) := rfl
@[simp] theorem pbMessage_dec (l : Loc) (st : MsgSt) :
    (pbMessage (GF := GF)).dec l st = msgPtsC l (DFrac.own 1) (DFrac.own 1) true st := rfl

/-! ### Entries (the msgappv2 codec's short frame marshals them one by one) -/

/-- **Decoding a `raftpb.Entry`'s bytes** (opaque): the entry, or `none`. -/
opaque entDecode (bs : List w8) : Option EntryM

/-- **`bs` is an encoding of the entry `e`**: `bs` decodes to it (every entry marshals, of any
`EntryType` value: the file header). -/
def EntWireOk (e : EntryM) (bs : List w8) : Prop :=
  entDecode bs = some e

/-- **A `*raftpb.Entry` at the bytes** (a trusted wire model, read against `raft.proto`'s `Entry`:
`Term`, `Index`, `Type`, `Data`, all in `EntryM`): read-only for good and decoded alike, a log
entry (`entRO`); blank, a zero struct. -/
def pbEntry : PbType GF where
  ty := raftpb.Entry.ty
  M := EntryM
  ro l e := entRO l e
  ro_persistent l e := entRO_persistent l e
  marshals _ := True
  wire := EntWireOk
  eqv e e' := e = e'
  blank l := iprop(l ↦ (zero_val raftpb.Entry))
  dec l e := entRO l e

@[simp] theorem pbEntry_ty : (pbEntry (GF := GF)).ty = raftpb.Entry.ty := rfl
@[simp] theorem pbEntry_M : (pbEntry (GF := GF)).M = EntryM := rfl
@[simp] theorem pbEntry_ro (l : Loc) (e : EntryM) : (pbEntry (GF := GF)).ro l e = entRO l e := rfl
@[simp] theorem pbEntry_marshals (e : EntryM) :
    (pbEntry (GF := GF)).marshals e = True := rfl
@[simp] theorem pbEntry_wire : (pbEntry (GF := GF)).wire = EntWireOk := rfl
@[simp] theorem pbEntry_blank (l : Loc) :
    (pbEntry (GF := GF)).blank l = iprop(l ↦ (zero_val raftpb.Entry)) := rfl
@[simp] theorem pbEntry_dec (l : Loc) (e : EntryM) : (pbEntry (GF := GF)).dec l e = entRO l e := rfl

/-- One encoding is of one entry. -/
theorem EntWireOk.inj {e e' : EntryM} {bs : List w8} (h : EntWireOk e bs) (h' : EntWireOk e' bs) :
    e = e' :=
  Option.some.inj (h.symm.trans h')

/-- **Two messages of which the same bytes are an encoding agree on the wire.** -/
theorem pbMessage_wire_eq {st st' : MsgSt} {bs : List w8} (h : MsgWireOk st bs)
    (h' : MsgWireOk st' bs) : wireEq st st' := by
  have e : wireOf st = wireOf st' := Option.some.inj (h.2.symm.trans h'.2)
  simp only [wireOf, MsgWire.mk.injEq] at e
  exact ⟨e.1.symm, e.2.1.symm, e.2.2.1.symm, e.2.2.2.symm⟩

end defs

end EtcdGrove
end Perennial
