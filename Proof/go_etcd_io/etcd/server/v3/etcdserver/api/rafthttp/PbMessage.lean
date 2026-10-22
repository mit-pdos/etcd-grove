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
  `msgOwn` does not own; raft sets them only on its local storage messages), and every enum a
  value of its closed proto2 enum (`MessageType` `0`-`23`, `EntryType` `0`-`2`): a decoder puts any
  other value in the unknown fields, and the getter reads the default;
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- **The messages that marshal** (see the file header): no `responses`, every enum known. -/
def MsgMarshals (st : MsgSt) : Prop :=
  st.resps = [] ∧ uint.Z st.msg.Type' ≤ 23 ∧ ∀ e ∈ st.ents, uint.Z e.Type' ≤ 2

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
  blank l := iprop(l ↦ (zero_val raftpb.Message))
  dec l st := msgPtsC l (DFrac.own 1) (DFrac.own 1) true st

@[simp] theorem pbMessage_ty : (pbMessage (GF := GF)).ty = raftpb.Message.ty := rfl
@[simp] theorem pbMessage_M : (pbMessage (GF := GF)).M = MsgSt := rfl
@[simp] theorem pbMessage_ro (l : Loc) (st : MsgSt) :
    (pbMessage (GF := GF)).ro l st = msgOwn l DFrac.discard st := rfl
@[simp] theorem pbMessage_marshals : (pbMessage (GF := GF)).marshals = MsgMarshals := rfl
@[simp] theorem pbMessage_wire : (pbMessage (GF := GF)).wire = MsgWireOk := rfl
@[simp] theorem pbMessage_blank (l : Loc) :
    (pbMessage (GF := GF)).blank l = iprop(l ↦ (zero_val raftpb.Message)) := rfl
@[simp] theorem pbMessage_dec (l : Loc) (st : MsgSt) :
    (pbMessage (GF := GF)).dec l st = msgPtsC l (DFrac.own 1) (DFrac.own 1) true st := rfl

/-- **Two messages of which the same bytes are an encoding agree on the wire.** -/
theorem pbMessage_wire_eq {st st' : MsgSt} {bs : List w8} (h : MsgWireOk st bs)
    (h' : MsgWireOk st' bs) : wireEq st st' := by
  have e : wireOf st = wireOf st' := Option.some.inj (h.2.symm.trans h'.2)
  simp only [wireOf, MsgWire.mk.injEq] at e
  exact ⟨e.1.symm, e.2.1.symm, e.2.2.1.symm, e.2.2.2.symm⟩

end defs

end EtcdGrove
end Perennial
