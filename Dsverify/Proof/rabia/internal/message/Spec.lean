/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Spec.lean`, run
`rabia-r1wake-1`: its specs over `bufio`, onto the revised shared bufio (dsv-bufio,
`Proof/bufio/Own.lean`; its predicates are never unfolded here). The other specs are
`SpecPure.lean`'s.)

`rabia/internal/message`'s framing specs:
* `BufWrite`: the frame (`frame`: the 4-byte little-endian length, the data) through a
  `*bufio.Writer` (`bufio.ownBufWriter bw wi J Q Ew sz sent pend err`, the lab's `ownWriter`);
  `WriteFlush`, `Command.MarshalWriteFlush`, `Msg.MarshalWriteFlush`: then `Flush`. The
  underlying writer's contract `io.writerOk wi J Q Ew` (persistent) is a premise, as the lab's
  `writerOk wr J Q` was: its `Q` is prefix-closed (`io.writerOk_prefixClosed`), which the frame's
  header's write needs.
* `BufRead`: the next frame from a `*bufio.Reader` (`bufio.ownBufReader br ri connPre S E R`, the
  lab's `ownReader`, over a reader whose only condition on a read is a non-empty buffer, a
  connection's, `net.conn_readerOk`); `Command.ReadUnmarshal`, `Msg.ReadUnmarshal`: and its
  decoding, over a connection's end (`S = recvTokL cn s P`), when the protocol says the frame's
  payload is an encoding (`frameIs P cn R D`, the lab's over the reader's stream predicate `I`;
  here over the protocol, since the stream state inside the reader is reached only through
  `bufio.ownBufReader_fact`, `net.connReader_proto`, one step later).
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Proof.bufio.Own
public import Proof.io.WriterOk
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net

/-- The condition of a connection's reads (`net.conn_readerOk`): a non-empty buffer. -/
abbrev connPre : List w8 → Nat → Prop := fun _ m => 0 < m

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The next frame's payload after `R`, if the peer's stream (`P cn`'s, up to extension) holds
it whole, satisfies `D` (persistent). -/
def frameIs (P : Proto GF) (cn : Nat) (R : List w8) (D : List w8 → Prop) : IProp GF :=
  iprop(□ ∀ (bs : List w8), ⌜bs.length < 2 ^ 32⌝ -∗ protoPrefix P cn (R ++ frame bs) -∗ ⌜D bs⌝)

instance frameIs_persistent (P : Proto GF) (cn : Nat) (R : List w8) (D : List w8 → Prop) :
    Persistent (frameIs P cn R D) := by
  unfold frameIs; infer_instance

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]

/-- `BufWrite(writer, data)`: writes `data`'s frame (or a prefix of it, with an error). -/
abbrev BufWrite.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sz : Nat) (sent pend : List w8) (err : GoInterface) (sl : GoSlice) (dq : DFrac)
    (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ ⌜bs.length < 2 ^ 32⌝ ∗
      EtcdGrove.io.writerOk wi J Q Ew ∗ EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      □ Q (sent ++ pend ++ frame bs) ∗ sl ↦*{dq} bs }}
    (App (App (Val (@! BufWrite)) (Val #bw)) (Val #sl))
  {{ (e : GoInterface), RET #e; ∃ (k : Nat) (sent' pend' : List w8),
      ⌜k ≤ (frame bs).length ∧ sent' ++ pend' = sent ++ pend ++ (frame bs).take k ∧
        sent <+: sent' ∧ (e = interface.nil → k = (frame bs).length)⌝ ∗
      sl ↦*{dq} bs ∗ EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e }}

/-- `WriteFlush(writer, data)`: `BufWrite`, then `Flush`; with no error, the frame is sent. -/
abbrev WriteFlush.spec : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sz : Nat) (sent pend : List w8) (err : GoInterface) (sl : GoSlice) (dq : DFrac)
    (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ ⌜bs.length < 2 ^ 32⌝ ∗
      EtcdGrove.io.writerOk wi J Q Ew ∗ EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      □ Q (sent ++ pend ++ frame bs) ∗ sl ↦*{dq} bs }}
    (App (App (Val (@! WriteFlush)) (Val #bw)) (Val #sl))
  {{ (e : GoInterface), RET #e; ∃ (sent' pend' : List w8),
      ⌜sent <+: sent' ∧ sent' ++ pend' <+: sent ++ pend ++ frame bs ∧
        (e = interface.nil → sent' = sent ++ pend ++ frame bs ∧ pend' = [])⌝ ∗
      sl ↦*{dq} bs ∗ EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e }}

/-- `(*Command).MarshalWriteFlush(writer)` (at most one command string): its encoding's frame,
flushed; an encoding of `2^32` bytes or more is not framed (N8, G12): nothing of it is written,
the pending bytes are flushed. -/
abbrev Command.MarshalWriteFlush.spec : Prop :=
  ∀ (l : Loc) (v : Command) (c : CmdV) (bw : Loc) (wi : GoInterfaceOk)
    (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8)
    (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦□ v ∗ cmdRep v c ∗
      ⌜c.commands.length ≤ 1⌝ ∗ EtcdGrove.io.writerOk wi J Q Ew ∗
      EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      □ (⌜(encCmd c).length < 2 ^ 32⌝ -∗ Q (sent ++ pend ++ frame (encCmd c))) }}
    (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"MarshalWriteFlush")) (Val #bw))
  {{ (e : GoInterface), RET #e; ∃ (sent' pend' : List w8),
      ⌜sent <+: sent' ∧
        ((encCmd c).length < 2 ^ 32 ∧ sent' ++ pend' <+: sent ++ pend ++ frame (encCmd c) ∧
          (e = interface.nil → sent' = sent ++ pend ++ frame (encCmd c) ∧ pend' = []) ∨
         2 ^ 32 ≤ (encCmd c).length ∧ sent' ++ pend' <+: sent ++ pend)⌝ ∗
      EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e }}

/-- `(*Msg).MarshalWriteFlush(writer)`. -/
abbrev Msg.MarshalWriteFlush.spec : Prop :=
  ∀ (l : Loc) (v : Msg) (m : MsgV) (bw : Loc) (wi : GoInterfaceOk)
    (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8)
    (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦□ v ∗ msgRep v m ∗
      ⌜(encMsg m).length < 2 ^ 32⌝ ∗ EtcdGrove.io.writerOk wi J Q Ew ∗
      EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      □ Q (sent ++ pend ++ frame (encMsg m)) }}
    (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"MarshalWriteFlush")) (Val #bw))
  {{ (e : GoInterface), RET #e; ∃ (sent' pend' : List w8),
      ⌜sent <+: sent' ∧ sent' ++ pend' <+: sent ++ pend ++ frame (encMsg m) ∧
        (e = interface.nil → sent' = sent ++ pend ++ frame (encMsg m) ∧ pend' = [])⌝ ∗
      EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e }}

/-- `BufRead(reader, data)`: the next frame's payload into `data` (`n` bytes), or an error
(the reader then has read some prefix of the frame; a frame longer than `data` is an error, N6). -/
abbrev BufRead.spec : Prop :=
  ∀ (br : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (sl : GoSlice) (ds : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
      EtcdGrove.bufio.ownBufReader br ri connPre S E R ∗ sl ↦* ds }}
    (App (App (Val (@! BufRead)) (Val #br)) (Val #sl))
  {{ (n : w64) (e : GoInterface), RET (PairV #n #e);
      (⌜e = interface.nil⌝ ∗ ∃ bs, ⌜n = W64 bs.length ∧ bs.length ≤ ds.length⌝ ∗
        sl ↦* (bs ++ ds.drop bs.length) ∗
        EtcdGrove.bufio.ownBufReader br ri connPre S E (R ++ frame bs)) ∨
      (⌜e ≠ interface.nil⌝ ∗ ∃ (R' ds' : List w8), ⌜R <+: R'⌝ ∗ sl ↦* ds' ∗
        EtcdGrove.bufio.ownBufReader br ri connPre S E R') }}

section conn
variable [π : NetProtoGS]

/-- `(*Command).ReadUnmarshal(reader, readBuf)` into a zero `Command`, over a connection's end
`(cn, s)` with the protocol `P`: the next frame, decoded (the protocol says its payload is a
`Command`'s encoding), or an error. -/
abbrev Command.ReadUnmarshal.spec : Prop :=
  ∀ (l : Loc) (br : Loc) (ri : GoInterfaceOk) (cn : Nat) (s : Bool) (P : Proto GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (sl : GoSlice) (ds : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦ (zeroValDef : Command) ∗
      EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E R ∗
      frameIs P cn R (fun bs => ∃ c, bs = encCmd c) ∗ sl ↦* ds }}
    (App (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"ReadUnmarshal")) (Val #br))
      (Val #sl))
  {{ (e : GoInterface), RET #e; ∃ (ds' : List w8), sl ↦* ds' ∗
      ((⌜e = interface.nil⌝ ∗ ∃ (v : Command) (c : CmdV), ⌜(encCmd c).length ≤ ds.length⌝ ∗
          l ↦ v ∗ cmdRep v c ∗
          EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E
            (R ++ frame (encCmd c))) ∨
       (⌜e ≠ interface.nil⌝ ∗ ∃ (R' : List w8) (v : Command), ⌜R <+: R'⌝ ∗ l ↦ v ∗
          EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E
            R')) }}

/-- `(*Msg).ReadUnmarshal(reader, readBuf)` into a zero `Msg`. -/
abbrev Msg.ReadUnmarshal.spec : Prop :=
  ∀ (l : Loc) (br : Loc) (ri : GoInterfaceOk) (cn : Nat) (s : Bool) (P : Proto GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (sl : GoSlice) (ds : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ l ↦ (zeroValDef : Msg) ∗
      EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E R ∗
      frameIs P cn R (fun bs => ∃ m, bs = encMsg m) ∗ sl ↦* ds }}
    (App (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"ReadUnmarshal")) (Val #br))
      (Val #sl))
  {{ (e : GoInterface) (n : w64), RET (PairV #e #n); ∃ (ds' : List w8), sl ↦* ds' ∗
      ((⌜e = interface.nil⌝ ∗ ∃ (v : Msg) (m : MsgV), ⌜(encMsg m).length ≤ ds.length⌝ ∗
          l ↦ v ∗ msgRep v m ∗
          EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E
            (R ++ frame (encMsg m))) ∨
       (⌜e ≠ interface.nil⌝ ∗ ∃ (R' : List w8) (v : Msg), ⌜R <+: R'⌝ ∗ l ↦ v ∗
          EtcdGrove.bufio.ownBufReader br ri connPre (recvTokL (Gg := hG.goose_globalGS) cn s P) E
            R')) }}

end conn

end spec

end Perennial.rabia.internal.message
