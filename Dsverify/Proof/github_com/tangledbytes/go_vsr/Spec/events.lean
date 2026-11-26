/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/events.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension. What changed:
* a connection end is the net extension's (`net.isConn c cn s a`, a `Conn` value holding a
  `*TCPConn`, persistent; `Nat` connection ids; `sendTok`/`recvTok` of `GooseLang/Ext/Net/Proto.lean`)
  instead of the lab's `*net.TCPConn` with `net.ownTCPConn c cid side`; `wstream` and `rstream`
  are stated over it;
* `rstream`'s decoder state is the `encoding/json` vocabulary's `DecoderRep` (`decOk`/`decErr`,
  `Spec/jsonlib.lean`: the model's `Decoder` is opaque here), not the lab model's fields (`buf`,
  `scanp`, `err`, `rerr`); the read error the lab kept (`net.connErr`) is the representation's;
* the hook's lock invariant (`hookLockInvFull γh`), its lock (`hookKnownFull`, the lab's
  `hookKnown`) and `frameDecoderSet` are package facts, in `pkg/events/Base.lean` (events' and
  `vsrwire`'s): a set hook holds `vsrwire`'s `decodeFrame` (`kitFrameDecoder`), not any `f` with
  `frameDecOk f` (the lab's), so that the facts name no class of this file; `SetFrameDecoder.spec`
  is at `decodeFrame`, and `FromDecoder`'s proof has `frameDecOk` from `decodeFrame`'s spec;
* `events.initialize'.spec` is gone (the generated `pkg/events/Init.lean` proves initialization);
* the JSON codec is `models_lab.jsoncodec`'s (`JsonCodec`), `codecSet`/`kitCodecOk`/`bufio.errOrNil`
  `Spec/jsonlib.lean`'s.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Basic
public import Perennial.Ghost.MonoList
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.jsonlib
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrwire.Base
public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The event type of a message (`EventRequest` = 1, ..., `EventHeartbeat` = 11). -/
def events.typeOf : Msg → w8
  | .request .. => W8 1
  | .reply .. => W8 2
  | .prepare .. => W8 3
  | .prepareOK .. => W8 4
  | .commit .. => W8 5
  | .startViewChange .. => W8 6
  | .doViewChange .. => W8 7
  | .startView .. => W8 8
  | .getState .. => W8 9
  | .newState .. => W8 10
  | .heartbeat => W8 11

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions]

/-- The `events.Request` value `r` is the request `(id, cid, op)`. -/
def events.reqIs (r : events.Request) (id cid : Nat) (op : GoString) : Prop :=
  uint.nat r.ID' = id ∧ uint.nat r.ClientID' = cid ∧ r.Op' = op

/-- The `Data` value `d` is message `m`'s payload (persistent): a struct value of `m`'s payload
type with `m`'s fields (the numbers as `uint64`s), its `Logs` read-only. -/
def events.payloadOf (d : GoInterface) : Msg → IProp GF
  | .request id cid op => iprop(∃ x : events.Request,
      ⌜d = interface.mkOk events.Request.ty #x ∧ events.reqIs x id cid op⌝)
  | .reply id cid v res => iprop(∃ x : events.Reply,
      ⌜d = interface.mkOk events.Reply.ty #x ∧ uint.nat x.ID' = id ∧
        uint.nat x.ClientID' = cid ∧ uint.nat x.ViewNum' = v ∧ x.Result' = res⌝)
  | .prepare v k c e rid => iprop(∃ x : events.Prepare,
      ⌜d = interface.mkOk events.Prepare.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.OpNum' = k ∧ uint.nat x.CommitNum' = c ∧
        events.reqIs x.Request' e.req e.cid e.op ∧ uint.nat x.ReplicaID' = rid⌝)
  | .prepareOK v k rid => iprop(∃ x : events.PrepareOK,
      ⌜d = interface.mkOk events.PrepareOK.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.OpNum' = k ∧ uint.nat x.ReplicaID' = rid⌝)
  | .commit v c rid => iprop(∃ x : events.Commit,
      ⌜d = interface.mkOk events.Commit.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.CommitNum' = c ∧ uint.nat x.ReplicaID' = rid⌝)
  | .startViewChange v rid => iprop(∃ x : events.StartViewChange,
      ⌜d = interface.mkOk events.StartViewChange.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.ReplicaID' = rid⌝)
  | .doViewChange dv => iprop(∃ x : events.DoViewChange,
      ⌜d = interface.mkOk events.DoViewChange.ty #x ∧ uint.nat x.ViewNum' = dv.view ∧
        uint.nat x.LastStableViewNum' = dv.lnv ∧ uint.nat x.OpNum' = dv.log.length ∧
        uint.nat x.CommitNum' = dv.commit ∧ uint.nat x.ReplicaID' = dv.rid⌝ ∗
      log.ownLogs x.Logs' DFrac.discard dv.log)
  | .startView v k c logs rid => iprop(∃ x : events.StartView,
      ⌜d = interface.mkOk events.StartView.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.OpNum' = k ∧ uint.nat x.CommitNum' = c ∧ uint.nat x.ReplicaID' = rid⌝ ∗
      log.ownLogs x.Logs' DFrac.discard logs)
  | .getState v k rid => iprop(∃ x : events.GetState,
      ⌜d = interface.mkOk events.GetState.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.OpNum' = k ∧ uint.nat x.ReplicaID' = rid⌝)
  | .newState v logs c k rid => iprop(∃ x : events.NewState,
      ⌜d = interface.mkOk events.NewState.ty #x ∧ uint.nat x.ViewNum' = v ∧
        uint.nat x.CommitNum' = c ∧ uint.nat x.OpNum' = k ∧ uint.nat x.ReplicaID' = rid⌝ ∗
      log.ownLogs x.Logs' DFrac.discard logs)
  | .heartbeat => iprop(∃ x : events.Heartbeat, ⌜d = interface.mkOk events.Heartbeat.ty #x⌝)

instance events.payloadOf_persistent (d : GoInterface) (m : Msg) :
    Persistent (events.payloadOf (GF := GF) d m) := by
  cases m <;> unfold events.payloadOf <;> infer_instance

instance events.payloadOf_timeless (d : GoInterface) (m : Msg) :
    Timeless (events.payloadOf (GF := GF) d m) := by
  cases m <;> unfold events.payloadOf <;> infer_instance

/-- The `*Event` `ev` is message `m`'s event (persistent). -/
def events.isEvent (ev : Loc) (m : Msg) : IProp GF :=
  iprop(∃ d : GoInterface, ev ↦□ events.Event.mk (events.typeOf m) d ∗ events.payloadOf d m)

instance events.isEvent_persistent (ev : Loc) (m : Msg) : Persistent (events.isEvent (GF := GF) ev m) :=
  by unfold events.isEvent; infer_instance
instance events.isEvent_timeless (ev : Loc) (m : Msg) : Timeless (events.isEvent (GF := GF) ev m) :=
  by unfold events.isEvent; infer_instance

/-- The capacity of the `Logs` slice of `ev`'s payload, for a DoViewChange or a StartView
(exclusive; a NewState's is not needed: `Merge` copies its entries). -/
def events.evCap (ev : Loc) : Msg → IProp GF
  | .doViewChange _ => iprop(∃ x : events.DoViewChange,
      ev ↦□ events.Event.mk (W8 7) (interface.mkOk events.DoViewChange.ty #x) ∗
      ownSliceCap log.Log x.Logs' (DFrac.own 1))
  | .startView .. => iprop(∃ x : events.StartView,
      ev ↦□ events.Event.mk (W8 8) (interface.mkOk events.StartView.ty #x) ∗
      ownSliceCap log.Log x.Logs' (DFrac.own 1))
  | _ => iprop(True)

/-- The JSON encoding of message `m`'s payload (the `data` member of `VsrWire.encEvent m`, as it
appears there).
-- sealed: the JSON codec's choice -/
def events.encPayload (m : Msg) : List w8 := VsrJson.encPayload m

/-- The payload type of message `m`. -/
def events.payloadTy : Msg → go.GoType
  | .request .. => events.Request.ty
  | .reply .. => events.Reply.ty
  | .prepare .. => events.Prepare.ty
  | .prepareOK .. => events.PrepareOK.ty
  | .commit .. => events.Commit.ty
  | .startViewChange .. => events.StartViewChange.ty
  | .doViewChange .. => events.DoViewChange.ty
  | .startView .. => events.StartView.ty
  | .getState .. => events.GetState.ty
  | .newState .. => events.NewState.ty
  | .heartbeat => events.Heartbeat.ty

/-- `p` holds the zero value of `m`'s payload type (`var v T` in `FromDecoder`). -/
def events.payloadZero (p : Loc) : Msg → IProp GF
  | .request .. => iprop(p ↦ (zero_val events.Request))
  | .reply .. => iprop(p ↦ (zero_val events.Reply))
  | .prepare .. => iprop(p ↦ (zero_val events.Prepare))
  | .prepareOK .. => iprop(p ↦ (zero_val events.PrepareOK))
  | .commit .. => iprop(p ↦ (zero_val events.Commit))
  | .startViewChange .. => iprop(p ↦ (zero_val events.StartViewChange))
  | .doViewChange .. => iprop(p ↦ (zero_val events.DoViewChange))
  | .startView .. => iprop(p ↦ (zero_val events.StartView))
  | .getState .. => iprop(p ↦ (zero_val events.GetState))
  | .newState .. => iprop(p ↦ (zero_val events.NewState))
  | .heartbeat => iprop(p ↦ (zero_val events.Heartbeat))

/-- `p` holds `m`'s payload (decoded: its `Logs`, if any, read-only, with their capacity). -/
def events.payloadAt (p : Loc) : Msg → IProp GF
  | m@(.request ..) => iprop(∃ x : events.Request, p ↦ x ∗
      events.payloadOf (interface.mkOk events.Request.ty #x) m)
  | m@(.reply ..) => iprop(∃ x : events.Reply, p ↦ x ∗
      events.payloadOf (interface.mkOk events.Reply.ty #x) m)
  | m@(.prepare ..) => iprop(∃ x : events.Prepare, p ↦ x ∗
      events.payloadOf (interface.mkOk events.Prepare.ty #x) m)
  | m@(.prepareOK ..) => iprop(∃ x : events.PrepareOK, p ↦ x ∗
      events.payloadOf (interface.mkOk events.PrepareOK.ty #x) m)
  | m@(.commit ..) => iprop(∃ x : events.Commit, p ↦ x ∗
      events.payloadOf (interface.mkOk events.Commit.ty #x) m)
  | m@(.startViewChange ..) => iprop(∃ x : events.StartViewChange, p ↦ x ∗
      events.payloadOf (interface.mkOk events.StartViewChange.ty #x) m)
  | m@(.doViewChange ..) => iprop(∃ x : events.DoViewChange, p ↦ x ∗
      events.payloadOf (interface.mkOk events.DoViewChange.ty #x) m ∗
      ownSliceCap log.Log x.Logs' (DFrac.own 1))
  | m@(.startView ..) => iprop(∃ x : events.StartView, p ↦ x ∗
      events.payloadOf (interface.mkOk events.StartView.ty #x) m ∗
      ownSliceCap log.Log x.Logs' (DFrac.own 1))
  | m@(.getState ..) => iprop(∃ x : events.GetState, p ↦ x ∗
      events.payloadOf (interface.mkOk events.GetState.ty #x) m)
  | m@(.newState ..) => iprop(∃ x : events.NewState, p ↦ x ∗
      events.payloadOf (interface.mkOk events.NewState.ty #x) m ∗
      ownSliceCap log.Log x.Logs' (DFrac.own 1))
  | m@(.heartbeat) => iprop(∃ x : events.Heartbeat, p ↦ x ∗
      events.payloadOf (interface.mkOk events.Heartbeat.ty #x) m)

/-- Where a healthy decoder stands in its stream (pure): `R` read from the connection, `U` the
unread bytes of its buffer (a suffix of `R`), the messages `ms` decoded (`pend = none`: `R` is
their lines, then `U` without its leading newline, if any; `pend = some m`: `m` was decoded last
and its line's newline has not been read yet). -/
def events.rstreamAt (ms : List Msg) (pend : Option Msg) (U R : List w8) : Prop :=
  match pend with
  | none => ∃ ws U', (ws = [] ∨ ws = [W8 10]) ∧ U = ws ++ U' ∧ R = VsrWire.lines ms ++ U'
  | some m => PlainMsg m ∧ R = VsrWire.lines ms ++ VsrWire.encEvent m ++ U

end defs

section streams
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions] [net.Assumptions]
variable [π : NetProtoGS]

/-- The writer `w`'s stream (see the file header): `w` is the end `s` of a connection `cn` (a
`Conn` holding a `*TCPConn`; `net` initialized), whose written stream (protocol `protoOf γ`) is
`W`. -/
def events.wstream (γ : VsrGhost.Names) (w : GoInterface) (ok : Bool) : IProp GF :=
  iprop(∃ (cn : Nat) (s : Bool) (a : GoString) (W : List w8),
    net.isConn w cn s a ∗ isPkgInit (PROP := IProp GF) pkg_id.net ∗ sendTok cn s (VsrWire.protoOf γ) W ∗
    if ok then iprop(∃ ms : List Msg, ⌜W = VsrWire.lines ms⌝ ∗
      ⌜∀ m ∈ ms, PlainMsg m ∧ MsgBound m ∧ (VsrWire.line m).length < 2 ^ 60⌝ ∗
      [∗list] m ∈ ms, VsrGhost.fact γ (.msg m))
    else iprop(True))

variable [encoding.json.DecoderRep GF]

/-- The decoder `dec`'s stream (see the file header): `dec` reads the connection end `c` (the end
`s` of `cn`); its sticky error is set (it returns it for good: `decErr`), or it is healthy
(`decOk`): it has read `R` (the reader's token `recvTok`, inside), its unread bytes are `U`, and
`R`, `U` stand as `rstreamAt` says.
-- sealed: the package's choice -/
def events.rstream (γ : VsrGhost.Names) (dec : Loc) : IProp GF :=
  iprop(∃ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString),
    net.isConn c cn s a ∗ isPkgInit (PROP := IProp GF) pkg_id.net ∗
    (encoding.json.DecoderRep.decErr dec c ∨
     ∃ (R U : List w8) (ms : List Msg) (pend : Option Msg),
       encoding.json.DecoderRep.decOk dec c (recvTok cn s (VsrWire.protoOf γ)) R U ∗
       ⌜events.rstreamAt ms pend U R⌝))

end streams

section hook
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions]
variable [net.Assumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [models_lab.jsoncodec.JsonCodec GF]

/-- The frame decoder `f` (`func(*json.Decoder) (uint8, json.RawMessage, error)`, the G1 hook's
value): on a decoder of `γ`'s stream it returns the next frame, a valid message's type and
its payload's bytes (the message's strings plain, its numbers in `uint64`: what decoding the
payload needs, `vsrnet.dec_payload`; D5), or an error (persistent). -/
def events.frameDecOk (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (F : List w8 → Bool → w64 × w64) (γ : VsrGhost.Names) (dec : Loc),
    {{ encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F ∗
        events.rstream γ dec }}
      (App (Val #f) (Val #dec))
    {{ (t : w8) (data : GoSlice) (err : GoInterface), RET (PairV (PairV #t #data) #err);
        events.rstream γ dec ∗
        if decide (err = interface.nil) then ∃ m : Msg, ⌜t = events.typeOf m⌝ ∗
          data ↦* events.encPayload m ∗ ⌜PlainMsg m⌝ ∗ ⌜MsgBound m⌝ ∗ VsrGhost.fact γ (.msg m)
        else bufio.errOrNil err }})

instance events.frameDecOk_persistent (f : GoFunc) : Persistent (events.frameDecOk (GF := GF) f) := by
  unfold events.frameDecOk; infer_instance

end hook

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions]
variable [net.Assumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- `NewNetworkEvent(src, ev)`: the pair. -/
abbrev events.NewNetworkEvent.spec : Prop :=
  ∀ (src : ipv4port.IPv4Port) (ev : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events }}
    (App (App (Val (@! events.NewNetworkEvent)) (Val #src)) (Val #ev))
  {{ RET #(events.NetworkEvent.mk src ev); True }}

/-- `ev.ToWriter(w)`, `ev` a valid message's event (its strings plain: the caller has it from
`VsrGhost.fact_plain`; its numbers in `uint64`, its line below 2^60 bytes: from the caller's
`uint64`s and `VsrWire.line_bound` with `VsrGhost.ghost_pure`; SF4, D5), `w`'s stream whole
lines: the event's line is written (`err` nil, whole lines again) or the write failed (`err`
non-nil; the stream may end in part of the line). -/
abbrev events.Event.ToWriter.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (γ : VsrGhost.Names) (ev : Loc) (m : Msg)
    (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events ∗
      encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F ∗
      events.isEvent ev m ∗ VsrGhost.fact γ (.msg m) ∗ ⌜PlainMsg m⌝ ∗ ⌜MsgBound m⌝ ∗
      ⌜(VsrWire.line m).length < 2 ^ 60⌝ ∗ events.wstream γ w true }}
    (App (Val (ev @!! go.GoType.PointerType events.Event.ty @!! go!"ToWriter")) (Val #w))
  {{ (err : GoInterface), RET #err; events.wstream γ w (decide (err = interface.nil)) ∗
      bufio.errOrNil err }}

/-- `json.NewDecoder(conn)` over a connection end `c` (the end `s` of `cn`) that has read nothing,
whose stream protocol is `protoOf γ`: a decoder of `γ`'s stream (proved at the model's decoder,
`decRepModel`: `Proof/events/DecodeFrame.lean`). -/
abbrev events.newDecoder.spec : Prop :=
  ∀ (γ : VsrGhost.Names) (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.isConn c cn s a ∗
      recvTok cn s (VsrWire.protoOf γ) [] }}
    (App (Val (@! encoding.json.NewDecoder)) (Val #c))
  {{ (dec : Loc), RET #dec; events.rstream γ dec }}

/-- `dec.Decode(&f)` into a `vsrwire.Frame` with a nil `Data` (the hook `vsrwire` installs calls
it on a `Frame{}`; codec-3, D5), on a decoder of `γ`'s stream: the next frame, a valid
message's type and payload bytes, or an error. Over the main tree's dispatch (#24 J3): a codec
registered (`codecSet`: `Decode` takes the registered codec's `Scan` to read the next value,
`getCodec`) and `unmarshalVia` at `&f` (the contract the instance gives; `*vsrwire.Frame` has
`JSONModelUnmarshal`, so its method, and `jsoncodec.Scan` computes `F`).

Proved of the model's `Decode` (`v2_stream.go`) at its decoder (`decRepModel`) and the kit's
contract `vsrnet.jsonCodec` (`Proof/events/DecodeFrame.lean`): a sticky error is returned again (`decErr`); else `readValue` reads up to the
end of the next value with the registered codec's `Scan` (`jsoncodec.Scan`), fetching from the
connection (`recvTok`), so the value read is whitespace and the next line's `encEvent m` of a
message `γ`'s stream has (`rstreamAt`), or a read error is returned and kept; then the frame's
`JSONModelUnmarshal` decodes it, which `unmarshalAt` (inside `unmarshalVia`) says meets
`vsrnet.jsonCodec`'s `decP` frame case: `Frame{typeOf m, data}`, `data` a fresh slice of
`encPayload m`. -/
abbrev events.Decoder.Decode_frame.spec : Prop :=
  ∀ (γ : VsrGhost.Names) (dec p : Loc)
    (fr : examples.vsrwire.Frame), fr.Data' = slice.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      encoding.json.codecSet (GF := GF) ∗
      encoding.json.unmarshalVia inferInstance JsonScan.scanF
        (interface.mkOk (go.GoType.PointerType examples.vsrwire.Frame.ty) #p) ∗
      events.rstream γ dec ∗ p ↦ fr }}
    (App (Val (dec @!! go.GoType.PointerType encoding.json.Decoder.ty @!! go!"Decode"))
      (Val #(interface.mkOk (go.GoType.PointerType examples.vsrwire.Frame.ty) #p)))
  {{ (err : GoInterface), RET #err; events.rstream γ dec ∗
      if decide (err = interface.nil) then ∃ (m : Msg) (data : GoSlice),
        p ↦ examples.vsrwire.Frame.mk (events.typeOf m) data ∗
        data ↦* events.encPayload m ∗ ⌜PlainMsg m⌝ ∗ ⌜MsgBound m⌝ ∗ VsrGhost.fact γ (.msg m)
      else ∃ fr' : examples.vsrwire.Frame, p ↦ fr' ∗ bufio.errOrNil err }}

/-- `ev.FromDecoder(dec)` (the hook set for good to a frame decoder: `frameDecoderSet`,
`vsrwire`'s package state; D11), on a decoder of `γ`'s stream: the next event, a valid
message's (with its payload's `Logs` capacity), or an error. -/
abbrev events.Event.FromDecoder.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (γ : VsrGhost.Names) (ev dec : Loc) (e0 : events.Event),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events ∗
      events.frameDecoderSet ∗
      encoding.json.codecSet (GF := GF) ∗
      encoding.json.kitCodecOk F ∗ events.rstream γ dec ∗ ev ↦ e0 }}
    (App (Val (ev @!! go.GoType.PointerType events.Event.ty @!! go!"FromDecoder")) (Val #dec))
  {{ (err : GoInterface), RET #err; events.rstream γ dec ∗ bufio.errOrNil err ∗
      if decide (err = interface.nil) then ∃ m : Msg, events.isEvent ev m ∗
        events.evCap ev m ∗ VsrGhost.fact γ (.msg m)
      else ∃ e : events.Event, ev ↦ e }}

/-- `SetFrameDecoder(decodeFrame)` (D11; `vsrwire`'s `init`, its only caller): the hook is set
for good (to `decodeFrame`, by this call or an earlier one). -/
abbrev events.SetFrameDecoder.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events }}
    (App (Val (@! events.SetFrameDecoder)) (Val #events.kitFrameDecoder))
  {{ RET #(); events.frameDecoderSet }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
