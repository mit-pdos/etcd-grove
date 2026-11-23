/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Wire/Basic.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, the net extension's `addrProto` for the lab's `addrProtoG netDistGS`;
the configuration's wire (`confBytes`, `ConfOk`, `cfgAddrs`, `confProto`, `ackProto`, `confProtos`)
moved to `examples/vsrnet/Conf.lean`; `addrs` (the lab's `github_com.tangledbytes.go_vsr.addrs`,
`VsrNetSpec.lean`) defined here from the kit's `Addrs()`.
-/
/-
The wire: how the model's messages travel. Each event is sent as one line, its JSON encoding
(the kit's codec's output for `events.Event{Type, Data}`, `json.Encoder.Encode`) and a newline;
every connection's streams (both directions, every address) follow `protoOf γ`: what was written
is a prefix of the lines of valid messages.

* `encEvent m`: the codec's encoding of the event of message `m` (its type and payload; the
  numbers as the payload types' `,string` fields, the strings plain).
* `protoOf γ`: the protocol of every configured address, for what dialers and acceptors write
  (a prefix of the lines of valid messages with plain strings, `MsgBound` numbers and lines
  below 2^60 bytes); `protos γ`: every configured address has it.
* `line_bound`: a valid message's line is below 2^60 bytes (SF4, D5).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.System
public import GooseLang.Ext.Net.Proto
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Frame
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.LineBound

@[expose] public section

noncomputable section

namespace VsrWire

open Perennial Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode VsrModel VsrGhost Net

/-- The JSON encoding of message `m`'s event (`jsonMarshal(&events.Event{Type, Data})`). -/
def encEvent (m : Msg) : List w8 := VsrJson.encEvent m

/-- One line: an event's encoding and a newline (`Encoder.Encode`). -/
def line (m : Msg) : List w8 := encEvent m ++ [W8 10]

/-- The go-vsr addresses of the machines (the kit's `Addrs()`, `kit.go`: machine `i` at
`127.0.0.1:(7500 + i)`; 0 the orchestrator (unused), client `c` on `1 + c`, then the servers); the lab's
`github_com.tangledbytes.go_vsr.addrs` (`VsrNetSpec.lean`, its `Addrs()`). -/
def addrs : List GoString :=
  [go!"127.0.0.1:7500", go!"127.0.0.1:7501", go!"127.0.0.1:7502",
   go!"127.0.0.1:7503", go!"127.0.0.1:7504", go!"127.0.0.1:7505",
   go!"127.0.0.1:7506", go!"127.0.0.1:7507", go!"127.0.0.1:7508",
   go!"127.0.0.1:7509", go!"127.0.0.1:7510", go!"127.0.0.1:7511"]

/-- The lines of a sequence of messages. -/
def lines (ms : List Msg) : List w8 := (ms.map line).flatten

/-- A valid message's line is short (SF4, D5): its logs are bounded (`VsrModel.vlog_length_le`:
registrations bounded, no duplicates), its strings are (`InputBounded`), and so are its numbers
(`MsgBound`). What the reader's decoder needs (its buffer arithmetic). -/
theorem line_bound (s : Sys) (h : Inv s) (m : Msg) (hm : MsgValid s m) (hb : MsgBound m) :
    (line m).length < 2 ^ 60 := by
  have := VsrLineBound.encEvent_bound s h m hm hb
  simp only [line, encEvent, List.length_append, List.length_singleton]
  omega

section defs
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]
variable [π : NetProtoGS]

/-- The stream protocol of every address: a prefix of the lines of valid messages, whose strings
are plain, whose numbers fit in `uint64` (`MsgBound`) and whose lines are below 2^60 bytes (so a
reader can frame and decode every line: the decoding facts need `PlainMsg` and `MsgBound`, the
decoder's buffer the line bound; SF4, D5). -/
def protoOf (γ : Names) : Proto GF :=
  fun _cid W => iprop(∃ ms : List Msg, ⌜W <+: lines ms⌝ ∗
    ⌜∀ m ∈ ms, PlainMsg m ∧ MsgBound m ∧ (line m).length < 2 ^ 60⌝ ∗
    [∗list] m ∈ ms, fact γ (.msg m))

theorem lines_eq (ms : List Msg) : lines ms = VsrJson.linesL ms := by
  simp only [lines, line, VsrJson.linesL, encEvent]
  rfl

theorem lines_append (a b : List Msg) : lines (a ++ b) = lines a ++ lines b := by
  simp [lines]

/-- A reader's view: if `R` was read from a stream with protocol `protoOf γ` and `R` starts with
the lines of `ms`, those messages are valid (the encodings frame: a line is never a prefix of
another, so the lines of a prefix are the stream's first messages). -/
theorem protoOf_lines (γ : Names) (cid : Nat) (ext R : List w8) (ms : List Msg)
    (hR : R <+: ext) (hms : lines ms <+: R) :
    □ protoOf (GF := GF) γ cid ext ⊢ ⌜∀ m ∈ ms, PlainMsg m ∧ MsgBound m ∧ (line m).length < 2 ^ 60⌝ ∗
      [∗list] m ∈ ms, fact γ (.msg m) := by
  iintro #H
  unfold protoOf
  icases H with ⟨%ms', %hext, %hpl, #Hf⟩
  have hl : lines ms <+: lines ms' := hms.trans (hR.trans hext)
  rw [lines_eq, lines_eq] at hl
  obtain ⟨t, rfl⟩ := VsrJson.lines_prefix ms ms' (fun m hm => (hpl m hm).1) hl
  ihave Hf2 := (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hf
  icases Hf2 with ⟨#H1, -⟩
  isplitr
  · ipureintro; exact fun m hm => hpl m (List.mem_append_left _ hm)
  · iexact H1

/-- A reader's view of what may come next: if `R` was read from a stream with protocol
`protoOf γ` and `R` is the lines of `ms` followed by a non-empty `rest`, then `rest` starts a
line of a valid message with plain strings, its numbers in `uint64`, its line below 2^60 bytes
(what the decoder frames next). -/
theorem protoOf_next (γ : Names) (cid : Nat) (ext R : List w8) (ms : List Msg) (rest : List w8)
    (hR : R <+: ext) (hms : R = lines ms ++ rest) (hne : rest ≠ []) :
    □ protoOf (GF := GF) γ cid ext ⊢ ∃ m : Msg, ⌜rest <+: line m ∨ line m <+: rest⌝ ∗ ⌜PlainMsg m⌝ ∗
      ⌜MsgBound m⌝ ∗ ⌜(line m).length < 2 ^ 60⌝ ∗ fact γ (.msg m) := by
  iintro #H
  unfold protoOf
  icases H with ⟨%ms', %hext, %hpl, #Hf⟩
  have hl0 : lines ms ++ rest <+: lines ms' := hms ▸ hR.trans hext
  have hl : lines ms <+: lines ms' := (List.prefix_append _ _).trans hl0
  rw [lines_eq, lines_eq] at hl
  obtain ⟨t, rfl⟩ := VsrJson.lines_prefix ms ms' (fun m hm => (hpl m hm).1) hl
  rw [lines_append] at hl0
  have hrt := (List.prefix_append_right_inj _).1 hl0
  cases t with
  | nil => simp [lines] at hrt; exact absurd hrt hne
  | cons m t' =>
    have hlt : lines (m :: t') = line m ++ lines t' := by simp [lines]
    rw [hlt] at hrt
    have hor := List.prefix_or_prefix_of_prefix hrt (List.prefix_append (line m) (lines t'))
    have hmem : m ∈ ms ++ m :: t' := by simp
    iexists m
    ihave Hm := (BigSepL.bigSepL_mem (PROP := IProp GF) hmem) $$ Hf
    iframe Hm
    ipureintro
    exact ⟨hor, (hpl m hmem).1, (hpl m hmem).2.1, (hpl m hmem).2.2⟩

/-- Every configured address's protocols are `protoOf γ` both ways (persistent; the start sets
them; `network.netProtos` is this). -/
def protos (γ : Names) : IProp GF :=
  iprop([∗list] a ∈ addrs, addrProto (Gg := G) a (protoOf γ) (protoOf γ))

end defs

end VsrWire
