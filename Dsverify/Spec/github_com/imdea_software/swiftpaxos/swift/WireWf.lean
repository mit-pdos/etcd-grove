/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/WireWf.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Well-formed SwiftPaxos messages (`Msg.wf`): what every value the code marshals satisfies, so that
frames decode uniquely (Proof/replica/WireWf.lean, `frames_align`). Required of every frame of a
stream by `Inv.lean`'s `framesProto` (change log C9, HUB-REQUEST R1; moved here from
Proof/replica/WireWf.lean).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- A hash: 32 bytes. -/
def Hash.wf (h : Hash) : Prop := h.length = 32

/-- A hash list's well-formedness. -/
def hashesWf (hs : List Hash) : Prop := hs.length < 2 ^ 62 ∧ ∀ h ∈ hs, Hash.wf h

def depWf (d : List CmdId) : Prop := d.length < 2 ^ 62

def Cmd.wf (c : Cmd) : Prop := c.val.length < 2 ^ 16

def FastAck.wf (f : FastAck) : Prop := depWf f.dep ∧ hashesWf f.cs
def Ack.wf (a : Ack) : Prop := depWf a.dep ∧ hashesWf a.cs

/-- An `MSync`'s codec encoding (`gobFrame`'s 8-byte length counts it). -/
def SyncWire.wf (m : SyncWire) : Prop := (KitVal.msync m).encode.length < 2 ^ 64

/-- A message is well formed: what every value the code marshals satisfies (a hash is a
`[32]byte`, a value's length fits `Value.Marshal`'s 16 bits, lengths fit the varints, an
`MSync`'s encoding fits the frame's length). -/
def Msg.wf : Msg → Prop
  | .propose _ _ c _ => c.wf
  | .beacon _ | .beaconReply _ | .lightSlowAck _ | .newLeader _ _ => True
  | .fastAck f => f.wf
  | .fastAckClient _ _ _ cs => hashesWf cs
  | .acks fs ss => (fs.length < 2 ^ 62 ∧ ∀ f ∈ fs, f.wf) ∧ ss.length < 2 ^ 62
  | .optAcks _ _ al => al.length < 2 ^ 62 ∧ ∀ a ∈ al, a.wf
  | .reply _ _ _ cs v => hashesWf cs ∧ v.length < 2 ^ 62
  | .newLeaderAckN _ _ _ es => es.length < 2 ^ 62 ∧ ∀ e ∈ es, e.cmd.wf ∧ depWf e.dep
  | .sync m => m.wf

end sp

end Perennial.github_com.imdea_software.swiftpaxos
