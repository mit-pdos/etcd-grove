/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Net.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The transport's API (`tcpnet.go`), stage 1 interface (frozen at `stage1-frozen`).

The transport is generic in a persistent message predicate `Φ` (the deployment chooses
`msgOK Γ`, `Inv.lean`): every address's protocol is `wireProto Φ` for what dialers write (whole
frames of messages that meet `Φ`) and `noProto` for what acceptors write (nothing is written on
an accepted connection), so a frame a reader completes is a frame some dialer wrote, of a message
meeting `Φ` (`parse_frames_prefix`).

* `is_node nd Φ amap ids` (persistent): the node `nd` (`newTCPNode`'s result): its read-only map
  `addrs` is `amap` (agent → address, each address with protocols `wireProto Φ`/`noProto`), and
  its inboxes are one bag channel per agent of `ids`, holding messages to that agent that meet
  `Φ`.
* `own_net nt Φ nd me` (exclusive): agent `me`'s network `nt` on `nd` (`network`'s result): its
  dialed connections, each with its writer's token, all of whose bytes are whole frames of
  messages meeting `Φ`. Owned by the one goroutine that sends (`send`) or receives on it.

Design decision D2 (`notes/decisions.md`): the transport takes `Φ` as a parameter (a HoCAP-style
predicate), not a ghost set of sent messages: the address protocols are fixed once at the start
for every node and must say what the bytes mean, and every fact the protocol layer needs of a
message is persistent.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Wire

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- What dialers write: whole frames of messages that fit and meet `Φ`. -/
def wireProto (Φ : message → IProp GF) : Proto GF := fun _ bs =>
  iprop(∃ ms : List message, ⌜bs = frames ms ∧ ∀ m ∈ ms, msgWf m⌝ ∗ [∗list] m ∈ ms, Φ m)

/-- What acceptors write: nothing is ever written on an accepted connection. -/
def noProto : Proto GF := fun _ _ => iprop(True)

/-- An inbox: a bag channel of messages to `id` that fit and meet `Φ`. -/
def inboxP (Φ : message → IProp GF) (id : w64) (m : message) : IProp GF :=
  iprop(Φ m ∗ ⌜m.to' = id ∧ msgWf m⌝)

/-- The node `nd`, made by `newTCPNode` (persistent). -/
def is_node (nd : Loc) (Φ : message → IProp GF) (amap : GMap w64 GoString) (ids : List w64) :
    IProp GF :=
  iprop(∃ (am im : Loc) (ib : GMap w64 Loc),
    nd.[tcpNode, go!"addrs"] ↦□ am ∗ nd.[tcpNode, go!"inbox"] ↦□ im ∗
    am ↦$□ amap ∗ im ↦$□ ib ∗ ⌜∀ id, (ib !! id).isSome ↔ id ∈ ids⌝ ∗
    ([∗map] id ↦ ch ∈ ib, ∃ γ, isChanBag γ ch (inboxP Φ id)) ∗
    [∗map] _id ↦ a ∈ amap, addrProto (Gg := hG.goose_globalGS) a (wireProto Φ) noProto)

/-- A dialed connection of `own_net`: the dialer's end (of a connection dialed to some address)
and its writer's token, every byte written being whole frames that meet the protocol. -/
def connOK (Φ : message → IProp GF) (cv : GoInterface) : IProp GF :=
  iprop(∃ (cn : Nat) (a : GoString) (W : List w8),
    net.isConn cv cn false a ∗ sendTok (Gg := hG.goose_globalGS) cn false (wireProto Φ) W ∗
    □ wireProto Φ cn W)

/-- Agent `me`'s network `nt` on node `nd` (exclusive). -/
def own_net (nt : Loc) (Φ : message → IProp GF) (nd : Loc) (me : w64) : IProp GF :=
  iprop(∃ (cm : Loc) (conns : GMap w64 GoInterface),
    nt.[tcpNetwork, go!"node"] ↦□ nd ∗ nt.[tcpNetwork, go!"me"] ↦□ me ∗
    nt.[tcpNetwork, go!"conns"] ↦□ cm ∗ cm ↦$ conns ∗
    [∗map] _to ↦ cv ∈ conns, connOK Φ cv)

instance wireProto_persistent (Φ : message → IProp GF) [∀ m, Persistent (Φ m)] (cn : Nat)
    (bs : List w8) : Persistent (wireProto Φ cn bs) := by
  unfold wireProto; infer_instance

instance is_node_persistent (nd : Loc) (Φ : message → IProp GF) (amap : GMap w64 GoString)
    (ids : List w64) : Persistent (is_node nd Φ amap ids) := by
  unfold is_node; infer_instance

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

local notation "pkg" => pkg_id.github_com.xiang90.paxos

/-- `newTCPNode(addrs, local)`: the node over the address map `amap` (consumed: the node keeps
it read-only) with an inbox for each agent of `ids`. -/
abbrev newTCPNode.spec : Prop :=
  ∀ (Φ : message → IProp GF) [∀ m, Persistent (Φ m)] (am : Loc) (amap : GMap w64 GoString)
    (sl : GoSlice) (ids : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ am ↦$ amap ∗ sl ↦*{dq} ids ∗
      [∗map] _id ↦ a ∈ amap, addrProto (Gg := hG.goose_globalGS) a (wireProto Φ) noProto }}
    (App (App (Val (@! newTCPNode)) (Val #am)) (Val #sl))
  {{ (nd : Loc), RET #nd; is_node nd Φ amap ids ∗ sl ↦*{dq} ids }}

/-- `nd.serve(addr, tries)`: listens on `addr` (whose protocols are the wire's) and accepts and
reads connections in the background. -/
abbrev tcpNode.serve.spec : Prop :=
  ∀ (Φ : message → IProp GF) [∀ m, Persistent (Φ m)] (nd : Loc) (amap : GMap w64 GoString)
    (ids : List w64) (a : GoString) (tries : w64),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Φ amap ids ∗
      addrProto (Gg := hG.goose_globalGS) a (wireProto Φ) noProto }}
    (App (App (Val (nd @!! go.GoType.PointerType tcpNode.ty @!! go!"serve")) (Val #a)) (Val #tries))
  {{ (ok : Bool), RET #ok; True }}

/-- `nd.network(id)`: agent `id`'s network. -/
abbrev tcpNode.network.spec : Prop :=
  ∀ (Φ : message → IProp GF) (nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Φ amap ids }}
    (App (Val (nd @!! go.GoType.PointerType tcpNode.ty @!! go!"network")) (Val #id))
  {{ (nt : Loc), RET #nt; own_net nt Φ nd id }}

/-- `nt.send(m)`: sends a message that fits and meets `Φ` (or drops it). -/
abbrev tcpNetwork.send.spec : Prop :=
  ∀ (Φ : message → IProp GF) [∀ m, Persistent (Φ m)] (nt nd : Loc) (amap : GMap w64 GoString)
    (ids : List w64) (me : w64) (m : message),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Φ amap ids ∗ own_net nt Φ nd me ∗ Φ m ∗
      ⌜msgWf m⌝ }}
    (App (Val (nt @!! go.GoType.PointerType tcpNetwork.ty @!! go!"send")) (Val #m))
  {{ RET #(); own_net nt Φ nd me }}

/-- `nt.recv(tmo)`: a message to `me` (which meets `Φ`), or a timeout. -/
abbrev tcpNetwork.recv.spec : Prop :=
  ∀ (Φ : message → IProp GF) (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64)
    (me : w64) (tmo : w64),
  me ∈ ids →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Φ amap ids ∗ own_net nt Φ nd me }}
    (App (Val (nt @!! go.GoType.PointerType tcpNetwork.ty @!! go!"recv")) (Val #tmo))
  {{ (m : message) (ok : Bool), RET (PairV #m #ok); own_net nt Φ nd me ∗
      if ok then inboxP Φ me m else True }}

/-- `nt.poll()`: a waiting message to `me` (which meets `Φ`), or none. -/
abbrev tcpNetwork.poll.spec : Prop :=
  ∀ (Φ : message → IProp GF) (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64)
    (me : w64),
  me ∈ ids →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd Φ amap ids ∗ own_net nt Φ nd me }}
    (App (Val (nt @!! go.GoType.PointerType tcpNetwork.ty @!! go!"poll")) (Val #()))
  {{ (m : message) (ok : Bool), RET (PairV #m #ok); own_net nt Φ nd me ∗
      if ok then inboxP Φ me m else True }}

end specs

end github_com.xiang90.paxos

end Perennial
