/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/WriterSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's writing side (internal statements, the replica group's).

* `sp.marshalOk msg m P`: the `fastrpc.Serializable` value `msg` (an interface) writes the body
  of the message `m` to any sink (`wire.sinkOk`), with its own resources `P` (taken and given
  back: a pooled message may be reused after it is sent). Persistent; the registrant of a
  message type (the swift package) proves it of its `Marshal`.
* `sp.wrSt_open`: opening a writer's state (`sp.wrSt`, Proof/replica/Defs.lean) to write one
  frame of a message of its kind with its witness: a sink at the frames so far `W`, the
  protocol fact for `W ++ m.frame`, and the closing wand taking the writer after `Flush` (no
  error: everything sent, `W ++ m.frame`) back to `wrSt`. With a sticky error nothing needs to
  hold (`wsink` is then vacuous): the write is a no-op and `wrSt`'s error arm holds.
* Triples: `BeaconReply.Marshal`, `ReplyBeacon` (in Specs.lean), `SendMsg`, `SendClientMsg`,
  `SendBeacon`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Sink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Marshal
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

namespace sp

/-- `msg.Marshal(wire)` writes `m.body` to the sink `wire` (see the file header). -/
def marshalOk (msg : GoInterface) (m : Msg) (P : IProp netDistGF) : IProp netDistGF :=
  iprop(∃ e : GoInterfaceOk, ⌜msg = interface.ok e⌝ ∗
    □ ∀ (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8)
      (Φ : val → IProp netDistGF),
      P -∗ sinkOk wr S Q -∗ S W -∗ bufio.prefixClosed Q -∗ □ Q (W ++ m.body) -∗
      ▷ (P -∗ S (W ++ m.body) -∗ Φ #()) -∗
      WP (App (Val #(methods e.ty go!"Marshal" e.v)) (Val #wr)) {{ Φ }})

instance marshalOk_persistent (msg : GoInterface) (m : Msg) (P : IProp netDistGF) :
    Persistent (marshalOk msg m P) := by
  unfold marshalOk; infer_instance

/-- (Change log C18) `msg.Marshal(wire)` writes the body of a message `m` with `Pm m`, chosen
at the write (an encoder iterating Go maps picks their order at run time): the sink's protocol
`Q` must hold after each candidate's body; the continuation gets the message written. -/
def marshalOkP (msg : GoInterface) (Pm : Msg → Prop) (P : IProp netDistGF) : IProp netDistGF :=
  iprop(∃ e : GoInterfaceOk, ⌜msg = interface.ok e⌝ ∗
    □ ∀ (wr : GoInterface) (S Q : List w8 → IProp netDistGF) (W : List w8)
      (Φ : val → IProp netDistGF),
      P -∗ sinkOk wr S Q -∗ S W -∗ bufio.prefixClosed Q -∗
      (□ ∀ m : Msg, ⌜Pm m⌝ -∗ □ Q (W ++ m.body)) -∗
      ▷ (∀ m : Msg, ⌜Pm m⌝ -∗ P -∗ S (W ++ m.body) -∗ Φ #()) -∗
      WP (App (Val #(methods e.ty go!"Marshal" e.v)) (Val #wr)) {{ Φ }})

instance marshalOkP_persistent (msg : GoInterface) (Pm : Msg → Prop) (P : IProp netDistGF) :
    Persistent (marshalOkP msg Pm P) := by
  unfold marshalOkP; infer_instance

/-- The candidates' protocol facts (`msgOk` of each message `Pm` allows). -/
def msgsOk (γ : Names) (γc γm : GName) (Pm : Msg → Prop) : IProp netDistGF :=
  iprop(□ ∀ m : Msg, ⌜Pm m⌝ -∗ msgOk γ γc γm m)

instance msgsOk_persistent (γ : Names) (γc γm : GName) (Pm : Msg → Prop) :
    Persistent (msgsOk γ γc γm Pm) := by
  unfold msgsOk; infer_instance

end sp

end defs

section laws
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

namespace sp

theorem framesOf_snoc' (ms : List Msg) (m : Msg) :
    framesOf (ms ++ [m]) = framesOf ms ++ m.frame := by
  simp [framesOf]

/-- The protocol of a writer's kind holds of whole frames of its messages. -/
theorem wrAt_proto (γ : Names) (γc γm : GName) (k : WrKind) (cid : Nat) (ms : List Msg)
    (hms : ∀ m ∈ ms, k.ok m ∧ m.wf) :
    connKind γ cid k.conn ∗ ([∗list] m ∈ ms, msgOk γ γc γm m) ⊢
      k.proto γ γc γm cid (k.head ++ framesOf ms) := by
  iintro ⟨#Hk, Hms⟩
  have hf : ∀ (head : List w8) (ok : Msg → Prop), (∀ m ∈ ms, ok m) →
      ([∗list] m ∈ ms, msgOk γ γc γm m) ⊢ framesProto γ γc γm head ok (head ++ framesOf ms) := by
    intro head ok hok
    iintro Hms
    unfold framesProto
    iexists ms
    iframe Hms
    ipureintro
    exact ⟨List.prefix_refl _, fun m hm => ⟨hok m hm, (hms m hm).2⟩⟩
  cases k with
  | peerOut me =>
    simp only [WrKind.proto, WrKind.conn, WrKind.head]
    iapply inP_peer cid me
    iframe Hk
    iapply hf (helloBytes me) Msg.isPeer (by simpa [WrKind.ok] using fun m hm => (hms m hm).1) $$ Hms
  | peerIn =>
    simp only [WrKind.proto, WrKind.conn, WrKind.head, List.nil_append]
    iapply outQ_peer cid
    iframe Hk
    rw [show framesOf ms = [] ++ framesOf ms from rfl]
    iapply hf [] Msg.isPeer (by simpa [WrKind.ok] using fun m hm => (hms m hm).1) $$ Hms
  | client cl =>
    simp only [WrKind.proto, WrKind.conn, WrKind.head, List.nil_append]
    iapply outQ_client cid cl
    iframe Hk
    rw [show framesOf ms = [] ++ framesOf ms from rfl]
    iapply hf [] (Msg.isToClient cl) (by simpa [WrKind.ok] using fun m hm => (hms m hm).1) $$ Hms

/-- Opening a writer's state to write one frame of a message chosen later (the frame's bytes
may be computed after its first byte is written: `SendBeacon`'s timestamp). -/
theorem wrSt_open_gen (γ : Names) (γc γm : GName) (w : Loc) (k : WrKind) :
    wrSt γ γc γm w k ⊢
      ∃ (cv : GoInterface) (cid : Nat) (W : List w8),
        bufio.writerOk cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid) ∗
        wsink w cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid) W ∗
        (□ ∀ m : Msg, ⌜k.ok m ∧ m.wf⌝ -∗ msgOk γ γc γm m -∗ □ k.proto γ γc γm cid (W ++ m.frame)) ∗
        (∀ (m : Msg) (sent pend : List w8) (err : GoInterface), ⌜k.ok m ∧ m.wf⌝ -∗
          msgOk γ γc γm m -∗
          bufio.ownWriter w cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid)
            sent pend err -∗ ⌜err = interface.nil → sent = W ++ m.frame ∧ pend = []⌝ -∗
          wrSt γ γc γm w k) := by
  iintro Hw
  unfold wrSt
  icases Hw with ⟨%cv, %cid, %sent, %pend, %err, #Hc, #Hk, #Hwr, Hown, Hat⟩
  -- the frames so far: those of the state, or none after a sticky error
  ihave HMs : (∃ ms : List Msg, ⌜(err = interface.nil → sent ++ pend = k.head ++ framesOf ms) ∧
      ∀ x ∈ ms, k.ok x ∧ x.wf⌝ ∗ □ [∗list] x ∈ ms, msgOk γ γc γm x) $$ [Hat]
  · icases Hat with (%He | #Hat)
    · iexists []
      isplitr
      · ipureintro; exact ⟨fun h => absurd h He, by simp⟩
      imodintro; iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
    · unfold wrAt
      icases Hat with ⟨%ms, %H, #Hms⟩
      iexists ms
      iframe Hms
      ipureintro; exact ⟨fun _ => H.1, H.2⟩
  icases HMs with ⟨%ms, %H, #Hms⟩
  iexists cv, cid, k.head ++ framesOf ms
  iframe Hwr
  isplitl [Hown]
  · unfold wsink
    iexists sent, pend, err
    iframe Hown
    ipureintro; exact H.1
  isplitr
  · imodintro
    iintro %m %hm #Hm
    imodintro
    rw [List.append_assoc, ← framesOf_snoc']
    have hall : ∀ x ∈ ms ++ [m], k.ok x ∧ x.wf := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact H.2 x h
      · simp at h; subst h; exact hm
    iapply wrAt_proto γ γc γm k cid (ms ++ [m]) hall
    iframe Hk
    iapply (BigSepL.bigSepL_snoc).2
    iframe Hms Hm
  iintro %m %sent' %pend' %err' %hm #Hm Hown %Hdone
  iexists cv, cid, sent', pend', err'
  iframe Hc Hk Hwr Hown
  by_cases he : err' = interface.nil
  · iright
    unfold wrAt
    iexists ms ++ [m]
    obtain ⟨h1, h2⟩ := Hdone he
    isplitr
    · ipureintro
      refine ⟨by rw [h1, h2, framesOf_snoc']; simp, ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact H.2 x h
      · simp at h; subst h; exact hm
    iapply (BigSepL.bigSepL_snoc).2
    iframe Hms Hm
  · ileft; ipureintro; exact he

/-- A fixed message is the one-candidate case. -/
theorem marshalOk_P (msg : GoInterface) (m : Msg) (P : IProp netDistGF) :
    marshalOk msg m P ⊢ marshalOkP msg (· = m) P := by
  iintro #Hm
  unfold marshalOk marshalOkP
  icases Hm with ⟨%e, %He, #HM⟩
  iexists e
  isplitr
  · ipureintro; exact He
  imodintro
  iintro %wr %S %Q %W %Φ HP #Hsk HS #Hpc #HQ HΦ
  iapply HM $$ HP Hsk HS Hpc
  · imodintro; iapply HQ $$ %m %rfl
  inext
  iintro HP HS
  iapply HΦ $$ %m %rfl HP HS

theorem msgsOk_eq (γ : Names) (γc γm : GName) (m : Msg) :
    □ msgOk γ γc γm m ⊢ msgsOk γ γc γm (· = m) := by
  iintro #Hm
  unfold msgsOk
  imodintro
  iintro %m' %He
  subst He
  iexact Hm

/-- Opening a writer's state to write one frame (see the file header). -/
theorem wrSt_open (γ : Names) (γc γm : GName) (w : Loc) (k : WrKind) (m : Msg)
    (hm : k.ok m ∧ m.wf) :
    wrSt γ γc γm w k ∗ msgOk γ γc γm m ⊢
      ∃ (cv : GoInterface) (cid : Nat) (W : List w8),
        bufio.writerOk cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid) ∗
        wsink w cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid) W ∗
        □ k.proto γ γc γm cid (W ++ m.frame) ∗
        (∀ (sent pend : List w8) (err : GoInterface),
          bufio.ownWriter w cv (sendTok cid k.side (k.proto γ γc γm)) (k.proto γ γc γm cid)
            sent pend err -∗ ⌜err = interface.nil → sent = W ++ m.frame ∧ pend = []⌝ -∗
          wrSt γ γc γm w k) := by
  iintro ⟨Hw, #Hm⟩
  icases wrSt_open_gen γ γc γm w k $$ Hw with ⟨%cv, %cid, %W, #Hwr, Hs, #HQ, Hclose⟩
  iexists cv, cid, W
  iframe Hwr Hs
  isplitr
  · iapply HQ $$ %m %hm Hm
  iintro %sent %pend %err Hown %Hd
  iapply Hclose $$ %m %sent %pend %err %hm Hm Hown %Hd

end sp

end laws

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- `r.SendMsg(peerId, code, msg)`: one frame of the peer message `m` (`msg` writes its body,
`code` its type) on peer `peerId`'s writer, under `r.M`; no writer: nothing. The message's own
resources `P` are given back. -/
abbrev replica.Replica.SendMsg.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (peerId : w32)
    (code : w8) (msg : GoInterface) (m : sp.Msg) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ sp.marshalOk msg m P ∗ P ∗ sp.msgOk γ γc γm m ∗
      ⌜m.isPeer ∧ m.wf ∧ code = m.code ∧ 0 ≤ peerId.toInt ∧ peerId.toInt < N⌝ }}
    (App (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"SendMsg"))
      (Val #peerId)) (Val #code)) (Val #msg))
  {{ RET #(); P }}

/-- `r.SendClientMsg(id, code, msg)`: one frame of the message `m` of client `id`'s commands
on client `id`'s registered writer, under `r.M`; none: nothing. -/
abbrev replica.Replica.SendClientMsg.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (id : w32)
    (code : w8) (msg : GoInterface) (m : sp.Msg) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ sp.marshalOk msg m P ∗ P ∗ sp.msgOk γ γc γm m ∗
      ⌜m.isToClient id ∧ m.wf ∧ code = m.code⌝ }}
    (App (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"SendClientMsg"))
      (Val #id)) (Val #code)) (Val #msg))
  {{ RET #(); P }}

/-- (C18) `SendMsg` of a message chosen at the write among `Pm` (all of code `code`). -/
abbrev replica.Replica.SendMsgP.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (peerId : w32)
    (code : w8) (msg : GoInterface) (Pm : sp.Msg → Prop) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ sp.marshalOkP msg Pm P ∗ P ∗ sp.msgsOk γ γc γm Pm ∗
      ⌜(∃ m, Pm m) ∧ (∀ m, Pm m → m.isPeer ∧ m.wf ∧ code = m.code) ∧ 0 ≤ peerId.toInt ∧
        peerId.toInt < N⌝ }}
    (App (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"SendMsg"))
      (Val #peerId)) (Val #code)) (Val #msg))
  {{ RET #(); P }}

/-- (C18) `SendClientMsg` of a message chosen at the write among `Pm`. -/
abbrev replica.Replica.SendClientMsgP.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (id : w32)
    (code : w8) (msg : GoInterface) (Pm : sp.Msg → Prop) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ sp.marshalOkP msg Pm P ∗ P ∗ sp.msgsOk γ γc γm Pm ∗
      ⌜(∃ m, Pm m) ∧ (∀ m, Pm m → m.isToClient id ∧ m.wf ∧ code = m.code)⌝ }}
    (App (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"SendClientMsg"))
      (Val #id)) (Val #code)) (Val #msg))
  {{ RET #(); P }}

/-- `r.SendBeacon(peerId)`: a beacon frame on peer `peerId`'s writer. -/
abbrev replica.Replica.SendBeacon.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (peerId : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ ⌜0 ≤ peerId.toInt ∧ peerId.toInt < N⌝ }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"SendBeacon")) (Val #peerId))
  {{ RET #(); True }}

/-- A peer message chosen at the write among `Pm` (`msg`, its type `rpc`), with its resources
`P`, to send (C18: `Pm` rather than one message). -/
def sp.peerSend (γ : sp.Names) (γc γm : GName) (msg : GoInterface) (Pm : sp.Msg → Prop) (rpc : w8)
    (P : IProp netDistGF) : IProp netDistGF :=
  iprop(sp.marshalOkP msg Pm P ∗ P ∗ sp.msgsOk γ γc γm Pm ∗
    ⌜(∃ m, Pm m) ∧ ∀ m, Pm m → m.isPeer ∧ m.wf ∧ rpc = m.code⌝)

/-- `sendToAll(r, msg, rpc)`: the frame to every alive peer. -/
abbrev replica.sendToAll.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (msg : GoInterface)
    (Pm : sp.Msg → Prop) (rpc : w8) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ sp.peerSend γ γc γm msg Pm rpc P }}
    (App (App (App (Val (@! replica.sendToAll)) (Val #r)) (Val #msg)) (Val #rpc))
  {{ RET #(); P }}

/-- `sendToAllExcept(r, except, msg, rpc)`: to every alive peer but `except`. -/
abbrev replica.sendToAllExcept.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (ex : w32)
    (msg : GoInterface) (Pm : sp.Msg → Prop) (rpc : w8) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ sp.peerSend γ γc γm msg Pm rpc P }}
    (App (App (App (App (Val (@! replica.sendToAllExcept)) (Val #r)) (Val #ex)) (Val #msg))
      (Val #rpc))
  {{ RET #(); P }}

/-- `sendToQuorum(r, q, msg, rpc)`: to every alive peer of the quorum `q`. -/
abbrev replica.sendToQuorum.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (q : Loc) (dq : DFrac)
    (s : List Nat) (msg : GoInterface) (Pm : sp.Msg → Prop) (rpc : w8) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ replica.quorum.qOwn q dq s ∗
      sp.peerSend γ γc γm msg Pm rpc P }}
    (App (App (App (App (Val (@! replica.sendToQuorum)) (Val #r)) (Val #q)) (Val #msg))
      (Val #rpc))
  {{ RET #(); replica.quorum.qOwn q dq s ∗ P }}

/-- `sendExcept(r, q, msg, rpc)`: to every alive peer outside the quorum `q`. -/
abbrev replica.sendExcept.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (q : Loc) (dq : DFrac)
    (s : List Nat) (msg : GoInterface) (Pm : sp.Msg → Prop) (rpc : w8) (P : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ replica.quorum.qOwn q dq s ∗
      sp.peerSend γ γc γm msg Pm rpc P }}
    (App (App (App (App (Val (@! replica.sendExcept)) (Val #r)) (Val #q)) (Val #msg))
      (Val #rpc))
  {{ RET #(); replica.quorum.qOwn q dq s ∗ P }}

instance replica.SendArg_countable [GooseExts] : Pos.Countable replica.SendArg :=
  countableOfLeftInverse (fun a : replica.SendArg => (a.msg', a.rpc', a.quorum', a.sendType', a.id', a.free'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

/-- A `free` closure: nil, or a call that takes the message's resources `P`. -/
def replica.freeOk (f : GoFunc) (P : IProp netDistGF) : IProp netDistGF :=
  iprop(⌜f = func.nil⌝ ∨
    □ ∀ Φ : val → IProp netDistGF, P -∗ ▷ Φ #() -∗ WP (App (Val #f) (Val #())) {{ Φ }})

instance replica.freeOk_persistent (f : GoFunc) (P : IProp netDistGF) :
    Persistent (replica.freeOk f P) := by
  unfold replica.freeOk; infer_instance

/-- What the sender's channel carries: a `SendArg` whose message (with its resources and its
`free`) fits its send type: a peer message to all peers, a quorum (owned), all but one, or one
peer below `N`; a client message of client `id`. (C18: the message is chosen at the write among
`Pm`.) -/
def replica.sendArgP (r : Loc) (γ : sp.Names) (γc γm : GName) (N : Nat) (a : replica.SendArg) :
    IProp netDistGF :=
  iprop((∃ (γw : GName) (me : w32), replica.isReplica r γ γc γm γw N me) ∗
    ∃ (Pm : sp.Msg → Prop) (P : IProp netDistGF),
    sp.marshalOkP a.msg' Pm P ∗ P ∗ sp.msgsOk γ γc γm Pm ∗ replica.freeOk a.free' P ∗
    ⌜(∃ m, Pm m) ∧ ∀ m, Pm m → m.wf ∧ a.rpc' = m.code⌝ ∗
    (⌜(a.sendType' = W32 0 ∨ a.sendType' = W32 5) ∧ ∀ m, Pm m → m.isPeer⌝ ∨
      (⌜(a.sendType' = W32 1 ∨ a.sendType' = W32 2) ∧ ∀ m, Pm m → m.isPeer⌝ ∗
        ∃ (dq : DFrac) (qs : List Nat), replica.quorum.qOwn a.quorum' dq qs) ∨
      ⌜a.sendType' = W32 3 ∧ (∀ m, Pm m → m.isPeer) ∧ 0 ≤ a.id'.toInt ∧ a.id'.toInt < N⌝ ∨
      ⌜a.sendType' = W32 4 ∧ ∀ m, Pm m → m.isToClient a.id'⌝))

/-- `NewSender(r)`: the sender's channel, whose goroutine sends what it carries. -/
abbrev replica.NewSender.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm : GName) (N : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.fld r go!"Shutdown" ↦□ false }}
    (App (Val (@! replica.NewSender)) (Val #r))
  {{ (s : Loc), RET #s; ∃ γs : ChanNames, isChanBag γs s (replica.sendArgP r γ γc γm N) }}

/-- The message `m` (`msg`, type `rpc`) with its resources `P` and its `free`, to hand to
the sender. -/
def replica.toSend (γ : sp.Names) (γc γm : GName) (msg : GoInterface) (m : sp.Msg) (rpc : w8)
    (P : IProp netDistGF) (f : GoFunc) : IProp netDistGF :=
  iprop(sp.marshalOk msg m P ∗ P ∗ sp.msgOk γ γc γm m ∗ replica.freeOk f P ∗
    ⌜m.wf ∧ rpc = m.code⌝)

/-- (C18) The message, chosen at the write among `Pm`, to hand to the sender. -/
def replica.toSendP (γ : sp.Names) (γc γm : GName) (msg : GoInterface) (Pm : sp.Msg → Prop)
    (rpc : w8) (P : IProp netDistGF) (f : GoFunc) : IProp netDistGF :=
  iprop(sp.marshalOkP msg Pm P ∗ P ∗ sp.msgsOk γ γc γm Pm ∗ replica.freeOk f P ∗
    ⌜(∃ m, Pm m) ∧ ∀ m, Pm m → m.wf ∧ rpc = m.code⌝)

theorem replica.toSend_P (γ : sp.Names) (γc γm : GName) (msg : GoInterface) (m : sp.Msg)
    (rpc : w8) (P : IProp netDistGF) (f : GoFunc) :
    replica.toSend γ γc γm msg m rpc P f ⊢ replica.toSendP γ γc γm msg (· = m) rpc P f := by
  unfold replica.toSend replica.toSendP
  iintro ⟨#Hmar, HP, #Hm, #Hf, %Hw⟩
  iframe HP Hf
  isplitr
  · iapply sp.marshalOk_P $$ Hmar
  isplitr
  · iapply sp.msgsOk_eq $$ Hm
  ipureintro
  exact ⟨⟨m, rfl⟩, fun m' h => h ▸ Hw⟩

/-- (C18) `s.SendToAllAndFree(...)` of a message chosen at the write among `Pm`. -/
abbrev replica.Sender.SendToAllAndFreeP.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (msg : GoInterface)
    (Pm : sp.Msg → Prop) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSendP γ γc γm msg Pm rpc P f ∗
      ⌜∀ m, Pm m → m.isPeer⌝ }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAllAndFree")) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendToAllAndFree(...)`: the message to the sender's channel. -/
abbrev replica.Sender.SendToAllAndFree.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P f ∗
      ⌜m.isPeer⌝ }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAllAndFree")) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendToAllExecptAndFree(...)`: the message to the sender's channel. -/
abbrev replica.Sender.SendToAllExecptAndFree.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (ex : w32) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P f ∗
      ⌜m.isPeer⌝ }}
    (App (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAllExecptAndFree")) (Val #ex)) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendToQuorumAndFree(...)`: the message to the sender's channel. -/
abbrev replica.Sender.SendToQuorumAndFree.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (q : Loc) (dq : DFrac) (qs : List Nat) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P f ∗
      ⌜m.isPeer⌝ ∗ replica.quorum.qOwn q dq qs }}
    (App (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToQuorumAndFree")) (Val #q)) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendExceptAndFree(...)`: the message to the sender's channel. -/
abbrev replica.Sender.SendExceptAndFree.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (q : Loc) (dq : DFrac) (qs : List Nat) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P f ∗
      ⌜m.isPeer⌝ ∗ replica.quorum.qOwn q dq qs }}
    (App (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendExceptAndFree")) (Val #q)) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendToClientAndFree(...)`: the message to the sender's channel. -/
abbrev replica.Sender.SendToClientAndFree.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (cid : w32) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P f ∗
      ⌜m.isToClient cid⌝ }}
    (App (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToClientAndFree")) (Val #cid)) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendToAndFree(...)`: the message to the sender's channel. -/
abbrev replica.Sender.SendToAndFree.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (id : w32) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF) (f : GoFunc),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P f ∗
      ⌜m.isPeer ∧ 0 ≤ id.toInt ∧ id.toInt < N⌝ }}
    (App (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAndFree")) (Val #id)) (Val #msg)) (Val #rpc)) (Val #f))
  {{ RET #(); True }}

/-- `s.SendToAll(...)`: as its `AndFree` form, with no `free`. -/
abbrev replica.Sender.SendToAll.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P func.nil ∗
      ⌜m.isPeer⌝ }}
    (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAll")) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

/-- (C18) `s.SendToAll(...)` of a message chosen at the write among `Pm`. -/
abbrev replica.Sender.SendToAllP.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (msg : GoInterface)
    (Pm : sp.Msg → Prop) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSendP γ γc γm msg Pm rpc P func.nil ∗
      ⌜∀ m, Pm m → m.isPeer⌝ }}
    (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAll")) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

/-- `s.SendToAllExecpt(...)`: as its `AndFree` form, with no `free`. -/
abbrev replica.Sender.SendToAllExecpt.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (ex : w32) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P func.nil ∗
      ⌜m.isPeer⌝ }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToAllExecpt")) (Val #ex)) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

/-- `s.SendToQuorum(...)`: as its `AndFree` form, with no `free`. -/
abbrev replica.Sender.SendToQuorum.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (q : Loc) (dq : DFrac) (qs : List Nat) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P func.nil ∗
      ⌜m.isPeer⌝ ∗ replica.quorum.qOwn q dq qs }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToQuorum")) (Val #q)) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

/-- `s.SendExcept(...)`: as its `AndFree` form, with no `free`. -/
abbrev replica.Sender.SendExcept.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (q : Loc) (dq : DFrac) (qs : List Nat) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P func.nil ∗
      ⌜m.isPeer⌝ ∗ replica.quorum.qOwn q dq qs }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendExcept")) (Val #q)) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

/-- `s.SendToClient(...)`: as its `AndFree` form, with no `free`. -/
abbrev replica.Sender.SendToClient.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (cid : w32) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P func.nil ∗
      ⌜m.isToClient cid⌝ }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendToClient")) (Val #cid)) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

/-- `s.SendTo(...)`: as its `AndFree` form, with no `free`. -/
abbrev replica.Sender.SendTo.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (γs : ChanNames) (s : Loc) (id : w32) (msg : GoInterface)
    (m : sp.Msg) (rpc : w8) (P : IProp netDistGF),
  {{ replica.isReplica r γ γc γm γw N me ∗ isChanBag γs s (replica.sendArgP r γ γc γm N) ∗ replica.toSend γ γc γm msg m rpc P func.nil ∗
      ⌜m.isPeer ∧ 0 ≤ id.toInt ∧ id.toInt < N⌝ }}
    (App (App (App (Val (s @!! replica.Sender.ty @!! go!"SendTo")) (Val #id)) (Val #msg)) (Val #rpc))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
