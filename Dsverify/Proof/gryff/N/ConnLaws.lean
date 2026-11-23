/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/ConnLaws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the connections of `ConnectToPeers` / `waitForPeerConnections` (ghost laws)

* the handshake's bits (`PeerHandshake = peerMark`): `and_peerMark_zero`, `peer_split`,
  `or_peerMark_inj`;
* `portId` of a replica's port is persistent and unique (`portId_node` + `nodeIdIs_agree`);
* what the acceptor learns from a handshake it read (`acc_peer_ids`, `acc_client_conn`) and the
  bridges of the accepted connection's reader and writer (`acc_peer_reader`, `acc_peer_writer`,
  `acc_client_reader`, `acc_client_writer`);
* the dialer's reader bridge (`dial_reader`): what the acceptor `q` writes after the dialer's
  handshake is `q`'s stream to the dialer.

Port (`Net/`): connection ids are `Nat`; a replica port `a`'s protocols are Gryff's wire
protocols `gryffWireP γ a`/`gryffWireQ γ a` themselves (the lab went through the hub's
`addrP`/`addrQ`; here the start sets them for the wildcard listener of `a`, `lisProto`). The
reader's state is `recvTokL` (`net.conn_readerOk`), whose protocol fact is under a later: the laws
are stated of the protocol fact (`acc_dial` from `protoPrefix`), and the reader-level bridges
(`acc_peer_reader`, `acc_client_reader`, `dial_reader`) take it from the reader
(`wire.ownReader_proto`) and strip the later under the update (the wire protocols are timeless:
`gryffWireP_timeless`, ...). The acceptor learns the dialer's handshake was written from the
reader too (`ownReader_sentLb`).
-/
module

public import Dsverify.Proof.gryff.N.Handshake
public import Dsverify.Proof.gryff.N.PeerMark
public import Dsverify.Proof.gryff.Client.Bufio

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The handshake's bits -/

theorem peerMark_twoPow : peerMark = BitVec.twoPow 32 31 := by decide

theorem bit31_iff (hs : w32) : hs.getLsbD 31 = true ↔ 2 ^ 31 ≤ hs.toNat := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have := hs.isLt
  simp only [decide_eq_true_eq]
  omega

/-- `hs & PeerHandshake == 0` iff the handshake is a client's. -/
theorem and_peerMark_zero (hs : w32) : hs &&& peerMark = 0 ↔ hs < peerMark := by
  rw [peerMark_twoPow, BitVec.and_twoPow, BitVec.lt_def, BitVec.toNat_twoPow]
  have h := bit31_iff hs
  by_cases hb : hs.getLsbD 31 = true
  · simp only [hb, ↓reduceIte]
    constructor
    · intro h0; exact absurd h0 (by decide)
    · intro hl; have := h.1 hb; simp at hl; omega
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have : ¬ 2 ^ 31 ≤ hs.toNat := fun h' => hb (h.2 h')
    simp; omega

/-- The id of a peer's handshake (`hs &^ PeerHandshake`). -/
theorem peer_split (hs : w32) (h : ¬ hs < peerMark) :
    (hs &&& ~~~peerMark) < peerMark ∧ (hs &&& ~~~peerMark) ||| peerMark = hs := by
  have hb : hs.getLsbD 31 = true := (bit31_iff hs).2 (by
    rw [BitVec.lt_def] at h; unfold peerMark at h; simp at h; omega)
  constructor
  · rw [← and_peerMark_zero, peerMark_twoPow, BitVec.and_twoPow]
    simp
  · rw [peerMark_twoPow]
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_twoPow]
    by_cases h31 : i = 31
    · subst h31; simp; exact hb
    · simp [h31]

theorem or_peerMark_inj (x y : w32) (hx : x < peerMark) (hy : y < peerMark)
    (h : x ||| peerMark = y ||| peerMark) : x = y := by
  have hx' := (and_peerMark_zero x).2 hx
  have hy' := (and_peerMark_zero y).2 hy
  rw [peerMark_twoPow] at hx' hy' h
  ext i hi
  have h1 := congrArg (fun z => z[i]) h
  simp only [BitVec.getElem_or, BitVec.getElem_twoPow] at h1
  by_cases h31 : i = 31
  · subst h31
    have a := congrArg (fun z => z[31]) hx'
    have b := congrArg (fun z => z[31]) hy'
    simp [BitVec.getElem_and] at a b
    rw [a, b]
  · simpa [h31] using h1

theorem u32Le_prefix {hs hs' : w32} {Y body : List w8}
    (h : u32Le hs ++ Y <+: u32Le hs' ++ body) : hs = hs' ∧ Y <+: body := by
  have h1 : u32Le hs = u32Le hs' := by
    have ha : u32Le hs <+: u32Le hs' ++ body := (List.prefix_append _ _).trans h
    have hb : u32Le hs' <+: u32Le hs' ++ body := List.prefix_append _ _
    exact (List.prefix_of_prefix_length_le ha hb (by simp [u32Le_length])).eq_of_length
      (by simp [u32Le_length])
  refine ⟨u32Le_inj h1, ?_⟩
  rw [h1] at h
  exact List.prefix_append_right_inj _ |>.1 h

theorem u32Le_ne_nil (hs : w32) (Y : List w8) : u32Le hs ++ Y ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [u32Le_length] at this

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions]

/-! ## `portId`, `peerRole` -/

instance clientReplyOk_pers (γ : GryffNames GF) (cid : w32) (m : List w8) :
    Persistent (clientReplyOk γ cid m) := by
  unfold clientReplyOk; infer_instance

theorem replicaAddrs_idx {a : GoString} (ha : a ∈ replicaAddrs) :
    ∃ j, j < 3 ∧ portAddr j = a := by
  simp only [replicaAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩

/-- A replica port's id is persistent (it is its node's registered id). -/
theorem portId_pers (γ : GryffNames GF) (a : GoString) (id : w32) (ha : a ∈ replicaAddrs) :
    portId γ a id ⊢ □ portId γ a id := by
  obtain ⟨j, hj, rfl⟩ := replicaAddrs_idx ha
  iintro H
  ihave #H' := (portId_node γ j id hj).1 $$ H
  imodintro
  iapply (portId_node γ j id hj).2 $$ H'

/-- A replica port has one id. -/
theorem portId_agree (γ : GryffNames GF) (a : GoString) (i j : w32) (ha : a ∈ replicaAddrs) :
    portId γ a i ∗ portId γ a j ⊢ ⌜i = j⌝ := by
  obtain ⟨n, hn, rfl⟩ := replicaAddrs_idx ha
  iintro ⟨Hi, Hj⟩
  ihave Hi := (portId_node γ n i hn).1 $$ Hi
  ihave Hj := (portId_node γ n j hn).1 $$ Hj
  ihave %h := nodeIdIs_agree γ.proto n (W64 (uint.Z i)) (W64 (uint.Z j)) $$ [$Hi $Hj]
  ipureintro
  apply BitVec.eq_of_toNat_eq
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt] at h2
  have := i.isLt; have := j.isLt
  simp only [uint.Z] at h2
  omega

/-- **Hub request N1-1**: the registry's `peerRole` is persistent. -/
theorem peerRole_pers (γ : GryffNames GF) (a : GoString) (id : w32) :
    peerRole γ a id ⊢ □ peerRole γ a id := by
  iintro #H; iexact H

/-! ## The wire protocols are timeless -/

instance portId_timeless (γ : GryffNames GF) (a : GoString) (id : w32) :
    Timeless (portId γ a id) := by
  unfold portId nodeIdIs; infer_instance

instance peerRole_timeless (γ : GryffNames GF) (a : GoString) (id : w32) :
    Timeless (peerRole γ a id) := by
  unfold peerRole; infer_instance

instance clientConnAt_timeless (γ : GryffNames GF) (hs : w32) (cid : Nat) :
    Timeless (clientConnAt γ hs cid) := by
  unfold clientConnAt; infer_instance

instance peerStreamOk_timeless (γ : ProtoNames) (k q : Fin 3) (W : List w8) :
    Timeless (peerStreamOk (GF := GF) γ k q W) := by
  unfold peerStreamOk predIdIs traceLb; infer_instance

instance clientReqsOk_timeless (γ : GryffNames GF) (hs : w32) (last : Int) (body : List w8) :
    Timeless (clientReqsOk γ hs last body) := by
  unfold clientReqsOk clientReqsBody opReg; infer_instance

instance clientReplyOk_timeless (γ : GryffNames GF) (hs : w32) (m : List w8) :
    Timeless (clientReplyOk γ hs m) := by
  unfold clientReplyOk clientReplyBody opDone histLb; infer_instance

instance dialStream_timeless (γ : GryffNames GF) (a : GoString) (cid : Nat) (full : List w8) :
    Timeless (dialStream γ a cid full) := by
  unfold dialStream; infer_instance

instance gryffWireP_timeless (γ : GryffNames GF) (a : GoString) (cid : Nat) (W : List w8) :
    Timeless (gryffWireP γ a cid W) := by
  unfold gryffWireP; infer_instance

instance sentLb_timeless (cn : Nat) (s : Bool) (W : List w8) :
    Timeless (sentLb (Gg := hG.goose_globalGS) cn s W) := by
  unfold sentLb connElem wLb; infer_instance

instance gryffWireQ_timeless (γ : GryffNames GF) (a : GoString) (cid : Nat) (W : List w8) :
    Timeless (gryffWireQ γ a cid W) := by
  unfold gryffWireQ acceptStream msgsOk; infer_instance

instance protoPrefix_timeless (P : Proto GF) [hP : ∀ cn W, Timeless (P cn W)] (cn : Nat)
    (W : List w8) : Timeless (protoPrefix P cn W) := by
  unfold protoPrefix; infer_instance

/-! ## The connection's tokens -/

/-- What a reader has read was written (`recvTokL`'s core). -/
theorem recvTokL_sentLb (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTokL (Gg := hG.goose_globalGS) cn s P R ⊢
      recvTokL (Gg := hG.goose_globalGS) cn s P R ∗ sentLb (Gg := hG.goose_globalGS) cn (!s) R := by
  refine persistent_entails_left ?_
  unfold recvTokL recvCore sentLb connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, -⟩, -, -, #Hlb⟩, -⟩
  iexists γ
  iframe He Hlb

theorem sentLb_le (cn : Nat) (s : Bool) {W W' : List w8} (h : W' <+: W) :
    sentLb (Gg := hG.goose_globalGS) cn s W ⊢ sentLb (Gg := hG.goose_globalGS) cn s W' := by
  unfold sentLb
  iintro ⟨%γ, #He, #Hlb⟩
  iexists γ
  iframe He
  iapply wLb_le _ W' h $$ Hlb

/-- Two lower bounds of one direction are comparable (the lab's `bufio.sentLb_comparable`). -/
theorem sentLb_comparable (cn : Nat) (s : Bool) (W1 W2 : List w8) :
    sentLb (Gg := hG.goose_globalGS) cn s W1 ∗ sentLb (Gg := hG.goose_globalGS) cn s W2 ⊢
      ⌜W1 <+: W2 ∨ W2 <+: W1⌝ := by
  unfold sentLb wLb
  iintro ⟨⟨%γ1, #He1, #H1⟩, ⟨%γ2, #He2, #H2⟩⟩
  icases connElem_agree cn γ1 γ2 $$ He1 He2 with %h
  subst h
  iapply mono_list_lb_valid $$ H1 H2

/-- What a connection's buffered reader has returned was written by the other end. -/
theorem ownReader_sentLb (br : Loc) (rd : wire.RSt GF) (cn : Nat) (s : Bool) (P : Proto GF)
    (R : List w8) :
    wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) cn s P) R ⊢
      wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) cn s P) R ∗
        sentLb (Gg := hG.goose_globalGS) cn (!s) R := by
  unfold wire.ownReader
  exact EtcdGrove.bufio.ownBufReader_fact br rd.ri _ _ rd.E R
    (fun r => sentLb (Gg := hG.goose_globalGS) cn (!s) r)
    (fun r => recvTokL_sentLb cn s P r)
    (fun x y => sentLb_le cn (!s) (List.prefix_append x y))

/-- A reader's protocol fact, now (the wire protocols are timeless). -/
theorem ownReader_protoNow (br : Loc) (rd : wire.RSt GF) (cn : Nat) (s : Bool) (P : Proto GF)
    [∀ cn W, Timeless (P cn W)] (R : List w8) (E : CoPset) :
    wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) cn s P) R ⊢ |={E}=>
      wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) cn s P) R ∗ protoPrefix P cn R := by
  iintro Hr
  ihave ⟨Hr, Hp⟩ := wire.ownReader_proto br rd cn s P R $$ Hr
  imod Hp
  imodintro
  iframe Hr Hp

/-! ## The acceptor's side -/

/-- What a dialer of a replica port has written, from its protocol fact at the acceptor: the
handshake `hs` and a body, a prefix of the dialer's stream. -/
theorem acc_dial (γ : GryffNames GF) (a : GoString) (c : Nat) (hs : w32) (Y : List w8) :
    protoPrefix (gryffWireP γ a) c (u32Le hs ++ Y) ⊢
      ∃ body, ⌜Y <+: body⌝ ∗
        ((∃ (id dst : w32), ⌜hs = id ||| peerMark ∧ id < peerMark⌝ ∗ □ peerRole γ a id ∗
            □ portId γ a dst ∗ peerStreamOk γ.proto (rid3 id) (rid3 dst) body) ∨
         (⌜hs < peerMark⌝ ∗ clientConnAt γ hs c ∗ ∃ last, clientReqsOk γ hs last body)) := by
  iintro #Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exact absurd Hnil (u32Le_ne_nil hs Y)
  unfold gryffWireP
  icases HP with (%Hn | ⟨%full, %Hfull, #Hd⟩)
  · subst Hn; exact absurd (List.prefix_nil.mp Hext) (u32Le_ne_nil hs Y)
  unfold dialStream
  icases Hd with ⟨%hs', %body, %Hf, #Hcase⟩
  subst Hf
  obtain ⟨rfl, hY⟩ := u32Le_prefix (Hext.trans Hfull)
  iexists body
  isplitr
  · ipureintro; exact hY
  icases Hcase with (⟨%id, %dst, %Hid, #Hrole, #Hport, #Hps⟩ | ⟨%Hlt, #Hcc, %last, #Hreqs⟩)
  · ileft
    iexists id, dst
    isplitr
    · ipureintro; exact Hid
    iframe Hrole Hport Hps
  · iright
    isplitr
    · ipureintro; exact Hlt
    iframe Hcc
    iexists last
    iexact Hreqs

/-- A peer's handshake read by the acceptor `k` (port `a`): the peer's id is above `k`, below 3. -/
theorem acc_peer_ids (γ : GryffNames GF) (a : GoString) (ha : a ∈ replicaAddrs) (c : Nat)
    (hs : w32) (k : Fin 3) (hp : ¬ hs < peerMark) :
    protoPrefix (gryffWireP γ a) c (u32Le hs) ∗ □ portId γ a (W32 (k.val : Int)) ⊢
      ⌜k.val < (hs &&& ~~~peerMark).toNat ∧ (hs &&& ~~~peerMark).toNat < 3⌝ := by
  iintro ⟨#HI, #Hk⟩
  rw [show u32Le hs = u32Le hs ++ [] by simp]
  ihave ⟨%body, -, Hcase⟩ := acc_dial γ a c hs [] $$ HI
  icases Hcase with (⟨%id, %dst, %Hid, #Hrole, #Hport, -⟩ | ⟨%Hlt, -⟩)
  · ihave %Hids := peerRole_ids γ a id dst $$ [$Hrole $Hport]
    ihave %Hd := portId_agree γ a dst (W32 (k.val : Int)) ha $$ [$Hport $Hk]
    subst Hd
    obtain ⟨h1, h2⟩ := peer_split hs hp
    obtain ⟨rfl, hid⟩ := Hid
    have heq := or_peerMark_inj _ _ h1 hid h2
    rw [heq]
    ipureintro
    have hk := k.isLt
    simp only [uint.Z, BitVec.toNat_ofInt] at Hids
    constructor <;> omega
  · exact absurd Hlt hp

/-- A client's handshake read by the acceptor: the client id is bound to the connection. -/
theorem acc_client_conn (γ : GryffNames GF) (a : GoString) (c : Nat) (hs : w32)
    (hc : hs < peerMark) :
    protoPrefix (gryffWireP γ a) c (u32Le hs) ⊢ clientConnAt γ hs c := by
  iintro #HI
  rw [show u32Le hs = u32Le hs ++ [] by simp]
  ihave ⟨%body, -, Hcase⟩ := acc_dial γ a c hs [] $$ HI
  icases Hcase with (⟨%id, %dst, %Hid, -⟩ | ⟨-, #Hcc, -⟩)
  · exfalso; rw [Hid.1] at hc; exact peerMark_or_ge_n id hc
  · iexact Hcc

/-- The accepted peer connection's reader bridge (peer `q`, acceptor `k` on port `a`; the reader
`peerReaderB`'s peek). -/
theorem acc_peer_reader (γ : GryffNames GF) (a : GoString) (ha : a ∈ replicaAddrs) (c : Nat)
    (k q : Fin 3) (br : Loc) (rd : wire.RSt GF) :
    □ portId γ a (W32 (k.val : Int)) ⊢
      □ (∀ Y, ⌜Y ≠ []⌝ -∗
        wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a))
          (u32Le (peerHs q) ++ Y) ={⊤}=∗
        wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a))
          (u32Le (peerHs q) ++ Y) ∗
        ∃ W, peerStreamOk γ.proto q k W ∗ ⌜Y <+: W⌝) := by
  iintro #Hk
  imodintro
  iintro %Y %_ Hr
  imod ownReader_protoNow br rd c true (gryffWireP γ a) _ ⊤ $$ Hr with ⟨Hr, #HI⟩
  iframe Hr
  ihave ⟨%body, %HY, Hcase⟩ := acc_dial γ a c (peerHs q) Y $$ HI
  icases Hcase with (⟨%id, %dst, %Hid, -, #Hport, #Hps⟩ | ⟨%Hlt, -⟩)
  · ihave %Hd := portId_agree γ a dst (W32 (k.val : Int)) ha $$ [$Hport $Hk]
    subst Hd
    have heq := or_peerMark_inj _ _ (W32_lt_peerMark q) Hid.2 Hid.1
    subst heq
    rw [rid3_W32, rid3_W32] at *
    imodintro
    iexists body
    iframe Hps
    ipureintro; exact HY
  · exfalso; exact peerMark_or_ge_n _ Hlt

/-- The accepted peer connection's writer bridge (acceptor `k` on port `a`, peer `q`). -/
theorem acc_peer_writer (γ : GryffNames GF) (a : GoString) (ha : a ∈ replicaAddrs) (c : Nat)
    (k q : Fin 3) :
    □ portId γ a (W32 (k.val : Int)) ∗
      sentLb (Gg := hG.goose_globalGS) c false (u32Le (peerHs q)) ⊢
      □ (∀ X, peerStreamOk γ.proto k q X -∗ □ gryffWireQ γ a c ([] ++ X)) := by
  iintro ⟨#Hk, #Hlb⟩
  imodintro
  iintro %X #Hps
  imodintro
  rw [List.nil_append]
  unfold gryffWireQ
  iright
  iexists X
  isplitr
  · ipureintro; exact List.prefix_refl _
  imodintro
  unfold acceptStream
  iexists peerHs q
  iframe Hlb
  ileft
  iexists W32 (q.val : Int), W32 (k.val : Int)
  isplitr
  · ipureintro; exact ⟨rfl, W32_lt_peerMark q⟩
  iframe Hk
  rw [rid3_W32, rid3_W32]
  iexact Hps

/-- The accepted client connection's reader bridge (`clientConnIn`'s peek). -/
theorem acc_client_reader (γ : GryffNames GF) (a : GoString) (c : Nat) (hs : w32)
    (hc : hs < peerMark) (br : Loc) (rd : wire.RSt GF) :
    ⊢ □ (∀ Y, wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a))
          (u32Le hs ++ Y) ={⊤}=∗
        wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) c true (gryffWireP γ a))
          (u32Le hs ++ Y) ∗
        ∃ (last : Int) (body : List w8), clientReqsOk γ hs last body ∗ ⌜Y <+: body⌝) := by
  iintro !> %Y Hr
  imod ownReader_protoNow br rd c true (gryffWireP γ a) _ ⊤ $$ Hr with ⟨Hr, #HI⟩
  iframe Hr
  ihave ⟨%body, %HY, Hcase⟩ := acc_dial γ a c hs Y $$ HI
  icases Hcase with (⟨%id, %dst, %Hid, -⟩ | ⟨-, -, %last, #Hr⟩)
  · exfalso; rw [Hid.1] at hc; exact peerMark_or_ge_n id hc
  · imodintro
    iexists last, body
    iframe Hr
    ipureintro; exact HY

/-- The accepted client connection's writer bridge (`clientConnIn`'s). -/
theorem acc_client_writer (γ : GryffNames GF) (a : GoString) (c : Nat) (hs : w32)
    (hc : hs < peerMark) :
    sentLb (Gg := hG.goose_globalGS) c false (u32Le hs) ⊢
      □ (∀ Y, msgsOk (clientReplyOk γ hs) Y -∗ gryffWireQ γ a c Y) := by
  iintro #Hlb
  imodintro
  iintro %Y HY
  unfold msgsOk
  icases HY with ⟨%ms, %Hms, #Hall⟩
  unfold gryffWireQ
  iright
  iexists Y
  isplitr
  · ipureintro; exact List.prefix_refl _
  imodintro
  unfold acceptStream
  iexists hs
  iframe Hlb
  iright
  isplitr
  · ipureintro; exact hc
  unfold msgsOk
  iexists ms
  iframe Hall
  ipureintro; exact Hms

/-- A replica port's protocols are prefix-closed (with the empty stream). -/
theorem gryffWireP_closed (γ : GryffNames GF) (a : GoString) :
    ProtoPrefixClosed (gryffWireP γ a) where
  nil cn := by
    iintro !>
    unfold gryffWireP
    ileft; ipureintro; rfl
  pre cn x y h := by
    unfold gryffWireP
    iintro #H
    iintro !>
    icases H with (%Hn | ⟨%full, %Hf, #Hs⟩)
    · ileft; ipureintro; subst Hn; exact List.prefix_nil.mp h
    iright
    iexists full
    iframe Hs
    ipureintro; exact h.trans Hf

theorem gryffWireQ_closed (γ : GryffNames GF) (a : GoString) :
    ProtoPrefixClosed (gryffWireQ γ a) where
  nil cn := by
    iintro !>
    unfold gryffWireQ
    ileft; ipureintro; rfl
  pre cn x y h := by
    unfold gryffWireQ
    iintro #H
    iintro !>
    icases H with (%Hn | ⟨%full, %Hf, #Hs⟩)
    · ileft; ipureintro; subst Hn; exact List.prefix_nil.mp h
    iright
    iexists full
    iframe Hs
    ipureintro; exact h.trans Hf

/-! ## The dialer's side -/

/-- The dialer `k`'s reader bridge on its connection to `q`'s port `a` (its handshake sent):
what `q` writes is `q`'s stream to `k`. -/
theorem dial_reader (γ : GryffNames GF) (a : GoString) (ha : a ∈ replicaAddrs) (c : Nat)
    (k q : Fin 3) (br : Loc) (rd : wire.RSt GF) :
    □ portId γ a (W32 (q.val : Int)) ∗
      sentLb (Gg := hG.goose_globalGS) c false (u32Le (peerHs k)) ⊢
      □ (∀ Y, ⌜Y ≠ []⌝ -∗
        wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) c false (gryffWireQ γ a))
          ([] ++ Y) ={⊤}=∗
        wire.ownReader br rd (recvTokL (Gg := hG.goose_globalGS) c false (gryffWireQ γ a))
          ([] ++ Y) ∗
        ∃ W, peerStreamOk γ.proto q k W ∗ ⌜Y <+: W⌝) := by
  iintro ⟨#Hq, #Hlb⟩
  imodintro
  iintro %Y %HY Hr
  imod ownReader_protoNow br rd c false (gryffWireQ γ a) _ ⊤ $$ Hr with ⟨Hr, #Hp⟩
  iframe Hr
  rw [List.nil_append] at *
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · exact absurd Hnil HY
  unfold gryffWireQ
  icases HQ with (%Hn | ⟨%full, %Hfull, #Hacc⟩)
  · subst Hn; exact absurd (List.prefix_nil.mp Hext) HY
  unfold acceptStream
  icases Hacc with ⟨%hs', #Hlb', Hcase⟩
  ihave %Hcmp := sentLb_comparable c false (u32Le (peerHs k)) (u32Le hs') $$ [Hlb Hlb']
  · iframe Hlb Hlb'
  have hhs' : peerHs k = hs' := by
    apply u32Le_inj
    exact prefix_same_len_n (by simp [u32Le_length]) Hcmp
  subst hhs'
  icases Hcase with (⟨%id, %dst, %Hid, #Hport, #Hps⟩ | ⟨%Hlt, -⟩)
  · ihave %Hd := portId_agree γ a dst (W32 (q.val : Int)) ha $$ [$Hport $Hq]
    subst Hd
    have heq := or_peerMark_inj _ _ (W32_lt_peerMark k) Hid.2 Hid.1
    subst heq
    rw [rid3_W32, rid3_W32]
    imodintro
    iexists full
    iframe Hps
    ipureintro; exact Hext.trans Hfull
  · exfalso; exact peerMark_or_ge_n _ Hlt

end

end Perennial.gryff.netN
