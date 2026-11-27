/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/WireLaws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The laws of the wire protocol's sealed slots that other units use (R10 of the interface review):
the client's requests and the replicas' replies as byte strings (`reqBytesOk`, `replyBytesOk`,
over the wire encodings), how a client extends its request stream, what a replica learns from a
request, what a reply's bytes give the client, client ids bound to connections, and the peers'
and ports' ids (the registry's).
-/
module

public import Dsverify.Proof.gryff.Proto.Wire
public import Dsverify.Proof.gryff.Proto.ClientLaws
public import Dsverify.Proof.gryff.Wire.Enc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net dsverify_lab.harness
open wire.gryffproto

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The client opcodes (`clientproto`'s iota). -/
def gryffRMW : w8 := W8 22
def gryffRMWReply : w8 := W8 23
def gryffRead : w8 := W8 24
def gryffReadReply : w8 := W8 25
def gryffWrite : w8 := W8 26
def gryffWriteReply : w8 := W8 27

/-- `m` is client `hs`'s request `req` for input `i`, as the adapter sends it (key 0, no
dependency: key -1). -/
def reqBytesOk [GooseExts] (hs req : w32) (i : RegInput w64) (m : List w8) : Prop :=
  match i with
  | .read => ∃ r : Read.Msg, m = gryffRead :: Read.enc r ∧ r.RequestId' = req ∧
      r.ClientId' = hs ∧ r.K' = W64 0 ∧ r.D'.Key' = W64 (-1)
  | .write v => ∃ r : Write.Msg, m = gryffWrite :: Write.enc r ∧ r.RequestId' = req ∧
      r.ClientId' = hs ∧ r.K' = W64 0 ∧ r.V' = v ∧ r.D'.Key' = W64 (-1)
  | .cas o n => ∃ r : RMW.Msg, m = gryffRMW :: RMW.enc r ∧ r.RequestId' = req ∧
      r.ClientId' = hs ∧ r.K' = W64 0 ∧ r.OldValue' = o ∧ r.NewValue' = n ∧
      r.D'.Key' = W64 (-1)

/-- `m` is a reply with `OK = 1` to client `hs`'s request `req`, with output `o`. -/
def replyBytesOk [GooseExts] (hs req : w32) (o : RegOutput w64) (m : List w8) : Prop :=
  (∃ (r : ReadReply.Msg) (v : w64), m = gryffReadReply :: ReadReply.enc r ∧ r.RequestId' = req ∧
    r.ClientId' = hs ∧ r.OK' = W8 1 ∧ r.V' = v ∧ o = .value v) ∨
  (∃ r : WriteReply.Msg, m = gryffWriteReply :: WriteReply.enc r ∧ r.RequestId' = req ∧
    r.ClientId' = hs ∧ r.OK' = W8 1 ∧ o = .done) ∨
  (∃ r : RMWReply.Msg, m = gryffRMWReply :: RMWReply.enc r ∧ r.RequestId' = req ∧
    r.OK' = W8 1 ∧ o = .done)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- `clientConnAt` is persistent (H-U3-3). -/
instance clientConnAt_persistent (γ : GryffNames GF) (hs : w32) (cid : Nat) :
    Persistent (clientConnAt γ hs cid) := by
  unfold clientConnAt; infer_instance

/-- `clientReqsOk` is persistent (H-U3-3). -/
instance clientReqsOk_persistent (γ : GryffNames GF) (hs : w32) (last : Int)
    (body : List w8) : Persistent (clientReqsOk γ hs last body) := by
  unfold clientReqsOk clientReqsBody
  have := fun (x : w32 × RegInput w64 × List w8) =>
    opReg_persistent (GF := GF) γ.proto (sint.Z hs, sint.Z x.1) x.2.1
  infer_instance

/-- A fresh client id is bound to the connection it opens. -/
theorem clientConnAt_intro (γ : GryffNames GF) (hs : w32) (cid : Nat) :
    □ protoInvs γ ∗ idTok γ hs ⊢ |={⊤}=> clientConnAt γ hs cid := by
  unfold protoInvs idTok clientConnAt
  iintro ⟨#⟨Hinv, -⟩, Htok⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact (fun x _ => CoPset.subseteq_top x ‹_›)
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Hconns
  ihave %hn := ghost_map_lookup $$ Hconns Htok
  imod ghost_map_update (some cid) $$ Hconns Htok with ⟨Hconns, Htok⟩
  imod ghostMapElem_persist $$ Htok with #Htok
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR Hcur Hrx Hreqs Hres] with -
  · inext
    iexists { S with conns := S.conns.insert hs (some cid) }
    iframe
    ipureintro; exact p2.facts_conn Hf hn
  imodintro
  iexact Htok

theorem clientConnAt_agree (γ : GryffNames GF) (hs : w32) (c1 c2 : Nat) :
    clientConnAt γ hs c1 ∗ clientConnAt γ hs c2 ⊢ ⌜c1 = c2⌝ := by
  unfold clientConnAt
  iintro ⟨H1, H2⟩
  ihave %h := ghostMapElem_agree $$ H1 H2
  ipureintro
  exact Option.some.inj h

theorem clientReqsOk_nil (γ : GryffNames GF) (hs : w32) (last : Int) :
    ⊢ clientReqsOk γ hs last [] := by
  unfold clientReqsOk clientReqsBody
  iexists []
  isplit
  · ipureintro; simp
  · iapply BigSepL.bigSepL_nil.2; iempintro

/-- A client appends a registered request with a greater id (the client's turn tokens, from
the client node's start resources for the ids it may use, order its requests). -/
theorem clientReqsOk_snoc (γ : GryffNames GF) (hs req : w32) (last : Int)
    (i : RegInput w64) (body m : List w8) (hlt : last < sint.Z req) (h0 : 0 ≤ sint.Z req)
    (hm : reqBytesOk hs req i m) :
    clientReqsOk γ hs last body ∗ opReg γ.proto (sint.Z hs, sint.Z req) i ⊢
      clientReqsOk γ hs (sint.Z req) (body ++ m) := by
  unfold clientReqsOk clientReqsBody
  iintro ⟨⟨%ms, %hms, Hms⟩, Hreg⟩
  obtain ⟨hb, hok, hsort, hle, hnn⟩ := hms
  iexists ms ++ [(req, i, m)]
  isplit
  · ipureintro
    refine ⟨by simp [hb], ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hok x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact hm
    · rw [List.map_append, List.pairwise_append]
      refine ⟨hsort, by simp, ?_⟩
      intro a ha b hb'
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      subst hb'
      exact Int.lt_of_le_of_lt (hle x hx) hlt
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Int.le_of_lt (Int.lt_of_le_of_lt (hle x hx) hlt)
      · simp only [List.mem_singleton] at hx; subst hx; exact Int.le_refl _
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hnn x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact h0
  · iapply BigSepL.bigSepL_snoc.2
    isplitl [Hms]
    · iexact Hms
    · iexact Hreg

/-- The shape of a client's request as a replica decodes it: an opcode, then the message's
encoding (`code` among the three request opcodes). -/
def reqShape (code : w8) (m : List w8) : Prop :=
  (code = gryffRead ∧ ∃ r : Read.Msg, m = code :: Read.enc r) ∨
  (code = gryffWrite ∧ ∃ r : Write.Msg, m = code :: Write.enc r) ∨
  (code = gryffRMW ∧ ∃ r : RMW.Msg, m = code :: RMW.enc r)

/-- A replica that read whole requests and then one more of a known shape learns that it is a
registered request of the connection's client: its fields (`reqBytesOk`: the client id, key 0,
no dependency, the input), its registration, and that its id is greater than every earlier one on
the stream. -/
theorem clientReqsOk_elim (γ : GryffNames GF) (hs : w32) (last : Int) (code : w8)
    (pre m post : List w8) (ms : List (List w8))
    (hpre : pre = ms.flatten ∧ ∀ x ∈ ms, ∃ c, reqShape c x) (hm : reqShape code m) :
    clientReqsOk γ hs last (pre ++ m ++ post) ⊢
      ∃ (req : w32) (i : RegInput w64), ⌜reqBytesOk hs req i m⌝ ∗
        opReg γ.proto (sint.Z hs, sint.Z req) i ∗
        ⌜∀ x ∈ ms, ∀ r j, reqBytesOk hs r j x → sint.Z r < sint.Z req⌝ ∗
        ⌜0 ≤ sint.Z req⌝ := by -- N-8
  unfold clientReqsOk clientReqsBody
  iintro ⟨%ms0, %hms, Hms⟩
  obtain ⟨hb, hok, hsort, -, hnn⟩ := hms
  obtain ⟨x, hx, hxm, hlt⟩ := reqs_elim_pure hs ms0 ms code m post
    (by rw [← hb, hpre.1]) hok hsort (fun y hy => hpre.2 y hy) hm
  have hxok := hok x (List.mem_of_getElem? hx)
  rw [hxm] at hxok
  iexists x.1, x.2.1
  isplit
  · ipureintro; exact hxok
  isplit
  · iapply (BigSepL.bigSepL_lookup (Φ := fun _ x => opReg γ.proto (sint.Z hs, sint.Z x.1) x.2.1) hx)
    iexact Hms
  isplit
  · ipureintro; exact hlt
  · ipureintro; exact hnn x (List.mem_of_getElem? hx)

/-- The right to place the requests of connection `cid` (exclusive; the acceptor's, minted once
from its fresh end), with the last request id it placed: the placers map's element (H-U4-8). -/
@[irreducible] def placeRight (γ : GryffNames GF) (cid : Nat) (last : Int) :
    IProp GF := ghostMapElem γ.proto.placers cid (DFrac.own 1) last

theorem placersN_sub_diff : (↑placersN : CoPset) ⊆ (⊤ : CoPset) \ ↑gryffN := by
  have hd : placersN ## gryffN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  rw [Iris.Std.mem_diff]
  exact ⟨CoPset.subseteq_top p hp, fun h => hd p ⟨hp, h⟩⟩

/-- `placeRight_intro` with the placed witness (unit WS: the placers' invariant keeps the fresh
token). -/
theorem placeRight_intro_core (γ : GryffNames GF) (cid : Nat) :
    □ protoInvs γ ∗ connFresh cid true ⊢
      |={⊤}=> (placeRight γ cid (-1) ∗ connPlaced γ cid) := by
  unfold protoInvs placeRight connPlaced
  iintro ⟨#⟨Hinv, HPinv⟩, Hfresh⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact (fun x _ => CoPset.subseteq_top x ‹_›)
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Hplacers
  iinv HPinv with Hp HPclose
  all_goals try exact placersN_sub_diff
  unfold placersInv
  icases Hp with ⟨%P, %D, >HPa, >HDa, >%hD, >HPm⟩
  ihave %hP := ghostMapAuth_agree (GF := GF) γ.proto.placers _ _ S.placers P $$ Hplacers HPa
  subst hP
  cases hcid : S.placers.lookup cid with
  | some n =>
    ihave Hold := (BigSepM.bigSepM_lookup (Φ := fun c (_ : Int) => connFresh (Gg := G) c true)
      (show get? S.placers cid = some n from hcid)) $$ HPm
    iexfalso
    iapply connFresh_excl cid true
    isplitl [Hold]
    · iexact Hold
    · iexact Hfresh
  | none =>
    have hDc : D.lookup cid = none := by
      have := hD cid; rw [hcid] at this; simpa using this
    imod ghost_map_insert cid () hDc $$ HDa with ⟨HDa, Hpl⟩
    imod ghostMapElem_persist $$ Hpl with #Hpl
    ihave Hfull := (ghostMapAuth_halves (GF := GF) γ.proto.placers S.placers).2
      $$ [Hplacers HPa]
    · isplitl [Hplacers]
      · iexact Hplacers
      · iexact HPa
    imod ghost_map_insert cid (-1 : Int) hcid $$ Hfull with ⟨Hfull, Hel⟩
    icases (ghostMapAuth_halves (GF := GF) γ.proto.placers (S.placers.insert cid (-1))).1
      $$ Hfull with ⟨Hplacers, HPa⟩
    imod HPclose $$ [HPa HDa HPm Hfresh] with -
    · inext
      iexists S.placers.insert cid (-1), D.insert cid ()
      iframe HPa HDa
      isplitr
      · ipureintro
        intro c
        by_cases hc : c = cid
        · subst hc; simp
        · simp [Ne.symm hc, hD c]
      iapply (BigSepM.bigSepM_insert (Φ := fun c (_ : Int) => connFresh (Gg := G) c true)
        (show get? S.placers cid = none from hcid)).2
      isplitl [Hfresh]
      · iexact Hfresh
      · iexact HPm
    imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR Hcur Hrx Hreqs Hres] with -
    · inext
      iexists { S with placers := S.placers.insert cid (-1) }
      iframe
      ipureintro; exact p2.facts_placer Hf hcid
    imodintro
    iframe Hel Hpl

theorem placeRight_intro (γ : GryffNames GF) (cid : Nat) :
    □ protoInvs γ ∗ connFresh cid true ⊢ |={⊤}=> placeRight γ cid (-1) := by
  iintro H
  imod placeRight_intro_core γ cid $$ H with ⟨Hr, -⟩
  iexact Hr

/-- **Unit I's slot** (N-4). Connection `cid` has been placed (`placeRight_intro_placed`;
persistent): the placers' invariant holds `cid`'s fresh acceptor token for good, so a second
acceptance of `cid` is refuted (`placedConn_fresh`). -/
@[irreducible] def placedConn (γ : GryffNames GF) (cid : Nat) : IProp GF :=
  iprop(inv placersN (placersInv γ) ∗ connPlaced γ cid)

instance placedConn_persistent (γ : GryffNames GF) (cid : Nat) :
    Persistent (placedConn γ cid) := by
  unfold placedConn connPlaced; infer_instance

/-- `placeRight_intro` with the persistent witness that `cid` is placed (N-4: `serveClient`
registers one writer per client id; a client id has one connection, accepted once). -/
theorem placeRight_intro_placed (γ : GryffNames GF) (cid : Nat) :
    □ protoInvs γ ∗ connFresh cid true ⊢
      |={⊤}=> (placeRight γ cid (-1) ∗ placedConn γ cid) := by
  unfold placedConn
  iintro ⟨#Hi, Hf⟩
  ihave #HP : inv placersN (placersInv γ) $$ [Hi]
  · unfold protoInvs
    icases Hi with ⟨-, HP⟩
    iexact HP
  imod placeRight_intro_core γ cid $$ [Hi Hf] with ⟨Hr, #Hpl⟩
  · iframe Hf; iexact Hi
  imodintro
  iframe Hr
  isplit
  · iexact HP
  · iexact Hpl

/-- A placed connection's fresh acceptor token is gone (N-4: `serveClient`'s second registration of
a client id is refuted). -/
theorem placedConn_fresh (γ : GryffNames GF) (cid : Nat) :
    placedConn γ cid ∗ connFresh cid true ⊢ |={⊤}=> False := by
  unfold placedConn connPlaced
  iintro ⟨⟨#HPinv, #Hpl⟩, Hfresh⟩
  iinv HPinv with Hp HPclose
  all_goals try exact (fun x _ => CoPset.subseteq_top x ‹_›)
  unfold placersInv
  icases Hp with ⟨%P, %D, >HPa, >HDa, >%hD, >HPm⟩
  ihave %hl := ghost_map_lookup $$ HDa Hpl
  have hP : (P.lookup cid).isSome := by rw [← hD cid, hl]; rfl
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hP
  ihave Hold := (BigSepM.bigSepM_lookup (Φ := fun c (_ : Int) => connFresh (Gg := G) c true)
    (show get? P cid = some n from hn)) $$ HPm
  iexfalso
  iapply connFresh_excl cid true
  isplitl [Hold]
  · iexact Hold
  · iexact Hfresh

/-- A replica sends a reply for a linearized operation. -/
theorem clientReplyOk_intro (γ : GryffNames GF) (hs req : w32) (o : RegOutput w64)
    (m : List w8) (hm : replyBytesOk hs req o m) :
    opDone γ.proto (sint.Z hs, sint.Z req) o ⊢ clientReplyOk γ hs m := by
  unfold clientReplyOk clientReplyBody
  iintro H
  iexists req, o
  isplit
  · ipureintro; exact hm
  · iexact H

/-- A client reading a reply with `OK = 1` to its request learns its output. -/
theorem clientReplyOk_elim (γ : GryffNames GF) (hs req : w32) (o : RegOutput w64)
    (m : List w8) (hm : replyBytesOk hs req o m) :
    clientReplyOk γ hs m ⊢ opDone γ.proto (sint.Z hs, sint.Z req) o := by
  unfold clientReplyOk clientReplyBody
  iintro ⟨%req', %o', %hm', H⟩
  obtain ⟨rfl, rfl⟩ := replyBytesD_unique hm hm'
  iexact H

/-- A replica's port's id is its node's registration id. -/
theorem portId_node (γ : GryffNames GF) (k : Nat) (id : w32) (hk : k < 3) :
    portId γ (portAddr k) id ⊣⊢ nodeIdIs γ.proto k (W64 (uint.Z id)) := by
  unfold portId
  constructor
  · iintro ⟨%k', %hk', H⟩
    obtain ⟨hlt, ha⟩ := hk'
    have hkk : k' = k := portAddr_inj hlt hk ha.symm
    subst hkk
    iexact H
  · iintro H
    iexists k
    iframe H
    ipureintro; exact ⟨hk, rfl⟩

/-- A peer dialing a port has a greater id than the port's replica, and is one of the three. -/
theorem peerRole_ids (γ : GryffNames GF) (a : GoString) (id dst : w32) :
    peerRole γ a id ∗ portId γ a dst ⊢ ⌜uint.Z dst < uint.Z id ∧ uint.Z id < 3⌝ := by
  unfold peerRole portId
  iintro ⟨⟨%d, ⟨%k1, %hk1, H1⟩, %hlt⟩, ⟨%k2, %hk2, H2⟩⟩
  obtain ⟨hk1, ha1⟩ := hk1
  obtain ⟨hk2, ha2⟩ := hk2
  have hkk : k1 = k2 := portAddr_inj hk1 hk2 (ha1.symm.trans ha2)
  subst hkk
  ihave %h := nodeIdIs_agree γ.proto k1 (W64 (uint.Z d)) (W64 (uint.Z dst)) $$ [$H1 $H2]
  ipureintro
  have hd : d = dst := by
    apply BitVec.eq_of_toNat_eq
    have h2 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofInt] at h2
    have := d.isLt; have := dst.isLt
    simp only [uint.Z] at h2
    omega
  subst hd
  exact hlt

/-- `peerRole` is persistent (N1-1; the registry's fact, as its documentation says). -/
instance peerRole_persistent (γ : GryffNames GF) (a : GoString) (id : w32) :
    Persistent (peerRole γ a id) := by
  unfold peerRole portId; infer_instance

end

end Perennial.gryff
