/-
The reader's side of a peer stream (package-internal, for `replicaListener`): what the bytes a
reader goroutine has read so far tell about the next message (its code is the next message's,
the rest is a prefix of its body: the `nextIs` the unmarshalers need), and the `msgSent` fact of
a whole protocol message read.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts of the wire format -/

theorem flatMap_encMsg_length_le (ws ws' : List Msg) (h : ws' <+: ws) :
    (ws'.flatMap encMsg).length ≤ (ws.flatMap encMsg).length := by
  obtain ⟨t, rfl⟩ := h
  simp [List.flatMap_append]

/-- The next message of a stream: bytes `c :: X` read after whole messages `ws` of a stream of
whole messages `ws'` are the code of the next message `m` of `ws'` and a prefix of its body and
what follows. -/
theorem stream_next (ws ws' : List Msg) (c : w8) (X : List w8) (hwf : ∀ m ∈ ws, m.wf)
    (hwf' : ∀ m ∈ ws', m.wf) (h : ws.flatMap encMsg ++ c :: X <+: ws'.flatMap encMsg) :
    ∃ (m : Msg) (rest : List Msg), ws' = ws ++ m :: rest ∧ m.code = c ∧
      X <+: m.body ++ rest.flatMap encMsg := by
  obtain ⟨t, ht⟩ := h
  rcases encMsg_prefix_inj ws ws' (c :: X ++ t) [] hwf hwf' (by simpa using ht) with hp | hp
  · obtain ⟨u, rfl⟩ := hp
    rw [List.flatMap_append, List.append_assoc] at ht
    have hu := List.append_cancel_left ht
    cases u with
    | nil => simp at hu
    | cons m rest =>
      refine ⟨m, rest, rfl, ?_, ?_⟩
      · simp [encMsg] at hu; exact hu.1.symm
      · simp only [List.flatMap_cons, encMsg, List.cons_append, List.nil_append,
          List.cons.injEq] at hu
        exact ⟨t, by rw [hu.2]⟩
  · exfalso
    have h1 := flatMap_encMsg_length_le ws ws' hp
    have h2 := congrArg List.length ht
    simp only [List.length_append, List.length_cons] at h2
    omega

theorem Msg.code_kind (m : Msg) (k : MsgKind) (h : m.code = k.code) : m.kind = some k := by
  cases m <;> cases k <;> simp_all [Msg.kind, Msg.code, MsgKind.code] <;> revert h <;> decide

theorem Msg.code_beacon (m : Msg) (h : m.code = W8 6) : ∃ ts, m = .beacon ts := by
  cases m <;> simp_all [Msg.code] <;> revert h <;> decide

theorem Msg.code_beaconReply (m : Msg) (h : m.code = W8 7) : ∃ ts, m = .beaconReply ts := by
  cases m <;> simp_all [Msg.code] <;> revert h <;> decide

/-- Every message's code is a beacon's, a beacon reply's or a protocol kind's. -/
theorem Msg.code_cases (m : Msg) :
    m.code = W8 6 ∨ m.code = W8 7 ∨ ∃ k ∈ MsgKind.all, m.code = k.code ∧ m.kind = some k := by
  cases m <;> simp [Msg.code, Msg.kind, MsgKind.all, MsgKind.code]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem roleElem_agree (γ : EpNames) (cid : Nat) (r r' : ConnRole) :
    roleElem (GF := GF) γ cid r -∗ roleElem γ cid r' -∗ ⌜r = r'⌝ := by
  unfold roleElem
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- The shape of a peer stream: a prefix of the header and whole well-formed messages. -/
theorem peerStreamOk_shape (γ : EpNames) (a : GoString) (d : w64) (side : Bool) (cid : Nat)
    (bs : List w8) :
    peerStreamOk (GF := GF) γ a d side cid bs ⊢
      ⌜∃ ws' : List Msg, (∀ m ∈ ws', m.wf) ∧ bs <+: streamHdr (uint.nat d) side ++ ws'.flatMap encMsg⌝ := by
  unfold peerStreamOk
  iintro ⟨%i, %ws, -, -, %Hp, -⟩
  ipureintro
  exact ⟨ws, Hp.1, Hp.2⟩

end ghost

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The stream a reader of peer `j`'s connection at replica `id` reads (the other end's): from
its protocol and the connection's role, the peer protocol of the dialer `dialerOf id j side`, at
end `!side`. -/
theorem pin_stream (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool) (cid : Nat)
    (dl : Nat) (R : List w8) (hdl : dl = dialerOf id j side) (hR : R ≠ []) :
    roleElem (GF := GF) γ cid (.peer (W64 dl)) -∗ protoPrefix (peerPin γ id L j side) cid R -∗
      peerStreamOk γ (if side then L.getD id [] else L.getD j []) (W64 dl) (!side) cid R := by
  iintro #Hr Hp
  unfold protoPrefix
  icases Hp with (%H | ⟨%ext, %Hpre, #HP⟩)
  · exact absurd H hR
  obtain ⟨t, rfl⟩ := Hpre
  cases side
  · unfold peerPin repAccP
    simp only [Bool.false_eq_true, ite_false, Bool.not_false]
    icases HP with (%He | ⟨%rl, #Hrl, #HP⟩)
    · exact absurd (List.append_eq_nil_iff.mp He).1 hR
    ihave %Heq := roleElem_agree $$ Hr Hrl
    subst Heq
    simp only
    iapply peerStreamOk_prefix $$ HP
  · unfold peerPin repDialP
    simp only [ite_true, Bool.not_true]
    icases HP with (%He | ⟨%rl, #Hrl, #HP⟩)
    · exact absurd (List.append_eq_nil_iff.mp He).1 hR
    ihave %Heq := roleElem_agree $$ Hr Hrl
    subst Heq
    simp only
    iapply peerStreamOk_prefix $$ HP


/-- What the unmarshalers need of the stream a reader of peer `j`'s connection reads, after
whole messages `ws` and the next code `c`: a prefix of the body of a message of code `c`, given
how such a body decodes (`henc`). -/
theorem listener_nextIs {A : Type} (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat)
    (side : Bool) (cid : Nat) (t : Loc) (eof la ra ed : GoInterface) (dl : Nat)
    (hdl : dl = dialerOf id j side) (hd : dl < 5) (ws : List Msg) (c : w8) (enc : A → List w8) (wf : A → Prop) (hwf : ∀ m ∈ ws, m.wf)
    (henc : ∀ m : Msg, m.wf → m.code = c → ∃ v, wf v ∧ m.body = enc v) :
    roleElem (GF := GF) γ cid (.peer (W64 dl)) ⊢
      nextIs (connRd t cid side eof la ra ed (peerPin γ id L j side))
        (streamHdr dl (!side) ++ ws.flatMap encMsg ++ [c]) enc wf := by
  iintro #Hr
  unfold nextIs
  imodintro
  iintro %S #Hp
  simp only [connRd]
  inext
  by_cases hS : streamHdr dl (!side) ++ ws.flatMap encMsg ++ [c] <+: S
  · have hne : S ≠ [] := by
      intro h; subst h
      have := hS.length_le; simp at this
    ihave #Hs := pin_stream γ id L j side cid dl S hdl hne $$ Hr Hp
    ihave %Hsh := peerStreamOk_shape $$ Hs
    ipureintro
    intro _
    obtain ⟨ws', hwf', hpre⟩ := Hsh
    have hdn : uint.nat (W64 (dl : Int)) = dl := by word
    rw [hdn] at hpre
    obtain ⟨X, hX⟩ := hS
    rw [← hX] at hpre
    have hpre' : ws.flatMap encMsg ++ c :: X <+: ws'.flatMap encMsg := by
      have := (List.prefix_append_right_inj (streamHdr dl (!side))).mp
        (by simpa [List.append_assoc] using hpre)
      exact this
    obtain ⟨m, rest, hws', hc, hX'⟩ := stream_next ws ws' c X hwf hwf' hpre'
    have hm : m.wf := hwf' m (by rw [hws']; simp)
    obtain ⟨v, hv, hb⟩ := henc m hm hc
    refine ⟨v, rest.flatMap encMsg, hv, ?_⟩
    rw [← hX, List.drop_left' rfl, ← hb]
    exact hX'
  · ipureintro
    intro h; exact absurd h hS

/-- A whole protocol message `m` read after whole messages `ws` by the reader of peer `j`'s
connection at replica `id`: it is the `(protoMsgs ws).length`-th message `j` sent to `id`. -/
theorem listener_msgSent (γ : EpNames) (id : Nat) (L : List GoString) (j : Nat) (side : Bool)
    (cid : Nat) (dl : Nat) (hdl : dl = dialerOf id j side) (hd : dl < 5) (hid : id < L.length)
    (hj : j < L.length) (ws : List Msg) (m : Msg) (hwf : ∀ m ∈ ws, m.wf) (hm : m.wf)
    (hp : m.isProto = true) :
    listFinal (GF := GF) γ L -∗ roleElem γ cid (.peer (W64 dl)) -∗
      protoPrefix (peerPin γ id L j side) cid (streamHdr dl (!side) ++ (ws ++ [m]).flatMap encMsg) -∗
      msgSent γ j id (protoMsgs ws).length m := by
  have hne : streamHdr dl (!side) ++ (ws ++ [m]).flatMap encMsg ≠ [] := by
    simp [encMsg]
  have hpin := pin_stream (GF := GF) γ id L j side cid dl _ hdl hne
  have hdn : uint.nat (W64 (dl : Int)) = dl := by word
  have hgd : ∀ i, i < L.length → L[i]? = some (L.getD i []) := fun i h => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  have hnext := peerStreamOk_next (GF := GF) γ (if side then L.getD id [] else L.getD j []) (W64 dl) (!side)
    cid ws m hwf hm
  rw [hp, hdn] at hnext
  cases side
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false] at hpin hnext ⊢
    unfold dialerOf at hdl; simp only [Bool.false_eq_true, ite_false] at hdl; subst hdl
    simp only [ite_true, streamDir] at hnext
    iintro #Hlf #Hr Hp
    ihave #Hs := hpin $$ Hr Hp
    ihave ⟨%i, #Ha, #Hm⟩ := hnext $$ [Hs]
    · iexact Hs
    ihave #Ha' := listFinal_addrId γ L j _ (hgd j hj) $$ Hlf
    ihave %Hi := addrId_agree $$ Ha Ha'
    subst Hi
    iexact Hm
  · simp only [ite_true, Bool.not_true] at hpin hnext ⊢
    unfold dialerOf at hdl; simp only [ite_true] at hdl; subst hdl
    simp only [Bool.false_eq_true, ite_false, streamDir] at hnext
    iintro #Hlf #Hr Hp
    ihave #Hs := hpin $$ Hr Hp
    ihave ⟨%i, #Ha, #Hm⟩ := hnext $$ [Hs]
    · iexact Hs
    ihave #Ha' := listFinal_addrId γ L id _ (hgd id hid) $$ Hlf
    ihave %Hi := addrId_agree $$ Ha Ha'
    subst Hi
    iexact Hm

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
