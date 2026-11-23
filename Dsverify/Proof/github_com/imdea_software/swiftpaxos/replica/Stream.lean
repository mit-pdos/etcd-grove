/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Stream.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A replica's readers over the frozen protocols (`sp.inP`, `sp.outQ`, through their elimination
laws, Spec/swift/Inv.lean): what a listener learns of the message it decoded.

* `RdKind`: what a reader knows of its stream: an accepted peer connection (after the peer's
  hello, `peerIn id`: protocol `inP`, the hello `helloBytes id` first), a dialed peer
  connection (`peerOut`: `outQ`), a client's connection (`client cl`: `inP`, proposals of
  `cl`). `RdKind.conn` is the connection's registered kind (`sp.connKind`).
* `rdAt k cid done R`: the bytes read so far `R` are the stream's head and the frames of `done`
  (well formed, of the kind's messages).
* `stream_next`: when the reader has read the frames of `done`, a type byte `c` and bytes that
  decode to `m` (`sp.decodes`), and the protocol holds of an extension of what it read, `m` is
  the stream's next message: of the kind's messages, with its witness `msgOk`, and the bytes
  read are its frame.
* `client_first`: the same for a connection of unknown kind whose first byte is not the peers'
  hello: it is a client's.
* `ownReader_proto`: the protocol fact the reader's token gives (`recvTok_proto`).

`framesProto_wf`: the messages are well formed (`Msg.wf`, in `framesProto` since change log C9,
HUB-REQUEST R1), without which frames do not decode uniquely.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WireWf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

-- PORT: lab imports dropped: Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

variable [GobFmt]

/-- What a replica's reader knows of its stream (see the file header). -/
inductive RdKind where
  | peerIn (id : w32)
  | peerOut
  | client (cl : w32)

def RdKind.conn : RdKind → ConnKind
  | .client cl => .client cl
  | _ => .peer

def RdKind.head : RdKind → List w8
  | .peerIn id => helloBytes id
  | _ => []

def RdKind.ok : RdKind → Msg → Prop
  | .client cl => Msg.isProposeOf cl
  | _ => Msg.isPeer

/-- The end a reader of kind `k` reads (the acceptor's end reads the dialer's stream). -/
def RdKind.side : RdKind → Bool
  | .peerOut => false
  | _ => true

section defs
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

def RdKind.proto (γ : Names) (γc γm : GName) : RdKind → Proto netDistGF
  | .peerOut => outQ γ γc γm
  | _ => inP γ γc γm

end defs

/-- The bytes `R` a reader of kind `k` has read are the stream's head and the frames of
`done`. -/
def rdAt (k : RdKind) (done : List Msg) (R : List w8) : Prop :=
  R = k.head ++ framesOf done ∧ ∀ d ∈ done, d.wf ∧ k.ok d

theorem rdAt_snoc {k : RdKind} {done : List Msg} {R : List w8} {c : w8} {data : List w8}
    {m : Msg} (h : rdAt k done R) (hf : c :: data = m.frame) (hw : m.wf) (hk : k.ok m) :
    rdAt k (done ++ [m]) (R ++ c :: data) := by
  obtain ⟨rfl, hd⟩ := h
  refine ⟨by simp [framesOf, hf, List.append_assoc], ?_⟩
  intro d hd'
  rcases List.mem_append.1 hd' with h | h
  · exact hd d h
  · simp at h; subst h; exact ⟨hw, hk⟩

theorem hello_prefix {a b : w32} {x y : List w8} (h : helloBytes a ++ x <+: helloBytes b ++ y) :
    a = b := by
  obtain ⟨u, hu⟩ := h
  rw [List.append_assoc] at hu
  exact (hello_peel hu.symm).1.symm

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable {γ : Names} {γc γm : GName}

/-- (An unfold of the slot's exposed `connKind`: a missing persistence instance.) -/
instance rconnKind_persistent (cid : Nat) (k : ConnKind) : Persistent (connKind γ cid k) := by
  unfold connKind; infer_instance

instance rmsgOk_persistent (m : Msg) : Persistent (msgOk γ γc γm m) := msgOk_persistent m

/-- A stream's messages are well formed (`framesProto` says so since change log C9,
HUB-REQUEST R1). -/
theorem framesProto_wf (head : List w8) (ok : Msg → Prop) (bs : List w8) :
    framesProto γ γc γm head ok bs ⊢ ∃ ms : List Msg,
      ⌜bs <+: head ++ framesOf ms ∧ ∀ m ∈ ms, ok m ∧ m.wf⌝ ∗
      [∗list] m ∈ ms, msgOk γ γc γm m := by
  unfold framesProto
  iintro ⟨%ms, %H, Hms⟩
  iexists ms
  iframe Hms
  ipureintro
  exact H

/-- The frames of the protocol's messages, with the next message's witness. -/
theorem frames_next (head : List w8) (ok : Msg → Prop) (bs : List w8) (done : List Msg)
    (c : w8) (data : List w8) (m : Msg)
    (hpre : head ++ framesOf done ++ c :: data <+: bs) (hdec : decodes c data m)
    (hd : ∀ d ∈ done, d.wf) :
    framesProto γ γc γm head ok bs ⊢ msgOk γ γc γm m ∗ ⌜ok m ∧ c :: data = m.frame⌝ := by
  iintro Hf
  icases framesProto_wf head ok bs $$ Hf with ⟨%ms, %H, Hms⟩
  obtain ⟨hbs, hok⟩ := H
  have hpre' : framesOf done ++ c :: data <+: framesOf ms := by
    have := hpre.trans hbs
    simp only [List.append_assoc] at this
    exact (List.prefix_append_right_inj head).1 this
  obtain ⟨⟨rest, rfl⟩, hf⟩ := frames_align_dec hd (fun x hx => (hok x hx).2) hdec hpre'
  icases (BigSepL.bigSepL_append).1 $$ Hms with ⟨-, Hm⟩
  icases (BigSepL.bigSepL_cons).1 $$ Hm with ⟨Hm, -⟩
  iframe Hm
  ipureintro
  exact ⟨(hok m (by simp)).1, hf⟩

/-- **The next message** of a stream whose kind the reader knows (see the file header). -/
theorem stream_next (k : RdKind) (cid : Nat) (ext : List w8) (done : List Msg) (c : w8)
    (data : List w8) (m : Msg)
    (hpre : k.head ++ framesOf done ++ c :: data <+: ext) (hdec : decodes c data m)
    (hd : ∀ d ∈ done, d.wf) :
    connKind γ cid k.conn ∗ k.proto γ γc γm cid ext ⊢
      msgOk γ γc γm m ∗ ⌜k.ok m ∧ c :: data = m.frame⌝ := by
  iintro ⟨#Hk, HP⟩
  cases k with
  | peerIn id =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre ⊢
    icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp [helloBytes] at hu
    ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
    subst Heq
    icases HP with ⟨%id', HP⟩
    -- the hello's id is the one read
    ihave %Hid : ⌜id' = id⌝ $$ [HP]
    · unfold framesProto
      icases HP with ⟨%ms, %H, -⟩
      ipureintro
      have h2 := hpre.trans H.1
      simp only [List.append_assoc] at h2
      exact (hello_prefix h2).symm
    subst Hid
    iapply frames_next _ _ ext done c data m hpre hdec hd $$ HP
  | peerOut =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok, List.nil_append] at hpre ⊢
    icases outQ_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp [framesOf] at hu
    ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
    subst Heq
    iapply frames_next [] _ ext done c data m (by simpa using hpre) hdec hd $$ HP
  | client cl =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok, List.nil_append] at hpre ⊢
    icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp [framesOf] at hu
    ihave %Heq := connKind_agree (γ := γ) cid (ConnKind.client cl) k' $$ [$Hk $Hk']
    subst Heq
    iapply frames_next [] _ ext done c data m (by simpa using hpre) hdec hd $$ HP

/-- The frames of `done` then a type byte: the next message of the stream has that type. -/
theorem frames_code_pure {done ms : List Msg} {c : w8} (hd : ∀ d ∈ done, d.wf)
    (hms : ∀ x ∈ ms, x.wf) (h : framesOf done ++ [c] <+: framesOf ms) :
    ∃ m rest, ms = done ++ m :: rest ∧ m.code = c := by
  obtain ⟨u, hu⟩ := h
  induction done generalizing ms with
  | nil =>
    cases ms with
    | nil => simp [framesOf] at hu
    | cons b ms =>
      simp only [framesOf, List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons, Msg.frame, List.singleton_append, List.cons_append,
        List.cons.injEq] at hu
      exact ⟨b, ms, rfl, hu.1.symm⟩
  | cons d done ih =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at hu
    | cons b ms =>
      simp only [framesOf, List.map_cons, List.flatten_cons, List.append_assoc] at hu
      obtain ⟨hdb, h2⟩ := frame_peel (hd d (by simp)) (hms b (by simp)) hu
      subst hdb
      obtain ⟨m, rest, hr, hc⟩ := ih (fun z hz => hd z (List.mem_cons_of_mem _ hz))
        (fun z hz => hms z (List.mem_cons_of_mem _ hz))
        (by simp only [framesOf, List.append_assoc]; exact h2)
      exact ⟨m, rest, by rw [hr]; rfl, hc⟩

/-- A client's stream: every message's type byte is `PROPOSE` (0). -/
theorem client_code (cid : Nat) (cl : w32) (ext : List w8) (done : List Msg) (c : w8)
    (hpre : framesOf done ++ [c] <+: ext) (hd : ∀ d ∈ done, d.wf) :
    connKind γ cid (.client cl) ∗ inP γ γc γm cid ext ⊢ ⌜c = W8 0⌝ := by
  iintro ⟨#Hk, HP⟩
  icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
  · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
  ihave %Heq := connKind_agree (γ := γ) cid (ConnKind.client cl) k' $$ [$Hk $Hk']
  subst Heq
  icases framesProto_wf _ _ _ $$ HP with ⟨%ms, %H, -⟩
  ipureintro
  obtain ⟨m, rest, rfl, hc⟩ := frames_code_pure hd (fun x hx => (H.2 x hx).2)
    (by simpa using hpre.trans H.1)
  have hp := (H.2 m (by simp)).1
  cases m <;> simp [Msg.isProposeOf] at hp
  rw [← hc]; rfl

/-- The type byte of a stream's next message: a message of the kind's. -/
theorem stream_code (k : RdKind) (cid : Nat) (ext : List w8) (done : List Msg) (c : w8)
    (hpre : k.head ++ framesOf done ++ [c] <+: ext) (hd : ∀ d ∈ done, d.wf) :
    connKind γ cid k.conn ∗ k.proto γ γc γm cid ext ⊢ ⌜∃ m : Msg, k.ok m ∧ m.code = c⌝ := by
  iintro ⟨#Hk, HP⟩
  have key : ∀ (head : List w8) (ok : Msg → Prop) (bs : List w8),
      head ++ framesOf done ++ [c] <+: bs →
      framesProto γ γc γm head ok bs ⊢ ⌜∃ m : Msg, ok m ∧ m.code = c⌝ := by
    intro head ok bs hb
    iintro HP
    icases framesProto_wf _ _ _ $$ HP with ⟨%ms, %H, -⟩
    ipureintro
    have h2 := hb.trans H.1
    simp only [List.append_assoc] at h2
    have h3 := (List.prefix_append_right_inj head).1 h2
    obtain ⟨m, rest, rfl, hc⟩ := frames_code_pure hd (fun x hx => (H.2 x hx).2)
      (by simpa [List.append_assoc] using h3)
    exact ⟨m, (H.2 m (by simp)).1, hc⟩
  cases k with
  | peerIn id =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre ⊢
    icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp [helloBytes] at hu
    ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
    subst Heq
    icases HP with ⟨%id', HP⟩
    ihave %Hid : ⌜id' = id⌝ $$ [HP]
    · unfold framesProto
      icases HP with ⟨%ms, %H, -⟩
      ipureintro
      have h2 := hpre.trans H.1
      simp only [List.append_assoc] at h2
      exact (hello_prefix h2).symm
    subst Hid
    iapply key _ _ ext hpre $$ HP
  | peerOut =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre ⊢
    icases outQ_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
    ihave %Heq := connKind_agree (γ := γ) cid ConnKind.peer k' $$ [$Hk $Hk']
    subst Heq
    iapply key [] _ ext hpre $$ HP
  | client cl =>
    simp only [RdKind.proto, RdKind.conn, RdKind.head, RdKind.ok] at hpre ⊢
    icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
    · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
    ihave %Heq := connKind_agree (γ := γ) cid (ConnKind.client cl) k' $$ [$Hk $Hk']
    subst Heq
    iapply key [] _ ext hpre $$ HP

/-- A connection whose first byte is not the peers' hello is a client's. -/
theorem client_kind (cid : Nat) (ext : List w8) (c : w8) (hpre : [c] <+: ext)
    (hc : c ≠ W8 0xFF) :
    inP γ γc γm cid ext ⊢ ∃ cl, connKind γ cid (.client cl) := by
  iintro HP
  icases inP_elim cid ext $$ HP with (%Hnil | ⟨%k', Hk', HP⟩)
  · subst Hnil; obtain ⟨u, hu⟩ := hpre; simp at hu
  cases k' with
  | client cl => iexists cl; iexact Hk'
  | peer =>
    icases HP with ⟨%id', HP⟩
    unfold framesProto
    icases HP with ⟨%ms, %H, -⟩
    exfalso
    have h2 := hpre.trans H.1
    obtain ⟨u, hu⟩ := h2
    simp [helloBytes] at hu
    exact hc hu.1

end laws

section reader
variable [go_gctx : GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- The protocol fact of what a reader over a connection has read, a step later (dsv-bufio's
`ownBufReader_fact` with `recvTokL_proto`, as `net.connReader_proto`). -/
theorem ownReader_proto (br : Loc) (rd : GoInterface) (cid : Nat)
    (side : Bool) (P : Proto netDistGF) (R : List w8) :
    bufio.ownReader br rd (recvTokL cid side P) R ⊢
      bufio.ownReader br rd (recvTokL cid side P) R ∗
      ▷ (⌜R = []⌝ ∨ ∃ ext, ⌜R <+: ext⌝ ∗ □ P cid ext) := by
  unfold bufio.ownReader
  iintro ⟨%ri, %E, %hrd, #HE, H⟩
  icases EtcdGrove.bufio.ownBufReader_fact br ri _ _ E R
      (fun r => iprop(▷ protoPrefix P cid r)) (fun r => recvTokL_proto cid side P r)
      (fun x y => later_mono (protoPrefix_le (List.prefix_append x y))) $$ H with ⟨H, #Hp⟩
  isplitl [H]
  · iexists ri, E; iframe HE H; ipureintro; exact hrd
  inext
  unfold protoPrefix
  icases Hp with (%Hn | ⟨%ext, %He, #HP⟩)
  · ileft; ipureintro; exact Hn
  · iright; iexists ext; iframe HP; ipureintro; exact He

end reader

end sp

end Perennial.github_com.imdea_software.swiftpaxos
