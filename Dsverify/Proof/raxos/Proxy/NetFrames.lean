/-
Package `proxy`: parsing the proxy port's stream (`proxyInProto`: the client's handshake, then
`ClientBatch` frames), for `connectionListener` (`NetListen.lean`).

* `frs L`: the frames of `L`; `le8_inj`, `leNum_le8`: the 8-byte length below `2^64`.
* `frs_align`: bytes made of whole frames `A` that a stream of frames `L` starts with are the
  frames of `L`'s first `A.length` batches (lengths below `2^64`).
* `frs_head`: a nonempty stream of frames starts with the code byte `1`, the length, the encoding.
* `recv_frames`: what the proxy's reader end knows of what it read (`recvTok_proto`), with the
  frames' facts. Its length bound is `HUB-REQUEST P1` (`proxyInProto` bounds no length).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg

/-- The frames of the batches `L`. -/
def frs (L : List Batch) : List w8 := (L.map frame).flatten

theorem frs_nil : frs [] = [] := rfl
theorem frs_cons (b : Batch) (L : List Batch) : frs (b :: L) = frame b ++ frs L := rfl
theorem frs_append (A B : List Batch) : frs (A ++ B) = frs A ++ frs B := by
  simp [frs]

theorem le8_length (n : Nat) : (le8 n).length = 8 := by simp [le8]

theorem le8_eq_u64Le (n : Nat) (h : n < 2 ^ 64) : le8 n = u64Le (W64 n) := by
  rw [u64Le_le8]; congr 1; simp [uint.nat, W64]; omega

theorem le8_inj {m n : Nat} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) (h : le8 m = le8 n) : m = n := by
  rw [le8_eq_u64Le m hm, le8_eq_u64Le n hn] at h
  have h2 := congrArg BitVec.toNat (u64Le_inj h)
  simp [W64] at h2
  omega

theorem leNum_le8 (n : Nat) (h : n < 2 ^ 64) : leNum (le8 n) = n := by
  rw [leNum_combine, le8_eq_u64Le n h, u64Le, u64LeDef, LittleEndian.combine_split]
  simp [W64]; omega

/-- Two frames that two streams start with are the same bytes. -/
theorem frame_append_eq {b b' : Batch} {x y : List w8} (hb : (encBatch b).length < 2 ^ 64)
    (hb' : (encBatch b').length < 2 ^ 64) (h : frame b ++ x = frame b' ++ y) :
    frame b = frame b' ∧ x = y := by
  have h' : le8 (encBatch b).length ++ (encBatch b ++ x) =
      le8 (encBatch b').length ++ (encBatch b' ++ y) := by
    simpa [frame, List.append_assoc] using h
  obtain ⟨h1, h2⟩ := List.append_inj h' (by rw [le8_length, le8_length])
  have hm := le8_inj hb hb' h1
  obtain ⟨h3, h4⟩ := List.append_inj h2 hm
  simp [frame, h1, h3, h4]

theorem frs_align (A L : List Batch) (x : List w8)
    (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 64) (hL : ∀ b ∈ L, (encBatch b).length < 2 ^ 64)
    (h : frs A ++ x <+: frs L) :
    frs A = frs (L.take A.length) ∧ x <+: frs (L.drop A.length) := by
  induction A generalizing L with
  | nil => simpa [frs_nil] using h
  | cons b A ih =>
    obtain ⟨z, hz⟩ := h
    cases L with
    | nil => simp [frs_cons, frs_nil, frame] at hz
    | cons b' L =>
      rw [frs_cons, frs_cons, List.append_assoc, List.append_assoc] at hz
      obtain ⟨he, hr⟩ := frame_append_eq (hA b (by simp)) (hL b' (by simp)) hz
      obtain ⟨h1, h2⟩ := ih L (fun c hc => hA c (by simp [hc])) (fun c hc => hL c (by simp [hc]))
        ⟨z, by rw [List.append_assoc]; exact hr⟩
      simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons, frs_cons, he, h1]
      exact ⟨trivial, h2⟩

/-- A nonempty stream of frames starts a frame: the code byte `1`, the length, the encoding. -/
theorem frs_head (L : List Batch) (n : Nat) (c : w8) (y : List w8)
    (h : c :: y <+: frs (L.drop n)) :
    ∃ b', L[n]? = some b' ∧ c = W8 1 ∧
      y <+: le8 (encBatch b').length ++ encBatch b' ++ frs (L.drop (n + 1)) := by
  cases hd : L.drop n with
  | nil => rw [hd, frs_nil] at h; simp at h
  | cons b' rest =>
    have h1 : L[n]? = some b' := by
      rw [← List.head?_drop, hd]; rfl
    have h2 : L.drop (n + 1) = rest := by
      rw [← List.drop_drop, hd]; rfl
    rw [hd, frs_cons] at h
    refine ⟨b', h1, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := h
      simp [frame] at hz
      exact hz.1
    · rw [h2]
      obtain ⟨z, hz⟩ := h
      simp only [frame, List.append_assoc, List.cons_append, List.cons.injEq] at hz
      exact ⟨z, by simp only [List.append_assoc]; exact hz.2⟩

/-- An 8-byte prefix of a frame's rest is its length. -/
theorem prefix_le8 {d e W : List w8} {m : Nat} (hd : d.length = 8) (h : d ++ e <+: le8 m ++ W) :
    d = le8 m := by
  obtain ⟨z, hz⟩ := h
  have := congrArg (List.take 8) hz
  rw [List.append_assoc, List.take_left' hd, List.take_left' (le8_length m)] at this
  exact this

/-- A whole frame read (its length below `2^64`): it is the frame's encoding. -/
theorem prefix_enc {bs pend W : List w8} {b' : Batch} (hbs : bs.length < 2 ^ 64)
    (hb' : (encBatch b').length < 2 ^ 64)
    (h : le8 bs.length ++ bs ++ pend <+: le8 (encBatch b').length ++ encBatch b' ++ W) :
    bs = encBatch b' := by
  have h8 := prefix_le8 (le8_length _) (by rw [List.append_assoc] at h; exact h)
  have hl := le8_inj hbs hb' h8
  obtain ⟨z, hz⟩ := h
  rw [h8, List.append_assoc, List.append_assoc, List.append_assoc] at hz
  have hz2 := List.append_cancel_left hz
  have := congrArg (List.take bs.length) hz2
  rw [List.take_left' rfl, hl, List.take_left' rfl] at this
  exact this

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- Two handshakes that a stream starts with are the same. -/
theorem hs_eq_of_prefix {a b : Nat} {Z : List w8} (ha : hs a <+: Z) (hb : hs b <+: Z) :
    hs a = hs b := by
  rcases List.prefix_of_prefix_length_le ha hb (by simp [hs]) with h
  exact List.IsPrefix.eq_of_length h (by simp [hs])

/-- The facts of a stream the proxy's port allows, with the frames' lengths below `2^63`. -/
theorem proxyIn_frames (γ : QNames) (k : Nat) (cid : w64) (ext : List w8) :
    proxyInProto (GF := GF) γ k cid ext ⊢
      ∃ (cl : Nat) (L : List Batch), ⌜cl < 6 ∧ ext <+: hs (21 + cl) ++ frs L ∧
        ∀ b ∈ L, batchOk b ∧ (encBatch b).length < 2 ^ 63⌝ ∗
      [∗list] n ↦ b ∈ L, batchReg γ b.id b ∗ ∃ c j, tixAt γ ((k : Int), c, j) cid n := by
  unfold proxyInProto
  iintro ⟨%cl, %L, %hL, H⟩
  iexists cl, L
  iframe H
  ipureintro
  exact hL

/-- What the proxy's reader end has read, starting with the handshake `hs n`, is a prefix of a
stream of frames after that handshake that the port allows. -/
theorem recv_frames (γ : QNames) (k n : Nat) (cid : w64) (W : List w8) (hW : hs n <+: W) :
    recvTok cid true (proxyInProto (GF := GF) γ k) W ⊢
      recvTok cid true (proxyInProto γ k) W ∗
      (⌜W = []⌝ ∨ ∃ L : List Batch, ⌜W <+: hs n ++ frs L ∧
        ∀ b ∈ L, batchOk b ∧ (encBatch b).length < 2 ^ 63⌝ ∗
        □ [∗list] n ↦ b ∈ L, batchReg γ b.id b ∗ ∃ c j, tixAt γ ((k : Int), c, j) cid n) := by
  iintro H
  ihave ⟨H, Hp⟩ := recvTok_proto cid true _ _ $$ H
  iframe H
  unfold protoPrefix
  icases Hp with (%h | ⟨%ext, %hp, #HP⟩)
  · ileft; ipureintro; exact h
  · ihave ⟨%cl, %L, %hL, #Hs⟩ := proxyIn_frames γ k cid ext $$ HP
    have he : hs n = hs (21 + cl) :=
      hs_eq_of_prefix ((hW.trans hp).trans hL.2.1) (List.prefix_append _ _)
    iright
    iexists L
    iframe Hs
    ipureintro
    rw [he]
    exact ⟨hp.trans hL.2.1, hL.2.2⟩

end iris

end Perennial.raxos
