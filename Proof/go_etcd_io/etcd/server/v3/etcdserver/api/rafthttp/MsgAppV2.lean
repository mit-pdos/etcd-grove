/-
**The msgappv2 stream's frames** (2026-10-22, rafthttp stage 3): the pure model of
`msgappv2_codec.go`, what its encoder writes and its decoder reads. Lean-first; D38a.

The encoder and the decoder of one connection each keep a state (`V2St`: the last `MsgApp`'s term
and the index its entries end at), updated in lockstep. A frame (`V2Frame from to cs w bs cs'`) at
the state `cs` carries the wire content `w` (what the decoder gives back) in the bytes `bs` and
leads to `cs'`; it is one of
- a **link heartbeat** (`msgTypeLinkHeartbeat`, the byte `0`): the content of
  `linkHeartbeatMessage` (`hbWire`), the state unchanged;
- an **AppEntries** frame (`msgTypeAppEntries`, `1`): an `MsgApp` from `from` (the decoder's
  `remote`) to `to` (its `local`) whose term and log term are the state's term and whose index is
  the state's index, no vote, rejection, hint, snapshot or context (`shortWire`), carried as the
  entries' count, each entry's encoding after its length, and the commit index; the state's index
  advances by the count;
- an **App** frame (`msgTypeApp`, `2`): any message, as `messageEncoder`'s frame of an encoding
  (`msgFrame`); the state becomes its term and the index of its last entry (else its index).

Frames are self-delimiting (`V2Frame.unique`): from one state, two frames of which one stream
starts with each are the same frame, with the same content. Lengths are below `2^63` (as `Size`'s
`int` gives them), so that a length's eight bytes determine it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Codec

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section model
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The msgappv2 codec's state**: the term and the index (`msgAppV2Encoder`'s and
`msgAppV2Decoder`'s `term`, `index`). -/
structure V2St where
  term : w64
  index : w64

/-- The wire content of `linkHeartbeatMessage` (`raftpb.Message{Type: MsgHeartbeat}`). -/
def hbWire : MsgWire :=
  ⟨⟨MsgHeartbeat, 0, 0, 0, 0, 0, 0, 0, false, 0⟩, [], none, []⟩

/-- The wire content an AppEntries frame decodes to. -/
def shortWire (frm to : w64) (cs : V2St) (ents : List EntryM) (commit : w64) : MsgWire :=
  ⟨⟨MsgApp, to, frm, cs.term, cs.term, cs.index, commit, 0, false, 0⟩, ents, none, []⟩

/-- The index the entries of `w` end at: its last entry's, else its own. -/
def lastIdx (w : MsgWire) : w64 :=
  match w.ents.getLast? with
  | some e => e.Index'
  | none => w.msg.Index'

/-- Each entry's encoding after its length (eight big-endian bytes). -/
def entFrames : List (List w8) → List w8
  | [] => []
  | b :: bs => u64Be (W64 b.length) ++ b ++ entFrames bs

theorem entFrames_append (a b : List (List w8)) :
    entFrames (a ++ b) = entFrames a ++ entFrames b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [entFrames, ih, List.append_assoc]

/-- The entry frames up to the `i+1`-th: those up to the `i`-th, then its own. -/
theorem entFrames_take_succ (E : List (List w8)) (i : Nat) (h : i < E.length) :
    entFrames (E.take (i + 1)) = entFrames (E.take i) ++ (u64Be (W64 E[i].length) ++ E[i]) := by
  rw [List.take_succ, List.getElem?_eq_getElem h, Option.toList_some, entFrames_append]
  simp [entFrames]

/-- An entry's encoding, no longer than `2^63` bytes. -/
def EntEnc (e : EntryM) (b : List w8) : Prop := EntWireOk e b ∧ b.length < 2 ^ 63

/-- **A msgappv2 frame** (see the file header). -/
def V2Frame (frm to : w64) (cs : V2St) (w : MsgWire) (bs : List w8) (cs' : V2St) : Prop :=
  (w = hbWire ∧ bs = [W8 0] ∧ cs' = cs) ∨
  (∃ ebs : List (List w8), w = shortWire frm to cs w.ents w.msg.Commit' ∧
    List.Forall₂ EntEnc w.ents ebs ∧ w.ents.length < 2 ^ 63 ∧
    bs = W8 1 :: (u64Be (W64 w.ents.length) ++ entFrames ebs ++ u64Be w.msg.Commit') ∧
    cs' = ⟨cs.term, cs.index + W64 w.ents.length⟩) ∨
  (∃ (st : MsgSt) (mbs : List w8), wireOf st = w ∧ MsgWireOk st mbs ∧ mbs.length < 2 ^ 63 ∧
    bs = W8 2 :: msgFrame mbs ∧ cs' = ⟨w.msg.Term', lastIdx w⟩)

/-! ## Indices -/

theorem sint_sub_one_bounds {x : w64} (h : 0 < sint.Z x) :
    0 ≤ sint.Z (x - W64 1) ∧ sint.Z (x - W64 1) < sint.Z x := by word

theorem sint_sub_one_toNat {x : w64} (h : 0 < sint.Z x) :
    (sint.Z (x - W64 1)).toNat = sint.nat x - 1 := by unfold sint.nat; word

theorem uint_nat_ge_of_sint {x : w64} {n : Nat} (h : (n : Int) ≤ sint.Z x) :
    n ≤ uint.nat (x - W64 0) := by word

/-! ## Lengths and their bytes -/

theorem u64Be_inj {x y : w64} (h : u64Be x = u64Be y) : x = y := by
  have := congrArg beToU64 h
  simpa [beToU64_u64Be] using this

/-- Lengths below `2^63` with the same eight bytes are equal. -/
theorem u64Be_len_inj {m n : Nat} (hm : m < 2 ^ 63) (hn : n < 2 ^ 63)
    (h : u64Be (W64 m) = u64Be (W64 n)) : m = n := by
  have h' := u64Be_inj h
  have : (W64 m).toNat = (W64 n).toNat := by rw [h']
  simp only [W64, BitVec.toNat_ofInt] at this
  omega

/-- Two strings that start with eight bytes each: the first eight bytes agree. -/
theorem append8_eq {a b x y : List w8} (ha : a.length = 8) (hb : b.length = 8)
    (h : a ++ x = b ++ y) : a = b ∧ x = y := by
  have h1 := congrArg (List.take 8) h
  have h2 := congrArg (List.drop 8) h
  simp only [List.take_append_of_le_length (by omega : 8 ≤ a.length),
    List.take_append_of_le_length (by omega : 8 ≤ b.length), List.drop_append_of_le_length
    (by omega : 8 ≤ a.length), List.drop_append_of_le_length (by omega : 8 ≤ b.length),
    List.take_of_length_le (by omega : a.length ≤ 8), List.take_of_length_le (by omega : b.length ≤ 8),
    List.drop_of_length_le (by omega : a.length ≤ 8), List.drop_of_length_le (by omega : b.length ≤ 8),
    List.nil_append] at h1 h2
  exact ⟨h1, h2⟩

/-- A length-prefixed chunk is self-delimiting. -/
theorem chunk_eq {a b x y : List w8} (ha : a.length < 2 ^ 63) (hb : b.length < 2 ^ 63)
    (h : u64Be (W64 a.length) ++ a ++ x = u64Be (W64 b.length) ++ b ++ y) : a = b ∧ x = y := by
  simp only [List.append_assoc] at h
  obtain ⟨h8, hr⟩ := append8_eq (u64Be_length _) (u64Be_length _) h
  exact List.append_inj hr (u64Be_len_inj ha hb h8)

/-- Entry frames are self-delimiting: equal-length lists of chunks, then anything. -/
theorem entFrames_eq {xs bs : List (List w8)} {x y : List w8} (hl : xs.length = bs.length)
    (ha : ∀ a ∈ xs, a.length < 2 ^ 63) (hb : ∀ b ∈ bs, b.length < 2 ^ 63)
    (h : entFrames xs ++ x = entFrames bs ++ y) : xs = bs ∧ x = y := by
  induction xs generalizing bs with
  | nil =>
    cases bs with
    | nil => simpa [entFrames] using h
    | cons _ _ => simp at hl
  | cons a xs ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [entFrames, List.append_assoc] at h
      have h' : u64Be (W64 a.length) ++ a ++ (entFrames xs ++ x) =
          u64Be (W64 b.length) ++ b ++ (entFrames bs ++ y) := by
        simpa [List.append_assoc] using h
      obtain ⟨rfl, hr⟩ := chunk_eq (ha a (by simp)) (hb b (by simp)) h'
      obtain ⟨rfl, rfl⟩ := ih (by simpa using hl) (fun a' h => ha a' (by simp [h]))
        (fun b' h => hb b' (by simp [h])) hr
      exact ⟨rfl, rfl⟩

/-- The entries' encodings are no longer than `2^63` bytes. -/
theorem Forall₂_EntEnc_len {es : List EntryM} {ebs : List (List w8)}
    (h : List.Forall₂ EntEnc es ebs) : ∀ b ∈ ebs, b.length < 2 ^ 63 := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hx.2
    · exact ih b hb

/-- Encodings determine the entries. -/
theorem Forall₂_EntEnc_inj {es es' : List EntryM} {ebs : List (List w8)}
    (h : List.Forall₂ EntEnc es ebs) (h' : List.Forall₂ EntEnc es' ebs) : es = es' := by
  induction h generalizing es' with
  | nil => cases h'; rfl
  | cons hx _ ih =>
    cases h' with
    | cons hx' hr' => rw [EntWireOk.inj hx.1 hx'.1, ih hr']

/-- **Frames are self-delimiting** (see the file header). -/
theorem V2Frame.unique {frm to : w64} {cs : V2St} {w1 w2 : MsgWire} {b1 b2 x y : List w8}
    {c1 c2 : V2St} (h1 : V2Frame frm to cs w1 b1 c1) (h2 : V2Frame frm to cs w2 b2 c2)
    (h : b1 ++ x = b2 ++ y) : w1 = w2 ∧ b1 = b2 ∧ c1 = c2 ∧ x = y := by
  rcases h1 with ⟨rfl, rfl, rfl⟩ | ⟨e1, hw1, hf1, hn1, rfl, rfl⟩ | ⟨s1, m1, rfl, hm1, hl1, rfl, rfl⟩ <;>
  rcases h2 with ⟨rfl, rfl, rfl⟩ | ⟨e2, hw2, hf2, hn2, rfl, rfl⟩ | ⟨s2, m2, rfl, hm2, hl2, rfl, rfl⟩ <;>
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h <;>
  (try (obtain ⟨h0, -⟩ := h; exact absurd h0 (by decide)))
  · exact ⟨rfl, rfl, rfl, h.2⟩
  · -- two AppEntries frames
    obtain ⟨-, h⟩ := h
    simp only [List.append_assoc] at h
    obtain ⟨hc8, hr⟩ := append8_eq (u64Be_length _) (u64Be_length _) h
    have hn := u64Be_len_inj hn1 hn2 hc8
    have hl : e1.length = e2.length := by
      rw [← hf1.length_eq, ← hf2.length_eq, hn]
    obtain ⟨rfl, hr2⟩ := entFrames_eq hl (Forall₂_EntEnc_len hf1) (Forall₂_EntEnc_len hf2)
      (by simpa only [List.append_assoc] using hr)
    obtain ⟨hcm, rfl⟩ := append8_eq (u64Be_length _) (u64Be_length _) hr2
    have he : w1.ents = w2.ents := Forall₂_EntEnc_inj hf1 hf2
    have hcm' := u64Be_inj hcm
    have hw : w1 = w2 := by rw [hw1, hw2, he, hcm']
    subst hw
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- two App frames
    obtain ⟨-, h⟩ := h
    simp only [msgFrame] at h
    obtain ⟨rfl, rfl⟩ := chunk_eq hl1 hl2 (by simpa only [List.append_assoc] using h)
    have hw := pbMessage_wire_eq hm1 hm2
    have : wireOf s1 = wireOf s2 := by
      obtain ⟨a, b, c, d⟩ := hw
      simp only [wireOf, a, b, c, d]
    rw [this]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## What the encoder is given -/

/-- A link heartbeat (`isLinkHeartbeatMessage`): a `MsgHeartbeat` from and to `0`. -/
def isHB (m : MessageM) : Prop := m.Type' = MsgHeartbeat ∧ m.From' = 0 ∧ m.To' = 0

instance (m : MessageM) : Decidable (isHB m) := by unfold isHB; infer_instance

/-- **A message the msgappv2 encoder may be given** on the connection from `frm` to `to`: one that
marshals, and either `linkHeartbeatMessage` or an `MsgApp` of raft's shape (`AppShape`, D38a)
between them (the stream's writer sends only those: `peer.pick`, `streamWriter.run`). -/
def V2EncOk (frm to : w64) (st : MsgSt) : Prop :=
  MsgMarshals st ∧
  ((isHB st.msg ∧ wireOf st = hbWire) ∨
   (st.msg.Type' = MsgApp ∧ AppShape st ∧ st.msg.From' = frm ∧ st.msg.To' = to))

/-- A link heartbeat the encoder is given is the heartbeat frame. -/
theorem V2EncOk.hb_frame {frm to : w64} {st : MsgSt} (cs : V2St) (h : V2EncOk frm to st)
    (hb : isHB st.msg) : V2Frame frm to cs (wireOf st) [W8 0] cs := by
  rcases h.2 with ⟨-, hw⟩ | ⟨hty, -⟩
  · exact Or.inl ⟨hw, rfl, rfl⟩
  · exact absurd (hb.1.symm.trans hty) (by simp [MsgHeartbeat, MsgApp])

/-- The bytes of an AppEntries frame: its entries' encodings `ebs`, then the commit index. -/
def shortBytes (ebs : List (List w8)) (commit : w64) : List w8 :=
  W8 1 :: (u64Be (W64 ebs.length) ++ entFrames ebs ++ u64Be commit)

/-- An AppEntries frame's bytes around its `i`-th entry. -/
theorem shortBytes_split (E : List (List w8)) (c : w64) (i : Nat) (h : i < E.length) :
    shortBytes E c = W8 1 :: (u64Be (W64 E.length) ++ entFrames (E.take i) ++
      (u64Be (W64 E[i].length) ++ E[i]) ++ entFrames (E.drop (i + 1)) ++ u64Be c) := by
  unfold shortBytes
  have hE : entFrames E = entFrames (E.take (i + 1)) ++ entFrames (E.drop (i + 1)) := by
    rw [← entFrames_append, List.take_append_drop]
  rw [hE, entFrames_take_succ E i h]
  simp [List.append_assoc]

/-- An `MsgApp` the encoder is given that continues the state (its index the state's, its log
term and term the state's term) is an AppEntries frame of its entries' encodings. -/
theorem V2EncOk.short_frame {frm to : w64} {st : MsgSt} {cs : V2St} {ebs : List (List w8)}
    (h : V2EncOk frm to st) (hb : ¬ isHB st.msg) (hi : cs.index = st.msg.Index')
    (ht : cs.term = st.msg.LogTerm') (hlt : st.msg.LogTerm' = st.msg.Term')
    (he : List.Forall₂ EntEnc st.ents ebs) (hn : st.ents.length < 2 ^ 63) :
    V2Frame frm to cs (wireOf st) (shortBytes ebs st.msg.Commit')
      ⟨cs.term, cs.index + W64 st.ents.length⟩ := by
  rcases h.2 with ⟨hhb, -⟩ | ⟨hty, ⟨hv, hr, hrh, hsn, hctx, -⟩, hf, ht'⟩
  · exact absurd hhb hb
  refine Or.inr (Or.inl ⟨ebs, ?_, he, hn, ?_, rfl⟩)
  · simp only [wireOf, shortWire]
    obtain ⟨m, ents, snap, ctx, resps⟩ := st
    obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := m
    simp_all
  · simp only [shortBytes, wireOf, he.length_eq]

/-- Any message the encoder is given is an App frame of an encoding. -/
theorem V2Frame.full {frm to : w64} {st : MsgSt} {mbs : List w8} (cs : V2St)
    (hw : MsgWireOk st mbs) (hl : mbs.length < 2 ^ 63) :
    V2Frame frm to cs (wireOf st) (W8 2 :: msgFrame mbs) ⟨st.msg.Term', lastIdx (wireOf st)⟩ :=
  Or.inr (Or.inr ⟨st, mbs, rfl, hw, hl, rfl, rfl⟩)

/-! ## What the decoder knows: the bytes it reads are a prefix of a frame, or extend one -/

/-- **`ys` is compatible with a frame from the state `cs`**: some frame and `ys` are each a prefix
of the other (both extend to a common stream). What the decoder knows of the bytes it has read
of its next frame (from what the stream's protocol promises of the whole stream). -/
def V2Compat (frm to : w64) (cs : V2St) (ys : List w8) : Prop :=
  ∃ (w : MsgWire) (bs : List w8) (cs' : V2St) (z z' : List w8),
    V2Frame frm to cs w bs cs' ∧ ys ++ z = bs ++ z'

/-- Entry frames are self-delimiting from the left: a prefix list of chunks of a longer one. -/
theorem entFrames_prefix {pre E : List (List w8)} {x y : List w8}
    (hp : ∀ a ∈ pre, a.length < 2 ^ 63) (hE : ∀ b ∈ E, b.length < 2 ^ 63)
    (hl : pre.length ≤ E.length) (h : entFrames pre ++ x = entFrames E ++ y) :
    pre = E.take pre.length ∧ x = entFrames (E.drop pre.length) ++ y := by
  induction pre generalizing E with
  | nil => simpa [entFrames] using h
  | cons a pre ih =>
    cases E with
    | nil => simp at hl
    | cons b E =>
      simp only [entFrames, List.append_assoc] at h
      have h' : u64Be (W64 a.length) ++ a ++ (entFrames pre ++ x) =
          u64Be (W64 b.length) ++ b ++ (entFrames E ++ y) := by
        simpa [List.append_assoc] using h
      obtain ⟨rfl, hr⟩ := chunk_eq (hp a (by simp)) (hE b (by simp)) h'
      obtain ⟨h1, h2⟩ := ih (fun a' h => hp a' (by simp [h])) (fun b' h => hE b' (by simp [h]))
        (by simpa using hl) hr
      exact ⟨by simp [← h1], by simpa using h2⟩

/-- The first byte of a frame says its kind. -/
theorem V2Frame.tag {frm to : w64} {cs cs' : V2St} {w : MsgWire} {bs : List w8}
    (h : V2Frame frm to cs w bs cs') :
    (bs = [W8 0] ∧ w = hbWire ∧ cs' = cs) ∨
    (∃ ebs, bs = shortBytes ebs w.msg.Commit' ∧ w = shortWire frm to cs w.ents w.msg.Commit' ∧
      List.Forall₂ EntEnc w.ents ebs ∧ w.ents.length < 2 ^ 63 ∧
      cs' = ⟨cs.term, cs.index + W64 w.ents.length⟩) ∨
    (∃ (st : MsgSt) (mbs : List w8), bs = W8 2 :: msgFrame mbs ∧ wireOf st = w ∧
      MsgWireOk st mbs ∧ mbs.length < 2 ^ 63 ∧ cs' = ⟨w.msg.Term', lastIdx w⟩) := by
  rcases h with ⟨hw, hb, hc⟩ | ⟨ebs, hw, hf, hn, hb, hc⟩ | ⟨st, mbs, hw, hm, hl, hb, hc⟩
  · exact Or.inl ⟨hb, hw, hc⟩
  · refine Or.inr (Or.inl ⟨ebs, ?_, hw, hf, hn, hc⟩)
    rw [hb, shortBytes, hf.length_eq]
  · exact Or.inr (Or.inr ⟨st, mbs, hb, hw, hm, hl, hc⟩)

/-- The first byte the decoder reads is a frame's tag: `0` (and then the frame is the heartbeat's),
`1` or `2`. -/
theorem V2Compat.head {frm to : w64} {cs : V2St} {b : w8} {ys : List w8}
    (h : V2Compat frm to cs (b :: ys)) :
    (b = W8 0 ∧ V2Frame frm to cs hbWire [W8 0] cs) ∨ b = W8 1 ∨ b = W8 2 := by
  obtain ⟨w, bs, cs', z, z', hF, heq⟩ := h
  rcases hF.tag with ⟨rfl, rfl, rfl⟩ | ⟨ebs, rfl, -⟩ | ⟨st, mbs, rfl, -⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
    exact Or.inl ⟨heq.1, hF⟩
  · simp only [shortBytes, List.cons_append, List.cons.injEq] at heq
    exact Or.inr (Or.inl heq.1)
  · simp only [List.cons_append, List.cons.injEq] at heq
    exact Or.inr (Or.inr heq.1)

/-- An App frame's length bytes: what the decoder reads after the tag `2`. -/
theorem V2Compat.app_len {frm to : w64} {cs : V2St} {ys8 : List w8}
    (h : V2Compat frm to cs (W8 2 :: ys8)) (h8 : ys8.length = 8) :
    ∃ n : Nat, n < 2 ^ 63 ∧ ys8 = u64Be (W64 n) := by
  obtain ⟨w, bs, cs', z, z', hF, heq⟩ := h
  rcases hF.tag with ⟨rfl, -⟩ | ⟨ebs, rfl, -⟩ | ⟨st, mbs, rfl, -, -, hl, -⟩
  · simp at heq
  · simp only [shortBytes, List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 (by decide)
  · simp only [msgFrame, List.cons_append, List.cons.injEq, List.append_assoc] at heq
    obtain ⟨h1, -⟩ := append8_eq h8 (u64Be_length _) heq.2
    exact ⟨mbs.length, hl, h1⟩

/-- An App frame's message bytes: after the tag and the length `n`, `n` bytes are an encoding,
and the whole is the frame. -/
theorem V2Compat.app {frm to : w64} {cs : V2St} {n : Nat} {yb : List w8}
    (h : V2Compat frm to cs (W8 2 :: (u64Be (W64 n) ++ yb))) (hn : n < 2 ^ 63)
    (hl : yb.length = n) :
    ∃ st : MsgSt, MsgWireOk st yb ∧
      V2Frame frm to cs (wireOf st) (W8 2 :: msgFrame yb) ⟨st.msg.Term', lastIdx (wireOf st)⟩ := by
  obtain ⟨w, bs, cs', z, z', hF, heq⟩ := h
  rcases hF.tag with ⟨rfl, -⟩ | ⟨ebs, rfl, -⟩ | ⟨st, mbs, rfl, hw, hm, hml, hc⟩
  · simp at heq
  · simp only [shortBytes, List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 (by decide)
  · simp only [msgFrame, List.cons_append, List.cons.injEq, List.append_assoc] at heq
    obtain ⟨h8, hr⟩ := append8_eq (u64Be_length _) (u64Be_length _) heq.2
    have hnl := u64Be_len_inj hn hml h8
    obtain ⟨rfl, -⟩ := List.append_inj hr (by omega)
    subst hw hc
    exact ⟨st, hm, hF⟩

/-- An AppEntries frame's count: what the decoder reads after the tag `1`. -/
theorem V2Compat.short_count {frm to : w64} {cs : V2St} {c8 : List w8}
    (h : V2Compat frm to cs (W8 1 :: c8)) (h8 : c8.length = 8) :
    ∃ n : Nat, n < 2 ^ 63 ∧ c8 = u64Be (W64 n) := by
  obtain ⟨w, bs, cs', z, z', hF, heq⟩ := h
  rcases hF.tag with ⟨rfl, -⟩ | ⟨ebs, rfl, -, hf, hn, -⟩ | ⟨st, mbs, rfl, -⟩
  · simp at heq
  · simp only [shortBytes, List.cons_append, List.cons.injEq, List.append_assoc] at heq
    obtain ⟨h1, -⟩ := append8_eq h8 (u64Be_length _) heq.2
    exact ⟨ebs.length, by rw [← hf.length_eq]; exact hn, h1⟩
  · simp only [List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 (by decide)

/-- **An AppEntries frame read so far** (the tag, the count `n`, the entries `pre`, then `rest`):
the frame has `n` entries whose first encodings are `pre`, and `rest` is a prefix of the frame's
rest, or extends it. -/
theorem V2Compat.short {frm to : w64} {cs : V2St} {n : Nat} {pre : List (List w8)} {rest : List w8}
    (h : V2Compat frm to cs (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ rest)))
    (hn : n < 2 ^ 63) (hp : ∀ b ∈ pre, b.length < 2 ^ 63) (hl : pre.length ≤ n) :
    ∃ (ents : List EntryM) (ebs : List (List w8)) (c : w64) (z z' : List w8),
      List.Forall₂ EntEnc ents ebs ∧ ebs.length = n ∧ pre = ebs.take pre.length ∧
      rest ++ z = entFrames (ebs.drop pre.length) ++ u64Be c ++ z' ∧
      V2Frame frm to cs (shortWire frm to cs ents c) (shortBytes ebs c)
        ⟨cs.term, cs.index + W64 n⟩ := by
  obtain ⟨w, bs, cs', z, z', hF, heq⟩ := h
  rcases hF.tag with ⟨rfl, -⟩ | ⟨ebs, rfl, hw, hf, hen, hc⟩ | ⟨st, mbs, rfl, -⟩
  · simp at heq
  · simp only [shortBytes, List.cons_append, List.cons.injEq, List.append_assoc] at heq
    obtain ⟨h8, hr⟩ := append8_eq (u64Be_length _) (u64Be_length _) heq.2
    have hebsl : ebs.length < 2 ^ 63 := by rw [← hf.length_eq]; exact hen
    have hebs : ebs.length = n := (u64Be_len_inj hn hebsl h8).symm
    obtain ⟨hpre, hrest⟩ := entFrames_prefix hp (Forall₂_EntEnc_len hf) (by omega) hr
    have hlen : w.ents.length = n := by rw [hf.length_eq, hebs]
    refine ⟨w.ents, ebs, w.msg.Commit', z, z', hf, hebs, hpre, by simpa using hrest,
      Or.inr (Or.inl ⟨ebs, rfl, hf, hen, ?_, ?_⟩)⟩
    · simp only [shortBytes, shortWire, hf.length_eq]
    · simp only [shortWire, hlen]
  · simp only [List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 (by decide)

/-- The `i`-th entry of related lists is related. -/
theorem Forall₂_EntEnc_get {es : List EntryM} {ebs : List (List w8)}
    (h : List.Forall₂ EntEnc es ebs) {i : Nat} (hi : i < ebs.length) :
    ∃ e, EntEnc e ebs[i] := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hx _ ih =>
    cases i with
    | zero => exact ⟨_, hx⟩
    | succ i => exact ih (by simpa using hi)

/-- The next entry's length. -/
theorem V2Compat.short_len {frm to : w64} {cs : V2St} {n : Nat} {pre : List (List w8)}
    {s8 : List w8} (h : V2Compat frm to cs (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ s8)))
    (hn : n < 2 ^ 63) (hp : ∀ b ∈ pre, b.length < 2 ^ 63) (hi : pre.length < n)
    (h8 : s8.length = 8) : ∃ sz : Nat, sz < 2 ^ 63 ∧ s8 = u64Be (W64 sz) := by
  obtain ⟨ents, ebs, c, z, z', hf, hl, -, hr, -⟩ := h.short hn hp (by omega)
  have hlt : pre.length < ebs.length := by omega
  rw [List.drop_eq_getElem_cons hlt] at hr
  simp only [entFrames, List.append_assoc] at hr
  obtain ⟨h1, -⟩ := append8_eq h8 (u64Be_length _) hr
  exact ⟨_, Forall₂_EntEnc_len hf _ (List.getElem_mem hlt), h1⟩

/-- The next entry's encoding. -/
theorem V2Compat.short_ent {frm to : w64} {cs : V2St} {n sz : Nat} {pre : List (List w8)}
    {eb : List w8}
    (h : V2Compat frm to cs (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ (u64Be (W64 sz) ++ eb))))
    (hn : n < 2 ^ 63) (hp : ∀ b ∈ pre, b.length < 2 ^ 63) (hi : pre.length < n)
    (hsz : sz < 2 ^ 63) (hl : eb.length = sz) : ∃ e : EntryM, EntEnc e eb := by
  obtain ⟨ents, ebs, c, z, z', hf, hln, -, hr, -⟩ := h.short hn hp (by omega)
  have hlt : pre.length < ebs.length := by omega
  rw [List.drop_eq_getElem_cons hlt] at hr
  simp only [entFrames, List.append_assoc] at hr
  obtain ⟨h1, hr2⟩ := append8_eq (u64Be_length _) (u64Be_length _) hr
  have he := Forall₂_EntEnc_len hf _ (List.getElem_mem hlt)
  have hs := u64Be_len_inj hsz he h1
  obtain ⟨rfl, -⟩ := List.append_inj hr2 (by omega)
  exact Forall₂_EntEnc_get hf hlt

/-- The commit index, after all `n` entries: the whole frame, of the entries decoded. -/
theorem V2Compat.short_end {frm to : w64} {cs : V2St} {n : Nat} {pre : List (List w8)}
    {c8 : List w8} {dents : List EntryM}
    (h : V2Compat frm to cs (W8 1 :: (u64Be (W64 n) ++ entFrames pre ++ c8)))
    (hn : n < 2 ^ 63) (hp : ∀ b ∈ pre, b.length < 2 ^ 63) (hl : pre.length = n)
    (h8 : c8.length = 8) (hd : List.Forall₂ EntEnc dents pre) :
    ∃ c : w64, c8 = u64Be c ∧
      V2Frame frm to cs (shortWire frm to cs dents c) (shortBytes pre c)
        ⟨cs.term, cs.index + W64 n⟩ := by
  obtain ⟨ents, ebs, c, z, z', hf, hln, hpre, hr, hF⟩ := h.short hn hp (by omega)
  have hpe : pre = ebs := by rw [hpre, hl, ← hln, List.take_length]
  subst hpe
  rw [hl, ← hln, List.drop_length] at hr
  simp only [entFrames, List.nil_append] at hr
  obtain ⟨h1, -⟩ := append8_eq h8 (u64Be_length _) hr
  have := Forall₂_EntEnc_inj hf hd
  subst this
  exact ⟨c, h1, hF⟩

/-- The decoder's entries slice, filled one more. -/
theorem list_set_snoc_replicate {α : Type} (ps : List α) (z p : α) (k : Nat) (hk : 0 < k) :
    (ps ++ List.replicate k z).set ps.length p = (ps ++ [p]) ++ List.replicate (k - 1) z := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [List.replicate_succ, List.set_append_right]

theorem Forall₂_EntEnc_snoc {es : List EntryM} {bs : List (List w8)} {e : EntryM} {b : List w8}
    (h : List.Forall₂ EntEnc es bs) (he : EntEnc e b) :
    List.Forall₂ EntEnc (es ++ [e]) (bs ++ [b]) := by
  induction h with
  | nil => exact .cons he .nil
  | cons hx _ ih => exact .cons hx ih

theorem entFrames_snoc (bs : List (List w8)) (b : List w8) :
    entFrames (bs ++ [b]) = entFrames bs ++ (u64Be (W64 b.length) ++ b) := by
  rw [entFrames_append]; simp [entFrames]

end model

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `msgAppV2BufSize`. -/
abbrev v2BufSize : Int := 1048576

/-- **The msgappv2 encoder `enc`** writing to `wi`, with the follower stats `fs`, at the state `cs`
(exclusive): its writer and stats fixed, its state, and its three buffers, owned (the entries'
buffer `buf` of `msgAppV2BufSize` bytes, with its capacity: `MarshalAppend` writes into it). -/
def v2EncOwn (enc : Loc) (wi : GoInterfaceOk) (fs : Loc) (cs : V2St) : IProp GF :=
  iprop(∃ (buf s8 s1 : GoSlice) (zs x8 x1 : List w8),
    "#Hw" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"w"] ↦□ GoInterface.ok wi ∗
    "#Hfs" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"fs"] ↦□ fs ∗ "%Hfsnn" ∷ ⌜fs ≠ null⌝ ∗
    "Hterm" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"term"] ↦ cs.term ∗
    "Hindex" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"index"] ↦ cs.index ∗
    "#Hbuf" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"buf"] ↦□ buf ∗
    "Hbufs" ∷ buf ↦* zs ∗ "Hbufc" ∷ ownSliceCap w8 buf (DFrac.own 1) ∗
    "%Hbuflen" ∷ ⌜sint.Z buf.len = v2BufSize⌝ ∗
    "#Hs8" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"uint64buf"] ↦□ s8 ∗ "Hs8s" ∷ s8 ↦* x8 ∗ "%Hx8" ∷ ⌜x8.length = 8⌝ ∗
    "#Hs1" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder, go!"uint8buf"] ↦□ s1 ∗ "Hs1s" ∷ s1 ↦* x1 ∗ "%Hx1" ∷ ⌜x1.length = 1⌝)

/-- **The msgappv2 decoder `dec`** reading from `r`, of the connection from `frm` (its `remote`) to
`to` (its `local`), at the state `cs` (exclusive): its reader and ids fixed, its state, and its three
buffers, owned. -/
def v2DecOwn (dec : Loc) (r : GoInterface) (frm to : w64) (cs : V2St) : IProp GF :=
  iprop(∃ (buf s8 s1 : GoSlice) (zs x8 x1 : List w8),
    "#Hr" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"r"] ↦□ r ∗
    "#Hlocal" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"local"] ↦□ to ∗
    "#Hremote" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"remote"] ↦□ frm ∗
    "Hterm" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"term"] ↦ cs.term ∗
    "Hindex" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"index"] ↦ cs.index ∗
    "#Hbuf" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"buf"] ↦□ buf ∗
    "Hbufs" ∷ buf ↦* zs ∗ "Hbufc" ∷ ownSliceCap w8 buf (DFrac.own 1) ∗
    "%Hbuflen" ∷ ⌜sint.Z buf.len = v2BufSize⌝ ∗
    "#Hs8" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"uint64buf"] ↦□ s8 ∗ "Hs8s" ∷ s8 ↦* x8 ∗ "%Hx8" ∷ ⌜x8.length = 8⌝ ∗
    "#Hs1" ∷ dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder, go!"uint8buf"] ↦□ s1 ∗ "Hs1s" ∷ s1 ↦* x1 ∗ "%Hx1" ∷ ⌜x1.length = 1⌝)

/-- A message's `Entries`, taken out (the field and the slice) with what gives them back. -/
theorem msgPtsC_ents_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap st ⊢
      ∃ (es : GoSlice) (els : List Loc),
        l.[raftpb.Message, go!"Entries"] ↦{dq} es ∗ es ↦*{dqe} els ∗
        □ ([∗list] p;e ∈ els;st.ents, entRO p e) ∗
        (l.[raftpb.Message, go!"Entries"] ↦{dq} es -∗ es ↦*{dqe} els -∗ msgPtsC l dq dqe cap st) := by
  iintro H
  iunfold msgPtsC at H
  iNamed H
  iexists es, els
  iframe HEs Hes Hents
  iintro HEs Hes
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  iframe; iframe #; iframe %

/-- A buffer read into its first `sz` bytes, given back. -/
theorem ownSlice_rejoin (buf : GoSlice) (zs mid : List w8) (sz : w64)
    (hb : 0 ≤ sint.Z sz ∧ sint.Z sz ≤ sint.Z buf.len) (hmid : mid.length = sint.nat sz) :
    (slice.slice buf w8 (W64 0) (W64 0) ↦* ([] : List w8) ∗ slice.slice buf w8 (W64 0) sz ↦* mid ∗
      slice.slice buf w8 sz buf.len ↦* zs.drop (sint.nat sz) : IProp GF) ⊢
      buf ↦* (mid ++ zs.drop (sint.nat sz)) := by
  iintro ⟨H0, Hm, Hr⟩
  iapply (ownSlice_slice (V := w8) (W64 0) sz buf (DFrac.own 1) (mid ++ zs.drop (sint.nat sz))
    ⟨by decide, by simp only [show sint.Z (W64 0) = 0 from rfl]; omega, hb.2⟩).2
  have h0 : sint.nat (W64 0) = 0 := rfl
  simp only [h0, List.take_zero, subslice, List.drop_zero, List.take_left' hmid, List.drop_left' hmid]
  iframe

/-- A slice that `MarshalAppend` returned within `buf[:0]`'s capacity, resliced to `buf`'s length,
is `buf`. -/
theorem slice_back {buf b' : GoSlice} (hptr : b'.ptr = (slice.slice buf w8 (W64 0) (W64 0)).ptr)
    (hcap : b'.cap = (slice.slice buf w8 (W64 0) (W64 0)).cap) :
    slice.slice b' w8 (W64 0) buf.len = buf := by
  obtain ⟨bp, bl, bc⟩ := buf
  obtain ⟨p', l', c'⟩ := b'
  simp only [slice.slice, sliceIndexRef] at hptr hcap ⊢
  subst hptr hcap
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
  congr 1 <;> word

/-- A frozen message's `Entries`: the field, its slice and the entries, read-only. -/
theorem msgOwn_ents (ml : Loc) (st : MsgSt) :
    msgOwn (GF := GF) ml DFrac.discard st ⊢
      ∃ (es : GoSlice) (els : List Loc),
        ml.[raftpb.Message, go!"Entries"] ↦□ es ∗ es ↦*□ els ∗
        [∗list] p;e ∈ els;st.ents, entRO p e := by
  iintro H
  iunfold msgOwn at H
  iunfold msgPts at H
  iunfold msgPtsC at H
  iNamed H
  iexists es, els
  iframe
  iexact Hents

/-- The encodings of a message's entries (`pbEnc` of each, `pbEnc_ok`) are encodings of them. -/
theorem ents_enc (els : List Loc) (ents : List EntryM) :
    ([∗list] p;e ∈ els;ents, entRO (GF := GF) p e) ⊢
      ⌜List.Forall₂ EntEnc ents (els.map (pbEnc raftpb.Entry.ty))⌝ := by
  induction els generalizing ents with
  | nil =>
    iintro H
    ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H
    subst h
    ipureintro; exact .nil
  | cons p ps ih =>
    iintro H
    icases (BigSepL2.bigSepL2_cons_inv_left).1 $$ H with ⟨%e, %es, %heq, He, Hr⟩
    subst heq
    have Hpe := pbEnc_ok (pbEntry (GF := GF)) p e
    simp only [pbEntry_ro, pbEntry_marshals, pbEntry_wire, pbEntry_ty] at Hpe
    ihave %h1 := Hpe $$ He
    ihave %h2 := ih es $$ Hr
    ipureintro
    exact .cons ⟨h1.1 trivial, h1.2⟩ h2

end preds

section make
open Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `make([]byte, len)`, its zero bytes abstracted (so that no proof term holds a concrete list of
`msgAppV2BufSize` bytes, which the kernel would unfold). -/
theorem wp_make_bytes_abs (len : w64) (h : 0 ≤ sint.Z len) :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.GoType.SliceType go.byte])) (Val #len))
    {{ (sl : GoSlice), RET #sl; ∃ zs : List w8, sl ↦* zs ∗ ownSliceCap w8 sl (DFrac.own 1) ∗
        ⌜zs.length = sint.nat len⌝ }} := by
  wp_start as -
  wp_apply (wp_slice_make3 (V := w8) len len ⟨h, Int.le_refl _⟩) as %sl ⟨Hs, Hc, -⟩
  iapply HΦ
  iexists _
  iframe
  ipureintro
  simp

end make

end EtcdGrove
end Perennial
