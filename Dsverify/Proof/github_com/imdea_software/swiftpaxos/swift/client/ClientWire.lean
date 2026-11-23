/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/ClientWire.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client's streams decode uniquely (pure; `Spec/swift/Wire.lean`'s formats): what the
client's readers (`RegisterRPCTable`'s goroutines) need to tie a message they decoded to the
message the replica's stream protocol (`sp.outQ`, `framesProto`) lists at that position.

A replica writes to client `cl` only `MReply`, `MFastAckClient` and `MLightSlowAck` frames of
`cl`'s commands (`Msg.isToClient`); their checksums' hashes have 32 bytes (`cMsg`: from the
witnesses, `ClientStream.lean`). For these, frames are a prefix-free injective encoding
(`frame_peel`) with no bound on the lengths: a varint (`uvarint`) is prefix-free and injective
on all naturals. The readers' decoder accepts more than the encoder writes (non-minimal
varints), but on a stream of frames each varint it accepts is the frame's own
(`uvTerm_peel`), and `readUvarint` bounds its value below `2 ^ 64`
(`Varint.lean`), so the counts are exact.

* `stOk cl R`: `R` is a prefix of the frames of some client messages of `cl` (the pure part of
  what the protocol says of a stream to `cl`);
* `next_prefix`: after the frames of `done`, a non-empty `P` read is a prefix of the next
  message's frame (and more);
* `frames_next`: after the frames of `done`, the frame of a client message `m`: the stream's
  messages continue `done` with `m`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.VarintPure
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp.cw

/-- Every hash has 32 bytes. -/
def hashOk (hs : List Hash) : Prop := ∀ h ∈ hs, h.length = 32

/-- A client message (`MReply`, `MFastAckClient`, `MLightSlowAck`) with 32-byte hashes (and,
for a reply, a non-empty checksum: it ends with the dependency hash). -/
def cKind : Msg → Prop
  | .reply _ _ _ cs _ => hashOk cs ∧ cs ≠ []
  | .fastAckClient _ _ _ cs => hashOk cs
  | .lightSlowAck _ => True
  | _ => False

/-- A message to client `cl` as the replicas write it. -/
def cMsg (cl : w32) (m : Msg) : Prop := sp.Msg.isToClient cl m ∧ cKind m

/-- The pure part of a stream to client `cl`: a prefix of the frames of client messages. -/
def stOk (cl : w32) (R : List w8) : Prop :=
  ∃ ms : List Msg, R <+: framesOf ms ∧ ∀ m ∈ ms, cMsg cl m

/-! ## Peeling -/

theorem le32_peel {a b : w32} {x y : List w8} (h : le32 a ++ x = le32 b ++ y) :
    a = b ∧ x = y := by
  have := List.append_inj h (by simp [le32, u32Le_length])
  exact ⟨u32Le_inj this.1, this.2⟩

theorem cmdId_peel {a b : CmdId} {x y : List w8} (h : encCmdId a ++ x = encCmdId b ++ y) :
    a = b ∧ x = y := by
  unfold encCmdId at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := le32_peel h
  obtain ⟨h2, h⟩ := le32_peel h
  cases a; cases b; simp_all

/-- Terminated byte strings (continuation bytes, then a last byte) are prefix-free. -/
theorem term_peel (p1 p2 : List w8) (c1 c2 : w8) (x y : List w8)
    (hp1 : ∀ b ∈ p1, 128 ≤ b.toNat) (hc1 : c1.toNat < 128)
    (hp2 : ∀ b ∈ p2, 128 ≤ b.toNat) (hc2 : c2.toNat < 128)
    (h : p1 ++ [c1] ++ x = p2 ++ [c2] ++ y) : p1 = p2 ∧ c1 = c2 ∧ x = y := by
  induction p1 generalizing p2 with
  | nil =>
    cases p2 with
    | nil => simpa using h
    | cons b p2 =>
      simp at h; have := hp2 b (by simp); rw [← h.1] at this; omega
  | cons a p1 ih =>
    cases p2 with
    | nil =>
      simp at h; have := hp1 a (by simp); rw [h.1] at this; omega
    | cons b p2 =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, h⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih p2 (fun z hz => hp1 z (List.mem_cons_of_mem _ hz))
        (fun z hz => hp2 z (List.mem_cons_of_mem _ hz)) (by simpa using h)
      exact ⟨by rw [hab, h1], h2, h3⟩

/-- `uvarint` is prefix-free and injective (any naturals). -/
theorem uvarint_peel {a b : Nat} {x y : List w8} (h : uvarint a ++ x = uvarint b ++ y) :
    a = b ∧ x = y := by
  obtain ⟨p1, c1, e1, hp1, hc1, d1⟩ := uvarint_shape a
  obtain ⟨p2, c2, e2, hp2, hc2, d2⟩ := uvarint_shape b
  rw [e1, e2] at h
  obtain ⟨hp, hc, hxy⟩ := term_peel p1 p2 c1 c2 x y hp1 hc1 hp2 hc2 h
  refine ⟨?_, hxy⟩
  rw [← d1, ← d2, e1, e2, hp, hc]

/-- An accepted varint (`uvTerm`) before a `uvarint`: the same bytes. -/
theorem uvTerm_peel {d : List w8} {b : Nat} {x y : List w8} (hd : uvTerm d)
    (h : d ++ x = uvarint b ++ y) : d = uvarint b ∧ x = y := by
  obtain ⟨p1, c1, rfl, hp1, hc1, -⟩ := hd
  obtain ⟨p2, c2, e2, hp2, hc2, -⟩ := uvarint_shape b
  rw [e2] at h ⊢
  obtain ⟨hp, hc, hxy⟩ := term_peel p1 p2 c1 c2 x y hp1 hc1 hp2 hc2 h
  exact ⟨by rw [hp, hc], hxy⟩

theorem uvDec_uvarint (n : Nat) : uvDec (uvarint n) = n := by
  obtain ⟨-, -, -, -, -, h⟩ := uvarint_shape n; exact h

theorem varintLen_peel {a b : Nat} {x y : List w8} (h : varintLen a ++ x = varintLen b ++ y) :
    a = b ∧ x = y := by
  unfold varintLen at h
  obtain ⟨h1, h2⟩ := uvarint_peel h
  exact ⟨by omega, h2⟩

/-- Lists of 32-byte hashes of the same count, concatenated. -/
theorem flat_peel {a b : List Hash} {x y : List w8} (ha : hashOk a) (hb : hashOk b)
    (hl : a.length = b.length) (h : a.flatten ++ x = b.flatten ++ y) : a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons _ _ => simp at hl
  | cons h1 a ih =>
    cases b with
    | nil => simp at hl
    | cons h2 b =>
      simp only [List.flatten_cons, List.append_assoc] at h
      have hl1 : h1.length = h2.length := by
        rw [ha h1 (by simp), hb h2 (by simp)]
      obtain ⟨e1, h⟩ := List.append_inj h hl1
      obtain ⟨e2, e3⟩ := ih (fun z hz => ha z (List.mem_cons_of_mem _ hz))
        (fun z hz => hb z (List.mem_cons_of_mem _ hz)) (by simpa using hl) h
      exact ⟨by rw [e1, e2], e3⟩

theorem hashes_peel {a b : List Hash} {x y : List w8} (ha : hashOk a) (hb : hashOk b)
    (h : encHashes a ++ x = encHashes b ++ y) : a = b ∧ x = y := by
  unfold encHashes at h
  simp only [List.append_assoc] at h
  obtain ⟨hl, h⟩ := varintLen_peel h
  exact flat_peel ha hb hl h

theorem bytes_peel {a b : List w8} {x y : List w8} (h : encBytes a ++ x = encBytes b ++ y) :
    a = b ∧ x = y := by
  unfold encBytes at h
  simp only [List.append_assoc] at h
  obtain ⟨hl, h⟩ := varintLen_peel h
  exact List.append_inj h hl

/-- **Frames of client messages are prefix-free and injective.** -/
theorem frame_peel' {a b : Msg} {x y : List w8} (wa : cKind a) (wb : cKind b)
    (h : a.frame ++ x = b.frame ++ y) : a = b ∧ x = y := by
  simp only [Msg.frame, List.cons_append, List.cons.injEq] at h
  obtain ⟨hc, h⟩ := h
  cases a <;> simp only [cKind] at wa <;> cases b <;> simp only [cKind] at wb <;>
    (try (exfalso; simp [Msg.code, rpcTable] at hc; done)) <;> simp only [Msg.body] at h
  · -- fastAckClient
    simp only [List.append_assoc] at h
    obtain ⟨e1, h1⟩ := le32_peel h
    obtain ⟨e2, h2⟩ := le32_peel h1
    obtain ⟨e3, h3⟩ := cmdId_peel h2
    obtain ⟨e4, h4⟩ := hashes_peel wa wb h3
    subst e1 e2 e3 e4; exact ⟨rfl, h4⟩
  · -- lightSlowAck
    rename_i s1 s2
    simp only [SlowAck.enc, List.append_assoc] at h
    obtain ⟨e1, h⟩ := le32_peel h
    obtain ⟨e2, h⟩ := le32_peel h
    obtain ⟨e3, h⟩ := cmdId_peel h
    cases s1; cases s2; simp_all
  · -- reply
    simp only [List.append_assoc] at h
    obtain ⟨e1, h1⟩ := le32_peel h
    obtain ⟨e2, h2⟩ := le32_peel h1
    obtain ⟨e3, h3⟩ := cmdId_peel h2
    obtain ⟨e4, h4⟩ := hashes_peel wa.1 wb.1 h3
    obtain ⟨e5, h5⟩ := bytes_peel h4
    subst e1 e2 e3 e4 e5; exact ⟨rfl, h5⟩

theorem frame_peel {cl : w32} {a b : Msg} {x y : List w8} (ha : cMsg cl a) (hb : cMsg cl b)
    (h : a.frame ++ x = b.frame ++ y) : a = b ∧ x = y := frame_peel' ha.2 hb.2 h

/-! ## Streams -/

/-- After the frames of `done`, a non-empty `P`: a prefix of the next message's frame, then
more. -/
theorem next_prefix {cl : w32} {done : List Msg} {P : List w8} (hd : ∀ d ∈ done, cMsg cl d)
    (hP : P ≠ []) (h : stOk cl (framesOf done ++ P)) :
    ∃ b rest, cMsg cl b ∧ (∀ m ∈ rest, cMsg cl m) ∧ P <+: b.frame ++ framesOf rest := by
  obtain ⟨ms, ⟨u, hu⟩, hms⟩ := h
  induction done generalizing ms with
  | nil =>
    cases ms with
    | nil => simp [framesOf] at hu; exact absurd hu.1 hP
    | cons b ms =>
      refine ⟨b, ms, hms b (by simp), fun m hm => hms m (List.mem_cons_of_mem _ hm), u, ?_⟩
      simpa [framesOf] using hu
  | cons d done ih =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at hu
    | cons b ms =>
      simp only [framesOf, List.map_cons, List.flatten_cons, List.append_assoc] at hu
      obtain ⟨-, h2⟩ := frame_peel (hd d (by simp)) (hms b (by simp)) hu
      exact ih (fun z hz => hd z (List.mem_cons_of_mem _ hz)) ms
        (fun z hz => hms z (List.mem_cons_of_mem _ hz))
        (by simpa [framesOf, List.append_assoc] using h2)

/-- After the frames of `done`, the frame of a client message `m` (its hashes of 32 bytes):
the next message is `m`, a client message. -/
theorem frames_next {cl : w32} {done : List Msg} {m : Msg} (hd : ∀ d ∈ done, cMsg cl d)
    (hm : cKind m) (h : stOk cl (framesOf done ++ m.frame)) : cMsg cl m := by
  obtain ⟨b, rest, hb, -, u, hu⟩ := next_prefix hd (by simp [Msg.frame]) h
  obtain ⟨rfl, -⟩ := frame_peel' hm hb.2 (by simpa using hu)
  exact hb

/-- The stream after the frames of `done` and the frame of `m`: `m` is the next message in
any list of client messages whose frames the stream is a prefix of. -/
theorem frames_align {cl : w32} {done ms : List Msg} {m : Msg} (hd : ∀ d ∈ done, cMsg cl d)
    (hm : cMsg cl m) (hms : ∀ x ∈ ms, cMsg cl x) (h : framesOf done ++ m.frame <+: framesOf ms) :
    ∃ rest, ms = done ++ m :: rest := by
  obtain ⟨u, hu⟩ := h
  induction done generalizing ms with
  | nil =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at hu
    | cons b ms =>
      simp only [framesOf, List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons, List.append_assoc] at hu
      obtain ⟨rfl, -⟩ := frame_peel hm (hms b (by simp)) hu
      exact ⟨ms, rfl⟩
  | cons d done ih =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at hu
    | cons b ms =>
      simp only [framesOf, List.map_cons, List.flatten_cons, List.append_assoc] at hu
      obtain ⟨rfl, h2⟩ := frame_peel (hd d (by simp)) (hms b (by simp)) hu
      obtain ⟨rest, hr⟩ := ih (fun z hz => hd z (List.mem_cons_of_mem _ hz))
        (fun z hz => hms z (List.mem_cons_of_mem _ hz))
        (by simp only [framesOf, List.append_assoc] at h2 ⊢; exact h2)
      exact ⟨rest, by rw [hr]; rfl⟩

/-! ## The readers' varints -/

/-- The 16 header bytes of an `MFastAckClient` or `MReply` (replica, ballot, command id). -/
def hdr16 (r b : w32) (x : CmdId) : List w8 := le32 r ++ le32 b ++ encCmdId x

theorem hdr16_length (r b : w32) (x : CmdId) : (hdr16 r b x).length = 16 := by
  simp [hdr16, le32, encCmdId, u32Le_length]

/-- The first varint of an `MFastAckClient` (type byte 10) or `MReply` (15): the frame's own. -/
theorem next_v1 {cl : w32} {done : List Msg} {c : w8} {hdr d1 : List w8}
    (hd : ∀ d ∈ done, cMsg cl d) (hc : c = W8 10 ∨ c = W8 15) (hl : hdr.length = 16)
    (ht : uvTerm d1) (h : stOk cl (framesOf done ++ (c :: (hdr ++ d1)))) :
    ∃ n, d1 = varintLen n ∧ (c = W8 15 → 0 < n) := by
  obtain ⟨b, rest, hb, -, u, hu⟩ := next_prefix hd (by simp) h
  obtain ⟨-, wb⟩ := hb
  cases b <;> simp only [cKind] at wb <;>
    simp only [Msg.frame, Msg.body, List.cons_append, List.cons.injEq] at hu <;>
    obtain ⟨hc', hu⟩ := hu
  · rename_i r bb x cs
    have e : hdr ++ (d1 ++ u) = hdr16 r bb x ++ (encHashes cs ++ framesOf rest) := by
      simpa [hdr16, List.append_assoc] using hu
    obtain ⟨-, e2⟩ := List.append_inj e (by rw [hl, hdr16_length])
    unfold encHashes varintLen at e2
    rw [List.append_assoc] at e2
    refine ⟨cs.length, (uvTerm_peel ht e2).1, fun h15 => ?_⟩
    exfalso; rw [h15] at hc'; simp [Msg.code, rpcTable] at hc'
  · exfalso; rcases hc with rfl | rfl <;> simp [Msg.code, rpcTable] at hc'
  · rename_i r bb x cs v
    have e : hdr ++ (d1 ++ u) = hdr16 r bb x ++ (encHashes cs ++ (encBytes v ++ framesOf rest)) := by
      simpa [hdr16, List.append_assoc] using hu
    obtain ⟨-, e2⟩ := List.append_inj e (by rw [hl, hdr16_length])
    unfold encHashes varintLen at e2
    rw [List.append_assoc] at e2
    exact ⟨cs.length, (uvTerm_peel ht e2).1, fun _ => List.length_pos_iff.2 wb.2⟩

/-- The second varint of an `MReply` (type byte 15), after its hashes: the frame's own. -/
theorem next_v2 {cl : w32} {done : List Msg} {hdr d2 : List w8} {hs : List Hash}
    (hd : ∀ d ∈ done, cMsg cl d) (hl : hdr.length = 16) (hh : hashOk hs)
    (ht : uvTerm d2) (h : stOk cl (framesOf done ++
      (W8 15 :: (hdr ++ (varintLen hs.length ++ (hs.flatten ++ d2)))))) :
    ∃ n, d2 = varintLen n := by
  obtain ⟨b, rest, hb, -, u, hu⟩ := next_prefix hd (by simp) h
  obtain ⟨-, wb⟩ := hb
  cases b <;> simp only [cKind] at wb <;>
    simp only [Msg.frame, Msg.body, List.cons_append, List.cons.injEq] at hu <;>
    obtain ⟨hc', hu⟩ := hu <;>
    (try (exfalso; simp [Msg.code, rpcTable] at hc'; done))
  rename_i r bb x cs v
  have e : hdr ++ (varintLen hs.length ++ (hs.flatten ++ (d2 ++ u))) =
      hdr16 r bb x ++ (varintLen cs.length ++ (cs.flatten ++ (uvarint (2 * v.length) ++
        (v ++ framesOf rest)))) := by
    simpa [hdr16, encHashes, encBytes, varintLen, List.append_assoc] using hu
  obtain ⟨-, e2⟩ := List.append_inj e (by rw [hl, hdr16_length])
  obtain ⟨hl2, e3⟩ := varintLen_peel e2
  obtain ⟨-, e4⟩ := flat_peel hh wb.1 hl2 e3
  exact ⟨v.length, (uvTerm_peel ht e4).1⟩

/-- The type byte after the frames of `done`: a client message's (`MFastAckClient` 10,
`MLightSlowAck` 12, `MReply` 15). -/
theorem next_code {cl : w32} {done : List Msg} {c : w8} (hd : ∀ d ∈ done, cMsg cl d)
    (h : stOk cl (framesOf done ++ [c])) : c = W8 10 ∨ c = W8 12 ∨ c = W8 15 := by
  obtain ⟨b, rest, hb, -, u, hu⟩ := next_prefix hd (by simp) h
  obtain ⟨-, wb⟩ := hb
  cases b <;> simp only [cKind] at wb <;>
    simp only [Msg.frame, List.cons_append, List.singleton_append, List.cons.injEq] at hu <;>
    obtain ⟨hc, -⟩ := hu <;> subst hc <;> simp [Msg.code, rpcTable]

end sp.cw

end Perennial.github_com.imdea_software.swiftpaxos
