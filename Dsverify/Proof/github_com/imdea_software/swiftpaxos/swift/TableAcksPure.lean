/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableAcksPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The stream laws of `MAcks` (13) and `MOptAcks` (14) (pure): each varint the decoder accepts is
the message's own count, and each element decoder reads under its element's law
(`fastAckNext`, `ackNext`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableLaw

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace swift.tbl

open sp in
/-- After the encodings of the well-formed `xs`, fewer than the well-formed `ys` whose
encodings (then more) the bytes are a prefix of: the next bytes are a prefix of an element's
encoding (then more). -/
theorem elems_next {α : Type} {wf : α → Prop} {enc : α → List w8} (hpf : PF wf enc) :
    ∀ (xs ys : List α) (d u w : List w8), (∀ x ∈ xs, wf x) → (∀ y ∈ ys, wf y) →
      xs.length < ys.length → (xs.map enc).flatten ++ d ++ u = (ys.map enc).flatten ++ w →
      ∃ (y : α) (w' : List w8), wf y ∧ d <+: enc y ++ w'
  | [], y :: ys, d, u, w, _, hy, _, h => by
    refine ⟨y, (ys.map enc).flatten ++ w, hy y (by simp), u, ?_⟩
    simpa [List.append_assoc] using h
  | x :: xs, y :: ys, d, u, w, hx, hy, hl, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨-, h'⟩ := hpf.peel (hx x (by simp)) (hy y (by simp)) h
    exact elems_next hpf xs ys d u w (fun z hz => hx z (by simp [hz]))
      (fun z hz => hy z (by simp [hz])) (by simpa using hl) (by simpa [List.append_assoc] using h')
  | _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | [], [], _, _, _, _, _, hl, _ => by simp at hl

theorem acks_of_next {d : List w8} (h : sp.nextOk (W8 13) d) :
    ∃ (fs : List sp.FastAck) (ss : List sp.SlowAck) (w : List w8), (sp.Msg.acks fs ss).wf ∧
      d <+: (sp.Msg.acks fs ss).body ++ w := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  exact ⟨_, _, w, hw, hp⟩

theorem optAcks_of_next {d : List w8} (h : sp.nextOk (W8 14) d) :
    ∃ (r b : w32) (al : List sp.Ack) (w : List w8), (sp.Msg.optAcks r b al).wf ∧
      d <+: (sp.Msg.optAcks r b al).body ++ w := by
  obtain ⟨m, w, hw, -, hc, hp⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  exact ⟨_, _, _, w, hw, hp⟩

/-! ## `MAcks` -/

theorem acks_v1 {d : List w8} (ht : sp.uvTerm d) (h : sp.nextOk (W8 13) d) :
    ∃ n, d = sp.varintLen n ∧ n < 2 ^ 62 := by
  obtain ⟨fs, ss, w, hw, hp⟩ := acks_of_next h
  refine ⟨fs.length, ?_, hw.1.1⟩
  apply uv_count (X := []) ht
  simpa [sp.Msg.body, List.append_assoc] using hp

theorem acks_elem {n : Nat} {prev : List sp.FastAck} {d : List w8}
    (hp : ∀ f ∈ prev, f.wf) (hl : prev.length < n)
    (h : sp.nextOk (W8 13) (sp.varintLen n ++ (prev.map sp.FastAck.enc).flatten ++ d)) :
    fastAckNext d := by
  obtain ⟨fs, ss, w, hw, u, hu⟩ := acks_of_next h
  simp only [sp.Msg.body, List.append_assoc] at hu
  obtain ⟨hn, hu⟩ := sp.cw.varintLen_peel hu
  subst hn
  obtain ⟨y, w', hy, hd⟩ := elems_next sp.pf_fastAck prev fs d u _ hp hw.1.2 hl
    (by simpa [List.append_assoc] using hu)
  exact ⟨y, w', hy, hd⟩

theorem acks_v2 {n : Nat} {fs : List sp.FastAck} {d : List w8} (ht : sp.uvTerm d)
    (hp : ∀ f ∈ fs, f.wf) (hl : fs.length = n)
    (h : sp.nextOk (W8 13) (sp.varintLen n ++ (fs.map sp.FastAck.enc).flatten ++ d)) :
    ∃ k, d = sp.varintLen k ∧ k < 2 ^ 62 ∧ n < 2 ^ 62 := by
  obtain ⟨fs', ss, w, hw, u, hu⟩ := acks_of_next h
  simp only [sp.Msg.body, List.append_assoc] at hu
  obtain ⟨hn, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨rfl, hu⟩ := sp.elems_peel sp.pf_fastAck fs fs' _ _ (by omega) hp hw.1.2 hu
  have := hw.1.1
  refine ⟨ss.length, ?_, hw.2, by omega⟩
  apply uv_count (X := []) ht
  exact ⟨u, by simpa [List.append_assoc] using hu⟩

/-! ## `MOptAcks` -/

/-- The 8 header bytes of an `MOptAcks` (replica, ballot). -/
theorem optAcks_v1 {hdr d : List w8} (hl : hdr.length = 8) (ht : sp.uvTerm d)
    (h : sp.nextOk (W8 14) (hdr ++ d)) : ∃ n, d = sp.varintLen n ∧ n < 2 ^ 62 := by
  obtain ⟨r, b, al, w, hw, u, hu⟩ := optAcks_of_next h
  simp only [sp.Msg.body, List.append_assoc] at hu
  rw [← List.append_assoc (sp.le32 r)] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl]; simp [sp.le32, u32Le_length])
  refine ⟨al.length, ?_, hw.1⟩
  apply uv_count (X := []) ht
  exact ⟨u, by simpa [List.append_assoc] using hu⟩

theorem optAcks_elem {hdr : List w8} {n : Nat} {prev : List sp.Ack} {d : List w8}
    (hl8 : hdr.length = 8) (hp : ∀ a ∈ prev, a.wf) (hl : prev.length < n)
    (h : sp.nextOk (W8 14) (hdr ++ sp.varintLen n ++ (prev.map sp.Ack.enc).flatten ++ d)) :
    ackNext d := by
  obtain ⟨r, b, al, w, hw, u, hu⟩ := optAcks_of_next h
  simp only [sp.Msg.body, List.append_assoc] at hu
  rw [← List.append_assoc (sp.le32 r)] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl8]; simp [sp.le32, u32Le_length])
  obtain ⟨hn, hu⟩ := sp.cw.varintLen_peel hu
  subst hn
  obtain ⟨y, w', hy, hd⟩ := elems_next sp.pf_ack prev al d u _ hp hw.2 hl
    (by simpa [List.append_assoc] using hu)
  exact ⟨y, w', hy, hd⟩

theorem optAcks_end {hdr : List w8} {n : Nat} {al : List sp.Ack}
    (hl8 : hdr.length = 8) (hp : ∀ a ∈ al, a.wf) (hl : al.length = n)
    (h : sp.nextOk (W8 14) (hdr ++ sp.varintLen n ++ (al.map sp.Ack.enc).flatten)) :
    n < 2 ^ 62 := by
  obtain ⟨r, b, al', w, hw, u, hu⟩ := optAcks_of_next h
  simp only [sp.Msg.body, List.append_assoc] at hu
  rw [← List.append_assoc (sp.le32 r)] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl8]; simp [sp.le32, u32Le_length])
  obtain ⟨hn, -⟩ := sp.cw.varintLen_peel hu
  have := hw.1; omega

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
