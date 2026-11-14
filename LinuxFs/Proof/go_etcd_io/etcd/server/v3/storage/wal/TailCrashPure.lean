/- Lean-first (no Rocq counterpart).

# The tail's crash after appends (W6, pure; `notes/wal-fsext-plan.md`, §2.4, §2.5, "W6 implementation log")

**The append's crash condition, its decoding core.** After this generation appended to the WAL's last
segment, a crash may keep, of each byte of the tail, any of its candidates. What the reader of the
crashed tail then reads is a prefix of the tail's intended records, at least those below the synced
offset, ending at a record the reader rejects (`tail_decode`). The facts it rests on:

* **the candidates** (`TailCands`, of the intended stream `X`, the bytes under it `Y`, the synced
  offset `so`, the end of the frames found at the generation's start `z0`): below `so`, the one
  durable candidate `X b`; above it, the byte under it `Y b` stamped 0, then candidates of `X b`
  stamped by the writes that announced it (`ByteOk`'s unsynced case); `Y` is `X` below `z0` (the
  frames found) and zero from `z0` on (F-Z, the preallocation: plan §2.4 item 2);
* **the boundary**: `max so z0` ends a record of the intended records (a sync is issued after a
  flush, at the end of the records encoded; `z0` is where the frames found end);
* **W1** (`AsOf`, `W1G`'s form, `Abs.lean`): every frame the reader accepts has its core as of the
  last sync (each byte its candidate stamped 0) or as of one change `n > 0` by which each of its
  bytes was announced.

Then a frame the reader accepts at a record boundary is the intended frame there: as of one change,
its core is the intended bytes (every candidate stamped after the sync is the intended byte); as of
the sync, its core is the intended bytes below `max so z0` and zeros above it, whose length word,
zero, the reader rejects. The padding is the intended zeros, since the bytes under the stream past
`z0` are zeros (`tail_frame_match`). This is the "no collision" the encoding layer's prefix lemma
asks for (`NoCollisionFrom`), along the reader's path only: W1 speaks of the frames the reader
accepts.

The candidates past the file's size (a write past the preallocated size, the `Save` crossing
`SegmentSizeBytes`) are of the same form when the layout grows `Y` with zeros (`OsMeta.pc`'s
zero candidates, plan §11's decision): this lemma does not look at the size.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

/-! ## Candidates -/

section cands

/-- **The candidates of the tail's bytes** (see the file header): the intended stream `X`, the bytes
under it `Y`, the synced offset `so`, the end `z0` of the frames found at the generation's start. -/
structure TailCands (X Y : Nat → w8) (cs : Nat → Cands) (so z0 : Nat) : Prop where
  synced : ∀ b, b < so → cs b = [(X b, 0)]
  unsynced : ∀ b, so ≤ b → ∃ ex : Cands, cs b = (Y b, 0) :: ex ∧ ∀ q ∈ ex, q.1 = X b ∧ 0 < q.2
  old_lo : ∀ b, b < z0 → Y b = X b
  old_hi : ∀ b, z0 ≤ b → Y b = 0

/-- **W1 of a frame core** (`AsOfOneG`'s form over a candidate function): the image bytes `img` of
`[o, o + len)` are each byte's candidate as of the last sync, or each byte's as of one change `n`
by which every one of them was announced. -/
def AsOf (cs : Nat → Cands) (img : List w8) (o len : Nat) : Prop :=
  (∀ b, o ≤ b → b < o + len → img.getD b 0 = valAt (cs b) 0) ∨
  ∃ n, 0 < n ∧ ∀ b, o ≤ b → b < o + len →
    img.getD b 0 = valAt (cs b) n ∧ ∃ q ∈ cs b, 0 < q.2 ∧ q.2 ≤ n

theorem asOfOneG_asOf {bs : List ByteG} {img : List w8} {o len : Nat} (h : AsOfOneG bs img o len) :
    AsOf (fun b => (bs.getD b (0, [])).2) img o len := AsOfW.weak h

theorem valAt_single (x : w8) (n : Nat) : valAt [(x, 0)] n = x := by
  simp [valAt]

theorem valAt_head_zero {y : w8} {ex : Cands} (hex : ∀ q ∈ ex, 0 < q.2) :
    valAt ((y, 0) :: ex) 0 = y := by
  have h : ex.filter (fun q => decide (q.2 ≤ 0)) = [] := by
    rw [List.filter_eq_nil_iff]; intro q hq; have := hex q hq; simp; omega
  unfold valAt
  rw [List.filter_cons_of_pos (by simp), h]
  rfl

theorem valAt_ex {y x : w8} {ex : Cands} {n : Nat} (hex : ∀ q ∈ ex, q.1 = x ∧ 0 < q.2)
    (hq : ∃ q ∈ (y, 0) :: ex, 0 < q.2 ∧ q.2 ≤ n) : valAt ((y, 0) :: ex) n = x := by
  obtain ⟨q, hqm, hq0, hqn⟩ := hq
  have hqex : q ∈ ex := by
    rcases List.mem_cons.1 hqm with rfl | h
    · simp at hq0
    · exact h
  have hne : ex.filter (fun q => decide (q.2 ≤ n)) ≠ [] := by
    intro h; rw [List.filter_eq_nil_iff] at h; exact h q hqex (by simpa using hqn)
  obtain ⟨z, hz⟩ : ∃ z, (ex.filter (fun q => decide (q.2 ≤ n))).getLast? = some z := by
    cases h : (ex.filter (fun q => decide (q.2 ≤ n))).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some z => exact ⟨z, rfl⟩
  have hzm : z ∈ ex := (List.mem_filter.1 (List.mem_of_getLast? hz)).1
  have e : ((y, 0) :: ex).filter (fun q => decide (q.2 ≤ n)) =
      (y, 0) :: ex.filter (fun q => decide (q.2 ≤ n)) := by
    simp [List.filter_cons]
  unfold valAt
  rw [e, List.getLast?_cons, hz]
  simp [(hex z hzm).1]

variable {X Y : Nat → w8} {cs : Nat → Cands} {so z0 : Nat}

/-- A byte's value as of the last sync: the intended byte below `max so z0`, zero above. -/
theorem TailCands.val0 (h : TailCands X Y cs so z0) (b : Nat) :
    valAt (cs b) 0 = if b < max so z0 then X b else 0 := by
  by_cases hb : b < so
  · rw [h.synced b hb, valAt_single, if_pos (by omega)]
  · obtain ⟨ex, he, hex⟩ := h.unsynced b (by omega)
    rw [he, valAt_head_zero (fun q hq => (hex q hq).2)]
    by_cases hz : b < z0
    · rw [h.old_lo b hz, if_pos (by omega)]
    · rw [h.old_hi b (by omega), if_neg (by omega)]

/-- A byte's value as of a change that announced it: the intended byte. -/
theorem TailCands.valn (h : TailCands X Y cs so z0) {b n : Nat}
    (hq : ∃ q ∈ cs b, 0 < q.2 ∧ q.2 ≤ n) : valAt (cs b) n = X b := by
  by_cases hb : b < so
  · rw [h.synced b hb] at hq
    obtain ⟨q, hq, h0, -⟩ := hq
    rw [List.mem_singleton] at hq; subst hq; simp at h0
  · obtain ⟨ex, he, hex⟩ := h.unsynced b (by omega)
    rw [he] at hq ⊢; exact valAt_ex hex hq

/-- **A crash keeps of a byte the intended byte, or (past `max so z0`) a zero.** -/
theorem TailCands.mem_val (h : TailCands X Y cs so z0) {b : Nat} {v : w8} {s : Nat}
    (hm : (v, s) ∈ cs b) : v = X b ∨ (max so z0 ≤ b ∧ v = 0) := by
  by_cases hb : b < so
  · rw [h.synced b hb, List.mem_singleton] at hm
    exact Or.inl (Prod.mk.inj hm).1
  · obtain ⟨ex, he, hex⟩ := h.unsynced b (by omega)
    rw [he] at hm
    rcases List.mem_cons.1 hm with hm | hm
    · have hv : v = Y b := (Prod.mk.inj hm).1
      by_cases hz : b < z0
      · exact Or.inl (hv.trans (h.old_lo b hz))
      · exact Or.inr ⟨by omega, hv.trans (h.old_hi b (by omega))⟩
    · exact Or.inl (hex _ hm).1

/-- What a core `AsOf` says, over these candidates. -/
theorem TailCands.asOf (h : TailCands X Y cs so z0) {img : List w8} {o len : Nat}
    (ha : AsOf cs img o len) :
    (∀ b, o ≤ b → b < o + len → img.getD b 0 = if b < max so z0 then X b else 0) ∨
    (∀ b, o ≤ b → b < o + len → img.getD b 0 = X b) := by
  rcases ha with ha | ⟨n, -, ha⟩
  · left; intro b h1 h2; rw [ha b h1 h2, h.val0]
  · right; intro b h1 h2
    obtain ⟨e, hq⟩ := ha b h1 h2
    rw [e, h.valn hq]

end cands

/-! ## Frames at record boundaries -/

section frames

theorem recFrames_take_mono (C : WalCodec) (R : List WalRec) {j k : Nat} (h : j ≤ k) :
    (recFrames C (R.take j)).length ≤ (recFrames C (R.take k)).length := by
  have e : R.take k = R.take j ++ (R.drop j).take (k - j) := by
    rw [show k = j + (k - j) by omega, List.take_add]; simp
  rw [e, recFrames_append, List.length_append]; omega

theorem frame_length_ge (d : List w8) : 8 ≤ (frame d).length := by
  rw [frame_length]; omega

theorem recFrames_take_succ (C : WalCodec) (R : List WalRec) {j : Nat} (hj : j < R.length) :
    recFrames C (R.take (j + 1)) = recFrames C (R.take j) ++ frame (C.encRec R[j]) := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, recFrames_append,
    recFrames_cons, recFrames_nil, List.append_nil]

/-- **A record boundary below another one**: the record after it, whose frame ends below the other. -/
theorem frame_at_lt (C : WalCodec) {R xs ys : List WalRec} (hxs : xs ++ ys = R) {jE : Nat}
    (hlt : (recFrames C xs).length < (recFrames C (R.take jE)).length) :
    ∃ y ys', ys = y :: ys' ∧
      (recFrames C xs).length + (frame (C.encRec y)).length ≤ (recFrames C (R.take jE)).length := by
  have hx : R.take xs.length = xs := by rw [← hxs]; simp
  have hj : xs.length < jE := by
    apply Nat.lt_of_not_le; intro hc
    have := recFrames_take_mono C R (show jE ≤ xs.length by omega)
    rw [hx] at this; omega
  cases ys with
  | nil =>
    exfalso
    have hR : xs = R := by simpa using hxs
    subst hR
    rw [List.take_of_length_le (by omega)] at hlt; omega
  | cons y ys' =>
    refine ⟨y, ys', rfl, ?_⟩
    have hxl : xs.length < R.length := by rw [← hxs]; simp
    have hy : R[xs.length] = y := by simp [← hxs]
    have := recFrames_take_mono C R (show xs.length + 1 ≤ jE by omega)
    rw [recFrames_take_succ C R hxl, hx, hy, List.length_append] at this
    exact this

/-- **What `decStep` read when it accepted**: a nonzero length word, inside the file, and the step's
length is the frame's by that word. -/
theorem decStep_accept_shape {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (h : decStep C last bs off c = .accept r len c') :
    leToU64 ((bs.drop off).take 8) ≠ 0#64 ∧ off + 8 ≤ bs.length ∧
    len = 8 + (decodeFrameSize (leToU64 ((bs.drop off).take 8))).1 +
      (decodeFrameSize (leToU64 ((bs.drop off).take 8))).2 := by
  have hb := decStep_rec_bound h
  unfold decStep at h
  simp only at h
  split at h; · cases h
  split at h; · cases h
  rename_i h2
  split at h; · cases h
  rename_i h3
  simp only [List.length_drop, Nat.not_lt] at h2
  refine ⟨h3, by omega, ?_⟩
  split at h; · cases h
  split at h; · cases h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · split at h
      · cases h
      · cases h; rfl

theorem take8_ext {img : List w8} {p : Nat} {w : List w8} (hw : w.length = 8) (hp : p + 8 ≤ img.length)
    (h : ∀ i, i < 8 → img.getD (p + i) 0 = w.getD i 0) : (img.drop p).take 8 = w := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < 8 := by simp at h1; omega
  have := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this
  simpa using this

theorem getD_rep8 {i : Nat} (h : i < 8) : (List.replicate 8 (0#8)).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos h]; rfl

theorem leToU64_zero8 : leToU64 (List.replicate 8 (0#8)) = 0#64 := by
  have := u64Le_to_word (W64 0); rw [u64Le_0] at this; exact this

variable {C : WalCodec} {R : List WalRec} {Y : Nat → w8} {cs : Nat → Cands} {so z0 : Nat}

/-- **A frame the reader accepts at a record boundary is the intended frame there** (see the file
header). -/
theorem tail_frame_match (hfit : RecsFit C R)
    (hT : TailCands (fun b => (recFrames C R).getD b 0) Y cs so z0) {jE : Nat}
    (hEb : (recFrames C (R.take jE)).length = max so z0)
    {img : List w8} (himg : ∀ b, b < img.length → ∃ s, (img.getD b 0, s) ∈ cs b)
    {xs ys : List WalRec} (hxs : xs ++ ys = R) {c : w32} {r : WalRec} {len : Nat} {c' : w32}
    (hd : decStep C true img (recFrames C xs).length c = .accept r len c')
    (ha : AsOf cs img (recFrames C xs).length (frameCore img (recFrames C xs).length)) :
    ∃ y ys', ys = y :: ys' ∧ len = (frame (C.encRec y)).length ∧
      (img.drop (recFrames C xs).length).take (frame (C.encRec y)).length = frame (C.encRec y) := by
  generalize hp : (recFrames C xs).length = p at hd ha
  obtain ⟨hl0, hp8, hlen⟩ := decStep_accept_shape hd
  have hbnd := (decStep_rec_bound hd).2
  have hS : recFrames C R = recFrames C xs ++ recFrames C ys := by rw [← hxs, recFrames_append]
  have hX : ∀ i, (recFrames C R).getD (p + i) 0 = (recFrames C ys).getD i 0 := by
    intro i; rw [hS, ← hp, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      ← List.getD_eq_getElem?_getD]; congr 1; omega
  have hcore8 : 8 ≤ frameCore img p := by unfold frameCore; omega
  -- the image's bytes at the frame: the intended ones (as of one change, or below `max so z0`)
  have hval : ∀ b, b < img.length → b < max so z0 → img.getD b 0 = (recFrames C R).getD b 0 := by
    intro b hb hbE
    rcases hT.mem_val (himg b hb).choose_spec with h | ⟨h1, -⟩
    · exact h
    · omega
  have hzero : ∀ b, b < img.length → (recFrames C R).getD b 0 = 0 → img.getD b 0 = 0 := by
    intro b hb hx
    rcases hT.mem_val (himg b hb).choose_spec with h | ⟨-, h⟩
    · rw [h, hx]
    · exact h
  -- the length word is the intended one
  have hword : ∀ i, i < 8 → img.getD (p + i) 0 = (recFrames C ys).getD i 0 := by
    rcases hT.asOf ha with ha | ha
    · -- as of the sync: below `max so z0`, else the word is zero
      by_cases hpE : p < max so z0
      · obtain ⟨y, ys', rfl, hle⟩ := frame_at_lt C hxs (by rw [hp, hEb]; exact hpE)
        intro i hi
        have := frame_length_ge (C.encRec y)
        rw [← hX]; exact hval _ (by omega) (by rw [← hEb, ← hp]; omega)
      · exfalso; apply hl0
        rw [take8_ext (w := List.replicate 8 (0#8)) (by simp) hp8 (fun i hi => by
          rw [ha (p + i) (by omega) (by omega), if_neg (by omega), getD_rep8 hi])]
        exact leToU64_zero8
    · intro i hi; rw [ha (p + i) (by omega) (by omega), hX]
  cases ys with
  | nil =>
    exfalso; apply hl0
    rw [take8_ext (w := List.replicate 8 (0#8)) (by simp) hp8 (fun i hi => by
      rw [hword i hi, getD_rep8 hi]; rfl)]
    exact leToU64_zero8
  | cons y ys' =>
    refine ⟨y, ys', rfl, ?_⟩
    have hfy := hfit y (by rw [← hxs]; simp)
    have hfr : recFrames C (y :: ys') = frame (C.encRec y) ++ recFrames C ys' := recFrames_cons C y ys'
    have hw8 : (img.drop p).take 8 = u64Le (encodeFrameSize (C.encRec y).length).1 := by
      apply take8_ext (u64Le_length _) hp8
      intro i hi
      rw [hword i hi, hfr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [frame_length]; omega)]
      simp only [frame, List.append_assoc]
      rw [List.getElem?_append_left (by rw [u64Le_length]; exact hi)]
    have hdec : decodeFrameSize (leToU64 ((img.drop p).take 8)) =
        ((C.encRec y).length, framePad (C.encRec y).length) := by
      rw [hw8, u64Le_to_word]; exact decodeFrameSize_encode _ hfy
    have hlenF : len = (frame (C.encRec y)).length := by rw [hlen, hdec, frame_length]
    refine ⟨hlenF, ?_⟩
    have hcore : frameCore img p = 8 + (C.encRec y).length := by unfold frameCore; rw [hdec]
    -- every byte of the frame
    have hall : ∀ i, i < (frame (C.encRec y)).length →
        img.getD (p + i) 0 = (frame (C.encRec y)).getD i 0 := by
      intro i hi
      have hXi : (recFrames C R).getD (p + i) 0 = (frame (C.encRec y)).getD i 0 := by
        rw [hX, hfr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hi]
      rw [← hXi]
      by_cases hc : i < 8 + (C.encRec y).length
      · rcases hT.asOf ha with ha | ha
        · by_cases hpE : p < max so z0
          · obtain ⟨y', ys'', hyy, hle⟩ := frame_at_lt C hxs (by rw [hp, hEb]; exact hpE)
            cases hyy
            exact hval _ (by omega) (by rw [← hEb, ← hp]; omega)
          · exfalso; apply hl0
            rw [take8_ext (w := List.replicate 8 (0#8)) (by simp) hp8 (fun i hi => by
              rw [ha (p + i) (by omega) (by omega), if_neg (by omega), getD_rep8 hi])]
            exact leToU64_zero8
        · exact ha (p + i) (by omega) (by rw [hcore]; omega)
      · -- the padding: intended zeros, and zeros under them
        have hpad : (frame (C.encRec y)).getD i 0 = 0 := by
          rw [frame_length] at hi
          simp only [frame, List.append_assoc, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by rw [u64Le_length]; omega),
            List.getElem?_append_right (by rw [u64Le_length]; omega), u64Le_length,
            List.getElem?_replicate]
          rw [if_pos (by omega)]; rfl
        rw [hXi, hpad]
        exact hzero _ (by omega) (by rw [hXi, hpad])
    apply List.ext_getElem (by have := frame_length (C.encRec y); simp; omega)
    intro i h1 h2
    have := hall i h2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this
    simpa using this

end frames

/-! ## The reader on the crashed tail -/

section decode
variable {C : WalCodec} {R : List WalRec} {Y : Nat → w8} {cs : Nat → Cands} {so z0 : Nat}

theorem acceptsFrom_accept {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (h : decStep C last bs off c = .accept r len c') :
    acceptsFrom C last bs off c = off :: acceptsFrom C last bs (off + len) c' := by
  rw [acceptsFrom_unfold, h]

/-- **The reader of the crashed tail** (see the file header): it accepts the intended records up to
some `j`, at least `jE` (those below `max so z0`), and rejects the next frame. -/
theorem tail_decode (hC : C.Ok) (hfit : RecsFit C R) {c0 : w32} (hch : ChainOk C c0 R)
    (hT : TailCands (fun b => (recFrames C R).getD b 0) Y cs so z0) {jE : Nat} (hjE : jE ≤ R.length)
    (hEb : (recFrames C (R.take jE)).length = max so z0)
    {img : List w8} (himg : ∀ b, b < img.length → ∃ s, (img.getD b 0, s) ∈ cs b)
    (hlen : max so z0 ≤ img.length)
    (hW : ∀ p ∈ acceptsFrom C true img 0 c0, AsOf cs img p (frameCore img p)) :
    ∃ j, jE ≤ j ∧ j ≤ R.length ∧ recFrames C (R.take j) <+: img ∧
      ∀ r len c', decStep C true img (recFrames C (R.take j)).length (chainEnd C c0 (R.take j)) ≠
        .accept r len c' := by
  -- the image is the intended stream below `max so z0`
  have hval : ∀ b, b < img.length → b < max so z0 → img.getD b 0 = (recFrames C R).getD b 0 := by
    intro b hb hbE
    rcases hT.mem_val (himg b hb).choose_spec with h | ⟨h1, -⟩
    · exact h
    · omega
  have key : ∀ ys xs, xs ++ ys = R → recFrames C xs <+: img →
      (∀ p ∈ acceptsFrom C true img (recFrames C xs).length (chainEnd C c0 xs),
        p ∈ acceptsFrom C true img 0 c0) →
      ∃ j, jE ≤ j ∧ j ≤ R.length ∧ recFrames C (R.take j) <+: img ∧
        ∀ r len c', decStep C true img (recFrames C (R.take j)).length (chainEnd C c0 (R.take j)) ≠
          .accept r len c' := by
    intro ys
    induction ys with
    | nil =>
      intro xs hxs hpre hsub
      have hR : xs = R := by simpa using hxs
      subst hR
      refine ⟨xs.length, hjE, Nat.le_refl _, by rw [List.take_length]; exact hpre, ?_⟩
      intro r len c' hd
      rw [List.take_length] at hd
      have hm := hsub _ (by rw [acceptsFrom_accept hd]; exact List.mem_cons_self ..)
      obtain ⟨y, ys', hy, -⟩ := tail_frame_match hfit hT hEb himg (List.append_nil xs) hd (hW _ hm)
      cases hy
    | cons y ys ih =>
      intro xs hxs hpre hsub
      have hx : R.take xs.length = xs := by rw [← hxs]; simp
      have hchy : ChainOk C (chainEnd C c0 xs) (y :: ys) :=
        ((chainOk_append C c0 xs (y :: ys)).mp (hxs ▸ hch)).2
      have hfy := hfit y (by rw [← hxs]; simp)
      cases hd : decStep C true img (recFrames C xs).length (chainEnd C c0 xs) with
      | stop s =>
        refine ⟨xs.length, ?_, by rw [← hxs]; simp, by rw [hx]; exact hpre, ?_⟩
        · -- below `jE` the image holds the next intended frame, which the reader accepts
          apply Nat.le_of_not_lt; intro hlt
          have hlt' : (recFrames C xs).length < (recFrames C (R.take jE)).length := by
            have := recFrames_take_mono C R (show xs.length + 1 ≤ jE by omega)
            have hxl : xs.length < R.length := by rw [← hxs]; simp
            rw [recFrames_take_succ C R hxl, hx, List.length_append] at this
            have := frame_length_ge (C.encRec R[xs.length]); omega
          obtain ⟨y', ys', hyy, hle⟩ := frame_at_lt C hxs hlt'
          cases hyy
          have hbs : img.drop (recFrames C xs).length = frame (C.encRec y) ++
              (img.drop (recFrames C xs).length).drop (frame (C.encRec y)).length := by
            have e : (img.drop (recFrames C xs).length).take (frame (C.encRec y)).length =
                frame (C.encRec y) := by
              apply List.ext_getElem (by have := frame_length (C.encRec y); simp; omega)
              intro i h1 h2
              have hb : (recFrames C xs).length + i < img.length := by simp at h1; omega
              have := hval _ hb (by omega)
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb,
                List.getD_eq_getElem?_getD, ← hxs, recFrames_append, recFrames_cons,
                List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)] at this
              simp only [Nat.add_sub_cancel_left, List.getElem?_eq_getElem h2, Option.getD_some]
                at this
              simpa using this
            have := List.take_append_drop (frame (C.encRec y)).length
              (img.drop (recFrames C xs).length)
            rw [e] at this; exact this.symm
          have := decStep_frame hC true hfy hbs hchy.1
          rw [hd] at this; cases this
        · intro r len c' h; rw [hx, hd] at h; cases h
      | accept r len c' =>
        have hm := hsub _ (by rw [acceptsFrom_accept hd]; exact List.mem_cons_self ..)
        obtain ⟨y', ys', hyy, hlenF, hwin⟩ := tail_frame_match hfit hT hEb himg hxs hd (hW _ hm)
        cases hyy
        have hbs : img.drop (recFrames C xs).length = frame (C.encRec y) ++
            (img.drop (recFrames C xs).length).drop (frame (C.encRec y)).length := by
          have := List.take_append_drop (frame (C.encRec y)).length
            (img.drop (recFrames C xs).length)
          rw [hwin] at this; exact this.symm
        have hst := decStep_frame hC true hfy hbs hchy.1
        rw [hd] at hst
        injection hst with h1 h2 h3
        subst h1 h2 h3
        have hpre' : recFrames C (xs ++ [r]) <+: img := by
          obtain ⟨t, ht⟩ := hpre
          rw [recFrames_append, recFrames_cons, recFrames_nil, List.append_nil]
          refine ⟨(img.drop (recFrames C xs).length).drop (frame (C.encRec r)).length, ?_⟩
          rw [List.append_assoc, ← hbs]
          have : (recFrames C xs).length = (recFrames C xs).length := rfl
          rw [← ht, List.drop_left' rfl]
        obtain ⟨j, h1, h2, h3, h4⟩ := ih (xs ++ [r]) (by rw [List.append_assoc]; exact hxs) hpre'
          (by
            intro p hp
            apply hsub
            rw [acceptsFrom_accept hd]
            apply List.mem_cons_of_mem
            rw [recFrames_append, chainEnd_append, List.length_append] at hp
            simpa [recFrames_cons, recFrames_nil, chainEnd] using hp)
        exact ⟨j, h1, h2, h3, h4⟩
  have := key R [] rfl (by simp [recFrames_nil]) (by simp [recFrames_nil, chainEnd])
  exact this

end decode

end WalFs
end EtcdGrove
end Perennial

end
