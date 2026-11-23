/-
The pure facts of a direction's byte stream (proved, not trusted; moved from the examples' `wire`
library, 2026-11-19, so that the kits' protocol library `Proto.lean` and the examples share them):

* `DirOk d W R`: a direction's unread bytes `d` agree with what its writer wrote (`W`) and its
  reader read (`R`): the read bytes followed by the unread ones are what was written, exactly while
  the connection is not broken (`d.status ≠ .cut`), a prefix of it once it is (bytes were lost). So
  the reader's bytes are always a prefix of the writer's (`dirOk_prefix`). Each operation's outcome
  keeps it (`dirOk_write`, `dirOk_read`, `dirOk_close`, `dirOk_closeWrite`); a new direction, or the
  shut empty one of an abandoned dial (D16), starts it with nothing written or read (`dirOk_fresh`,
  `dirOk_empty`, `dirOk_abandoned`).
* Facts of the outcomes (`readOutcome_got_le`, `readOutcome_bytes_pos`, `closeOutcome_closed`,
  `closeOutcome_of_closed`, `writeOutcome_of_closed`, `readOutcome_of_closed`).
* Dead directions (`NetDir.dead`: nothing unread, not open; D1 v3.5, `notes/net-sticky-read.md`):
  a read that returns EOF or `sys` leaves its direction dead (`readOutcome_dead_of`), every outcome
  keeps a dead direction dead (`readOutcome_dead`, `writeOutcome_dead`, `closeOutcome_dead`,
  `closeWriteOutcome_dead`), and a read of a dead direction returns no byte (`readOutcome_dead`).
* `setMap`: a set as the map `[∗map]` ranges over (`GSet` has no `[∗set]` instance; as raft's
  `Protocol.toMap`), with its laws; `ndot_mask`, disjoint namespaces.

The histories `W` and `R` are the proofs' bookkeeping: the semantics and the `net` specs have only
the unread bytes (`notes/net-tcp.md`).
-/
module

public import GooseLang.Ext.Net.Specs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace Net

section pure

/-- A direction's unread bytes and what its writer wrote (`W`) and its reader read (`R`) agree:
exactly, unless the connection broke, and as a prefix once it did. -/
def DirOk (d : NetDir) (W R : List w8) : Prop :=
  if d.status = .cut then R ++ d.bytes <+: W else R ++ d.bytes = W

theorem dirOk_prefix {d : NetDir} {W R : List w8} (h : DirOk d W R) : R <+: W := by
  unfold DirOk at h
  split at h
  · exact (List.prefix_append R d.bytes).trans h
  · rw [← h]; exact List.prefix_append R d.bytes

theorem dirOk_fresh : DirOk NetDir.fresh [] [] := by
  simp [DirOk, NetDir.fresh]

/-- A direction with nothing in it agrees with nothing written or read, whatever its status. -/
theorem dirOk_empty (st : NetStatus) : DirOk ⟨[], st⟩ [] [] := by
  cases st <;> simp [DirOk]

/-- The direction from an abandoned dial's dialer (D16: shut and empty). -/
theorem dirOk_abandoned : DirOk ⟨[], .fin⟩ [] [] := dirOk_empty .fin

theorem dirOk_cut {d : NetDir} {W R : List w8} (k : Nat) (h : DirOk d W R) :
    DirOk ⟨d.bytes.take k, .cut⟩ W R := by
  simp only [DirOk, ↓reduceIte]
  have hp : R ++ d.bytes.take k <+: R ++ d.bytes :=
    (List.prefix_append_right_inj R).2 (List.take_prefix k d.bytes)
  unfold DirOk at h
  split at h
  · exact hp.trans h
  · rw [← h]; exact hp

theorem dirOk_avail {st : NetEnd} {d d' : NetDir} {W R : List w8} {n : Nat} {r : ReadRes}
    (h : DirOk d W R) (hr : ReadAvail st d n r d') : DirOk d' W (R ++ r.got) := by
  rcases hr with ⟨k, -, -, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · simp only [ReadRes.got, DirOk, List.append_assoc, List.take_append_drop] at h ⊢
    exact h
  all_goals simpa [ReadRes.got] using h

/-- A read keeps `DirOk`, the reader having read what it returned. -/
theorem dirOk_read {st : NetEnd} {d d' : NetDir} {W R : List w8} {n : Nat} {r : ReadRes}
    (h : DirOk d W R) (hr : ReadOutcome st d n r d') : DirOk d' W (R ++ r.got) := by
  unfold ReadOutcome at hr
  split at hr
  · obtain ⟨rfl, rfl⟩ := hr; simpa [ReadRes.got] using h
  · split at hr
    · obtain ⟨rfl, rfl⟩ := hr; simpa [ReadRes.got] using h
    · rcases hr with hr | ⟨k, -, hr⟩
      · exact dirOk_avail h hr
      · exact dirOk_avail (dirOk_cut k h) hr

/-- A step of a `Write` keeps `DirOk`, the writer having written what it appended. -/
theorem dirOk_write {st : NetEnd} {d d' : NetDir} {W R rs : List w8} {k : Nat}
    {res : Option NetErr} (h : DirOk d W R) (hw : WriteOutcome st d rs k res d') :
    DirOk d' (W ++ rs.take k) R := by
  unfold WriteOutcome at hw
  split at hw
  · obtain ⟨rfl, -, rfl⟩ := hw; simpa using h
  · split at hw
    · obtain ⟨rfl, rfl, -⟩ := hw; simpa using h
    · rename_i hcut
      obtain ⟨rfl, -⟩ := hw
      simp only [DirOk, hcut, ↓reduceIte] at h ⊢
      exact h.trans (List.prefix_append W _)
    · rename_i hopen
      simp only [DirOk, hopen, reduceCtorEq, ↓reduceIte] at h
      rcases hw with ⟨-, -, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨-, rfl, -, rfl⟩
      · simp only [DirOk, hopen, reduceCtorEq, ↓reduceIte, ← List.append_assoc, h]
      · simp only [DirOk, ↓reduceIte, List.take_zero, List.append_nil, h]
        exact List.prefix_refl _
      · simp only [DirOk, hopen, reduceCtorEq, ↓reduceIte, List.take_zero, List.append_nil, h]

theorem dirOk_shut {d : NetDir} {W R : List w8} (h : DirOk d W R) : DirOk d.shut W R := by
  unfold NetDir.shut
  split
  · rename_i ho
    simp only [DirOk, ho] at h ⊢
    simpa using h
  · exact h

theorem dirOk_close {st st' : NetEnd} {d d' : NetDir} {W R : List w8} {res : Option NetErr}
    (h : DirOk d W R) (hc : CloseOutcome st d res st' d') : DirOk d' W R := by
  unfold CloseOutcome at hc
  split at hc
  · obtain ⟨-, -, rfl⟩ := hc; exact h
  · obtain ⟨-, -, rfl⟩ := hc; exact dirOk_shut h

theorem dirOk_closeWrite {st : NetEnd} {d d' : NetDir} {W R : List w8} {res : Option NetErr}
    (h : DirOk d W R) (hc : CloseWriteOutcome st d res d') : DirOk d' W R := by
  unfold CloseWriteOutcome at hc
  split at hc
  · obtain ⟨-, rfl⟩ := hc; exact h
  · rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact dirOk_shut h
    · exact h

/-- A read of `m` bytes returns at most `m`, and some unless `m = 0`. -/
theorem readOutcome_got_le {st : NetEnd} {d : NetDir} {m : Nat} {r : ReadRes} {d' : NetDir}
    (h : ReadOutcome st d m r d') : r.got.length ≤ m ∧ (r = .bytes [] → m = 0) := by
  have hav : ∀ d0, ReadAvail st d0 m r d' → r.got.length ≤ m ∧ (r = .bytes [] → m = 0) := by
    intro d0 h
    rcases h with ⟨k, hk1, hk, hkd, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, rfl, -⟩
    · refine ⟨by simp only [ReadRes.got, List.length_take]; omega, ?_⟩
      intro h
      have h' := congrArg (fun r => r.got.length) h
      simp only [ReadRes.got, List.length_take, List.length_nil] at h'
      omega
    all_goals simp [ReadRes.got]
  unfold ReadOutcome at h
  split at h
  · obtain ⟨rfl, -⟩ := h; simp [ReadRes.got]
  split at h
  · obtain ⟨rfl, -⟩ := h; simp [ReadRes.got]; assumption
  rcases h with h | ⟨k, -, h⟩
  · exact hav _ h
  · exact hav _ h

/-- A read of `n > 0` bytes that returns bytes returns at least one. -/
theorem readOutcome_bytes_pos {st : NetEnd} {d d' : NetDir} {n : Nat} {bs : List w8}
    (h : ReadOutcome st d n (.bytes bs) d') (hn : 0 < n) : 1 ≤ bs.length := by
  have hav : ∀ (d0 : NetDir), ReadAvail st d0 n (.bytes bs) d' → 1 ≤ bs.length := by
    intro d0 hr
    rcases hr with ⟨k, hk1, -, hkl, hr, -⟩ | ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩ | ⟨-, hr, -⟩
    · cases hr; simp only [List.length_take]; omega
    all_goals cases hr
  unfold ReadOutcome at h
  split at h
  · cases h.1
  · split at h
    · omega
    · rcases h with h | ⟨k, -, h⟩
      · exact hav d h
      · exact hav _ h

/-- A close leaves the end closed. -/
theorem closeOutcome_closed {st : NetEnd} {d : NetDir} {res : Option NetErr} {st' : NetEnd}
    {d' : NetDir} (h : CloseOutcome st d res st' d') : st'.closed = true := by
  unfold CloseOutcome at h
  split at h
  · rw [h.2.1]; assumption
  · rw [h.2.1]

/-- A close of a closed end fails (`closed`) and changes nothing. -/
theorem closeOutcome_of_closed {st : NetEnd} {d : NetDir} {res : Option NetErr} {st' : NetEnd}
    {d' : NetDir} (hc : st.closed = true) (h : CloseOutcome st d res st' d') :
    res = some .closed ∧ st' = st := by
  simp only [CloseOutcome, hc, ↓reduceIte] at h
  exact ⟨h.1, h.2.1⟩

/-- A write on a closed end fails (`closed`). -/
theorem writeOutcome_of_closed {st : NetEnd} {d : NetDir} {bs : List w8} {k : Nat}
    {res : Option NetErr} {d' : NetDir} (hc : st.closed = true)
    (h : WriteOutcome st d bs k res d') : res = some .closed := by
  simp only [WriteOutcome, hc, ↓reduceIte] at h
  exact h.2.1

/-- A read on a closed end fails (`closed`). -/
theorem readOutcome_of_closed {st : NetEnd} {d : NetDir} {n : Nat} {r : ReadRes} {d' : NetDir}
    (hc : st.closed = true) (h : ReadOutcome st d n r d') : r = .err .closed := by
  simp only [ReadOutcome, hc, ↓reduceIte] at h
  exact h.1

/-! ### Dead directions (D1 v3.5) -/

/-- A direction is dead: nothing is unread and its writer is done (`fin` or `cut`). No outcome
gives it a byte or reopens it, so a read of it returns no byte. -/
def NetDir.dead (d : NetDir) : Prop := d.bytes = [] ∧ d.status ≠ .open

/-- A read of a dead direction leaves it dead and returns no byte. -/
theorem readAvail_dead {st : NetEnd} {d d' : NetDir} {n : Nat} {r : ReadRes}
    (hd : d.dead) (h : ReadAvail st d n r d') : d'.dead ∧ ∀ bs, r ≠ .bytes bs := by
  have hb := hd.1
  rcases h with ⟨k, hk1, -, hkl, -, -⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · rw [hb] at hkl; simp at hkl; omega
  all_goals exact ⟨hd, fun _ h => by cases h⟩

/-- A read that returns EOF or a `sys` error leaves its direction dead (D1 v3.5: a `sys` error needs
nothing unread). -/
theorem readOutcome_dead_of {st : NetEnd} {d d' : NetDir} {n : Nat} {r : ReadRes}
    (h : ReadOutcome st d n r d') (hr : r = .eof ∨ r = .err .sys) : d'.dead := by
  have hav : ∀ d0, ReadAvail st d0 n r d' → d'.dead := by
    intro d0 h
    rcases h with ⟨k, -, -, -, rfl, -⟩ | ⟨hb, hs, -, rfl⟩ | ⟨hs, hb, -, rfl⟩ | ⟨-, rfl, -⟩
    · rcases hr with h | h <;> cases h
    · exact ⟨hb, hs⟩
    · exact ⟨hb, by rw [hs]; decide⟩
    · rcases hr with h | h <;> cases h
  unfold ReadOutcome at h
  split at h
  · obtain ⟨rfl, -⟩ := h; rcases hr with h | h <;> cases h
  split at h
  · obtain ⟨rfl, -⟩ := h; rcases hr with h | h <;> cases h
  rcases h with h | ⟨k, -, h⟩
  · exact hav _ h
  · exact hav _ h

/-- A read of a dead direction leaves it dead and returns no byte: nothing for `n = 0` or on a
closed end, else an error or EOF. -/
theorem readOutcome_dead {st : NetEnd} {d d' : NetDir} {n : Nat} {r : ReadRes}
    (hd : d.dead) (h : ReadOutcome st d n r d') :
    d'.dead ∧ r.got = [] ∧ (n ≠ 0 → ∀ bs, r ≠ .bytes bs) := by
  have hav : ∀ d0 : NetDir, d0.dead → ReadAvail st d0 n r d' →
      d'.dead ∧ r.got = [] ∧ (n ≠ 0 → ∀ bs, r ≠ .bytes bs) := by
    intro d0 hd0 h
    obtain ⟨h1, h2⟩ := readAvail_dead hd0 h
    refine ⟨h1, ?_, fun _ => h2⟩
    cases r with
    | bytes bs => exact absurd rfl (h2 bs)
    | eof => rfl
    | err e => rfl
  unfold ReadOutcome at h
  split at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨hd, rfl, fun _ _ h => by cases h⟩
  split at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨hd, rfl, fun h => absurd ‹n = 0› h⟩
  rcases h with h | ⟨k, -, h⟩
  · exact hav d hd h
  · refine hav _ ⟨?_, by simp⟩ h
    show d.bytes.take k = []
    rw [hd.1]; simp

/-- A step of a `Write` keeps a dead direction dead (nothing is appended to a shut or cut one). -/
theorem writeOutcome_dead {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    {res : Option NetErr} (hd : d.dead) (h : WriteOutcome st d rs k res d') : d'.dead := by
  unfold WriteOutcome at h
  split at h
  · obtain ⟨-, -, rfl⟩ := h; exact hd
  · split at h
    · obtain ⟨-, rfl, -⟩ := h; exact hd
    · obtain ⟨rfl, -⟩ := h; exact hd
    · rename_i hopen; exact absurd hopen hd.2

theorem shut_dead {d : NetDir} (hd : d.dead) : d.shut.dead := by
  unfold NetDir.shut
  simp only [hd.2, ↓reduceIte]; exact hd

/-- A close keeps a dead direction dead. -/
theorem closeOutcome_dead {st st' : NetEnd} {d d' : NetDir} {res : Option NetErr}
    (hd : d.dead) (h : CloseOutcome st d res st' d') : d'.dead := by
  unfold CloseOutcome at h
  split at h
  · obtain ⟨-, -, rfl⟩ := h; exact hd
  · obtain ⟨-, -, rfl⟩ := h; exact shut_dead hd

/-- A `CloseWrite` keeps a dead direction dead. -/
theorem closeWriteOutcome_dead {st : NetEnd} {d d' : NetDir} {res : Option NetErr}
    (hd : d.dead) (h : CloseWriteOutcome st d res d') : d'.dead := by
  unfold CloseWriteOutcome at h
  split at h
  · obtain ⟨-, rfl⟩ := h; exact hd
  · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact shut_dead hd
    · exact hd

/-- A close keeps the end's read deadline. -/
theorem closeOutcome_rdl {st st' : NetEnd} {d d' : NetDir} {res : Option NetErr}
    (h : CloseOutcome st d res st' d') : st'.rdl = st.rdl := by
  unfold CloseOutcome at h
  split at h
  · rw [h.2.1]
  · rw [h.2.1]

/-- Setting the write deadline (kind `2`) keeps the end's read deadline. -/
theorem deadlineOutcome_w_rdl {st st' : NetEnd} {set : Bool} {res : Option NetErr}
    (h : DeadlineOutcome st (W64 2) set res st') : st'.rdl = st.rdl := by
  unfold DeadlineOutcome at h
  split at h
  · rw [h.2]
  · rw [h.2]; simp

/-- Without a read deadline, a read does not time out. -/
theorem readOutcome_no_timeout {st : NetEnd} {d d' : NetDir} {n : Nat}
    (hst : st.rdl = false) (h : ReadOutcome st d n (.err .timeout) d') : False := by
  have hav : ∀ d0, ReadAvail st d0 n (.err .timeout) d' → False := by
    intro d0 h
    rcases h with ⟨_, _, _, _, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -, -⟩
    · cases h
    · cases h
    · cases h
    · rw [hst] at h; cases h
  unfold ReadOutcome at h
  split at h
  · cases h.1
  split at h
  · cases h.1
  rcases h with h | ⟨k, -, h⟩
  · exact hav _ h
  · exact hav _ h

end pure

/-! ## Sets as maps, namespaces -/

/-- A set as the map `[∗map]` ranges over. -/
@[reducible] def setMap (X : GSet Nat) : GMap Nat Unit := X

theorem setMap_insert (S : GSet Nat) (c : Nat) :
    setMap (S ∪ {[c]}) = (setMap S).insert c () := by
  apply GMap.ext; intro k
  simp only [setMap, GMap.lookup_insert_eq_iff]
  by_cases h : c = k
  · subst h
    have : c ∈ S ∪ {[c]} := (GMap.elem_of_union _ _ _).2 (.inr (GMap.elem_of_singleton_2 c))
    simpa [GMap.elem_of_gset] using this
  · simp only [h, ↓reduceIte]
    have hiff : k ∈ S ∪ {[c]} ↔ k ∈ S := by
      rw [GMap.elem_of_union, GMap.elem_of_singleton]; constructor
      · rintro (h1 | h1)
        · exact h1
        · exact absurd h1.symm h
      · intro h1; exact .inl h1
    simp only [GMap.elem_of_gset] at hiff
    cases h1 : S !! k <;> cases h2 : (S ∪ {[c]}) !! k <;> simp_all

theorem setMap_lookup_none {S : GSet Nat} {c : Nat} (h : c ∉ S) :
    PartialMap.get? (setMap S) c = none := by
  rw [gmap_get?_eq]
  cases hk : (setMap S).lookup c with
  | none => rfl
  | some u => exact absurd ((GMap.elem_of_gset _ _).2 (by simpa using hk)) h

theorem setMap_delete (S : GSet Nat) (c : Nat) :
    PartialMap.delete (setMap S) c = setMap (S \ {[c]}) := by
  apply GMap.ext; intro k
  show (GMap.delete c S).lookup k = (S \ {[c]}).lookup k
  by_cases h : c = k
  · subst h
    rw [GMap.lookup_delete]
    have : c ∉ S \ {[c]} := by
      rw [GMap.elem_of_difference]; intro h1; exact h1.2 (GMap.elem_of_singleton_2 c)
    rw [GMap.elem_of_gset] at this
    cases hk : (S \ {[c]}).lookup c with
    | none => rfl
    | some u => exact absurd (by simpa using hk) this
  · rw [GMap.lookup_delete_ne _ h]
    have hiff : k ∈ S \ {[c]} ↔ k ∈ S := by
      rw [GMap.elem_of_difference, GMap.not_elem_of_singleton]
      exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, Ne.symm h⟩⟩
    simp only [GMap.elem_of_gset] at hiff
    cases h1 : S !! k <;> cases h2 : (S \ {[c]}) !! k <;> simp_all


/-- Two namespaces of different names are disjoint (as Perennial's `sync.wg_mask_ndot_ne`). -/
theorem ndot_mask (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩


end Net
end Perennial
