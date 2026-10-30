/-
The compaction keys' tracked absence (`fkKey`, `Model2.lean`; the backend-compaction stage,
2026-10-29): the batch state's operations other than a put of a compaction key keep it
(`fkAbsSt_*`), and a readers' state without the keys reads none (`rtRange_fkAbs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WritebackLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

theorem dget_insert (S : Data) (n n' k : GoString) (b : BktData) :
    dget (S.insert n b) n' k = if n = n' then b.lookup k else dget S n' k := by
  unfold dget
  rw [GMap.lookup_insert_eq_iff]
  split <;> rfl

theorem fkAbsD_put {S : Data} {n k : GoString} (v : GoString) (h : fkAbsD S) (hk : ¬ fkKey n k) :
    fkAbsD (S.insert n ((bktOf S n).insert k v)) := by
  intro n' k' hf
  rw [dget_insert]
  split
  · rename_i hn
    subst hn
    rw [GMap.lookup_insert_eq_iff]
    split
    · rename_i hkk; subst hkk; exact absurd hf hk
    · rw [← dget_eq_bktOf]; exact h _ _ hf
  · exact h _ _ hf

theorem fkAbsD_delk {S : Data} {n k : GoString} (h : fkAbsD S) :
    fkAbsD (S.insert n ((bktOf S n).delete k)) := by
  intro n' k' hf
  rw [dget_insert]
  split
  · rename_i hn
    subst hn
    rw [GMap.lookup_delete_iff]
    split
    · rfl
    · rw [← dget_eq_bktOf]; exact h _ _ hf
  · exact h _ _ hf

theorem fkAbsD_create {S : Data} {n : GoString} (h : fkAbsD S) :
    fkAbsD (if S.lookup n = none then S.insert n ∅ else S) := by
  split
  · intro n' k' hf
    rw [dget_insert]
    split
    · rfl
    · exact h _ _ hf
  · exact h

theorem fkAbsD_delete {S : Data} {n : GoString} (h : fkAbsD S) : fkAbsD (S.delete n) := by
  intro n' k' hf
  unfold dget
  rw [GMap.lookup_delete_iff]
  split
  · rfl
  · exact h _ _ hf

theorem fkAbsB_empty (P : BParams) : fkAbsB P (∅ : GMap w64 (List Ent)) := by
  intro n k i _ _ e he
  simp [bkOf] at he

theorem fkAbsB_wbAdd {P : BParams} {B : GMap w64 (List Ent)} {n : GoString} {id : w64}
    {k v : GoString} (hP : P.Wf) (h : fkAbsB P B) (hid : P.BT.lookup n = some id)
    (hk : ¬ fkKey n k) : fkAbsB P (wbAdd B id (k, v)) := by
  intro n' k' i hf hi e he
  rw [bkOf_wbAdd] at he
  split at he
  · rename_i hii
    subst hii
    rcases List.mem_append.1 he with he | he
    · exact h n' k' id hf hi e he
    · rw [List.mem_singleton] at he
      subst he
      intro hkk
      have hn : n = n' := hP.1 n n' id hid hi
      subst hn
      simp only at hkk
      subst hkk
      exact hk hf
  · exact h n' k' i hf hi e he

theorem fkAbsB_wbMerge {P : BParams} {W R : GMap w64 (List Ent)} (hW : fkAbsB P W)
    (hR : fkAbsB P R) : fkAbsB P (wbMerge W R) := by
  intro n k i hf hi e he
  rcases mem_bkOf_wbMerge he with he | he
  · exact hR n k i hf hi e he
  · exact hW n k i hf hi e he

theorem fkAbsB_bksReset (P : BParams) (B : GMap w64 (List Ent)) : fkAbsB P (bksReset B) := by
  intro n k i _ _ e he
  rw [bkOf_bksResetC] at he
  cases he

theorem fkAbsB_writebackW (P : BParams) (W : WBuf) (R : RBuf) :
    fkAbsB P (writebackW W R).bks := by
  intro n k i _ _ e he
  rw [bkOf_writebackW] at he
  cases he

theorem fkInit_zero {D : Data} (h : fkInit D = 0) : fkAbsD D := by
  unfold fkInit at h
  split at h
  · assumption
  · cases h

theorem fkInit_of_abs {D : Data} (h : fkAbsD D) : fkInit D = 0 := by
  unfold fkInit
  simp [h]

/-! ## The batch state's operations -/

theorem fkAbsSt_put {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hP : P.Wf) (hbi : P.has bi) (hk : ¬ fkKey bi.name k) (h : fkAbsSt P st) :
    fkAbsSt P (st.put bi k v seq) := by
  obtain ⟨hrv, hS, hW⟩ := h
  refine ⟨hrv, fkAbsD_put v hS hk, ?_⟩
  unfold BSess.put
  cases seq
  · exact fkAbsB_wbAdd hP hW hbi hk
  · exact fkAbsB_wbAdd hP hW hbi hk

theorem fkAbsSt_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString}
    (h : fkAbsSt P st) : fkAbsSt P (st.del bi k) :=
  ⟨h.1, fkAbsD_delk h.2.1, h.2.2⟩

theorem fkAbsSt_create {P : BParams} {st : BSess} {bi : BucketInfo} (h : fkAbsSt P st) :
    fkAbsSt P (st.create bi) :=
  ⟨h.1, fkAbsD_create h.2.1, h.2.2⟩

theorem fkAbsSt_delBucket {P : BParams} {st : BSess} {bi : BucketInfo} (h : fkAbsSt P st) :
    fkAbsSt P (st.delBucket bi) :=
  ⟨h.1, fkAbsD_delete h.2.1, h.2.2⟩

theorem fkAbsSt_wb {P : BParams} {st : BSess} (h : fkAbsSt P st) : fkAbsSt P (wbSt P st) :=
  ⟨⟨h.1.1, fkAbsB_wbMerge h.2.2 h.1.2⟩, h.2.1, fkAbsB_writebackW P st.W st.R⟩

theorem fkAbsSt_commit {P : BParams} {st : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt}
    (h : fkAbsSt P st) (hC : C' = st.S ∨ C' = st.C) : fkAbsSt P (commitSt st C' tx' cnt') := by
  refine ⟨⟨?_, fkAbsB_bksReset P _⟩, h.2.1, h.2.2⟩
  rcases hC with rfl | rfl
  · exact h.2.1
  · exact h.1.1

theorem fkAbsSt_setHw {P : BParams} {st : BSess} (x : Bool) (h : fkAbsSt P st) :
    fkAbsSt P (st.setHw x) := h

/-! ## Reads -/

/-- A readers' state with no compaction key reads none at one: `UnsafeRange(Meta, k, nil, _)`
of a compaction key `k` returns nothing. -/
theorem rtRange_fkAbs {P : BParams} {rv : RView} {bi : BucketInfo} {kb : GoString} (lim : w64)
    (h : fkAbsRv P rv) (hbi : P.has bi) (hk : fkKey bi.name kb) :
    rtRange rv bi kb [] lim = [] := by
  have hbuf : bbRange (bkOf rv.2.bks bi.id) kb [] (rangeLimit [] lim) = [] := by
    unfold bbRange
    split
    · rfl
    · rename_i e rest hd
      simp only [↓reduceIte]
      have he : e ∈ bkOf rv.2.bks bi.id := by
        have : e ∈ (bkOf rv.2.bks bi.id).dropWhile (fun e => decide (strLt e.1 kb)) := by
          rw [hd]; exact List.mem_cons_self
        exact (List.dropWhile_sublist _).subset this
      have hne := h.2 bi.name kb bi.id hk hbi e he
      simp [hne]
  unfold rtRange
  simp only [hbuf, List.length_nil, List.append_nil]
  have hlim : rangeLimit [] lim = W64 1 := by simp [rangeLimit]
  rw [hlim]
  have h0 : ¬ (((0 : Nat) : Int) = sint.Z (W64 1)) := by decide
  simp only [h0, ↓reduceIte]
  unfold cursorRange
  simp only [↓reduceIte]
  -- no entry of the committed bucket has the key
  have hnone : ∀ e ∈ bktEnts (bktOf rv.1 bi.name), e.1 ≠ kb := by
    intro e he hek
    have hm : e ∈ (bktOf rv.1 bi.name).toList := List.mem_mergeSort.1 he
    have hl : (bktOf rv.1 bi.name).lookup e.1 = some e.2 := (GMap.mem_toList _ _ _).1 hm
    rw [hek, ← dget_eq_bktOf, h.1 bi.name kb hk] at hl
    cases hl
  generalize hr : (bktEnts (bktOf rv.1 bi.name)).drop _ = rest
  have hsub : ∀ e ∈ rest, e.1 ≠ kb := by
    intro e he
    rw [← hr] at he
    exact hnone e (List.mem_of_mem_drop he)
  cases rest with
  | nil => rfl
  | cons e rest =>
    simp [List.takeWhile, hsub e List.mem_cons_self]

/-! ## The compaction keys' well-formed values (question 4, 2026-10-29) -/

theorem fkWfD_of_abs (P : BParams) {D : Data} (h : fkAbsD D) : fkWfD P D := by
  intro n k v hf hv
  rw [h n k hf] at hv; cases hv

theorem fkWfB_of_abs {P : BParams} {B : GMap w64 (List Ent)} (h : fkAbsB P B) : fkWfB P B := by
  intro n k i hf hi e he hek
  exact absurd hek (h n k i hf hi e he)

theorem fkWfSt_of_abs {P : BParams} {st : BSess} (h : fkAbsSt P st) : fkWfSt P st :=
  ⟨⟨fkWfD_of_abs P h.1.1, fkWfB_of_abs h.1.2⟩, fkWfD_of_abs P h.2.1, fkWfB_of_abs h.2.2⟩

theorem fkWfD_put {P : BParams} {S : Data} {n k : GoString} (v : GoString) (h : fkWfD P S)
    (hv : fkKey n k → P.FV v) : fkWfD P (S.insert n ((bktOf S n).insert k v)) := by
  intro n' k' v' hf hl
  rw [dget_insert] at hl
  split at hl
  · rename_i hn
    subst hn
    rw [GMap.lookup_insert_eq_iff] at hl
    split at hl
    · rename_i hkk; subst hkk; cases hl; exact hv hf
    · rw [← dget_eq_bktOf] at hl; exact h _ _ _ hf hl
  · exact h _ _ _ hf hl

theorem fkWfD_delk {P : BParams} {S : Data} {n k : GoString} (h : fkWfD P S) :
    fkWfD P (S.insert n ((bktOf S n).delete k)) := by
  intro n' k' v' hf hl
  rw [dget_insert] at hl
  split at hl
  · rename_i hn
    subst hn
    rw [GMap.lookup_delete_iff] at hl
    split at hl
    · cases hl
    · rw [← dget_eq_bktOf] at hl; exact h _ _ _ hf hl
  · exact h _ _ _ hf hl

theorem fkWfD_create {P : BParams} {S : Data} {n : GoString} (h : fkWfD P S) :
    fkWfD P (if S.lookup n = none then S.insert n ∅ else S) := by
  split
  · intro n' k' v' hf hl
    rw [dget_insert] at hl
    split at hl
    · simp at hl
    · exact h _ _ _ hf hl
  · exact h

theorem fkWfD_delete {P : BParams} {S : Data} {n : GoString} (h : fkWfD P S) :
    fkWfD P (S.delete n) := by
  intro n' k' v' hf hl
  unfold dget at hl
  rw [GMap.lookup_delete_iff] at hl
  split at hl
  · cases hl
  · exact h _ _ _ hf hl

theorem fkWfB_wbAdd {P : BParams} {B : GMap w64 (List Ent)} {n : GoString} {id : w64}
    {k v : GoString} (hP : P.Wf) (h : fkWfB P B) (hid : P.BT.lookup n = some id)
    (hv : fkKey n k → P.FV v) : fkWfB P (wbAdd B id (k, v)) := by
  intro n' k' i hf hi e he hek
  rw [bkOf_wbAdd] at he
  split at he
  · rename_i hii
    subst hii
    rcases List.mem_append.1 he with he | he
    · exact h n' k' id hf hi e he hek
    · rw [List.mem_singleton] at he
      subst he
      have hn : n = n' := hP.1 n n' id hid hi
      subst hn
      simp only at hek
      subst hek
      exact hv hf
  · exact h n' k' i hf hi e he hek

theorem fkWfB_wbMerge {P : BParams} {W R : GMap w64 (List Ent)} (hW : fkWfB P W)
    (hR : fkWfB P R) : fkWfB P (wbMerge W R) := by
  intro n k i hf hi e he hek
  rcases mem_bkOf_wbMerge he with he | he
  · exact hR n k i hf hi e he hek
  · exact hW n k i hf hi e he hek

theorem fkWfB_bksReset (P : BParams) (B : GMap w64 (List Ent)) : fkWfB P (bksReset B) :=
  fkWfB_of_abs (fkAbsB_bksReset P B)

theorem fkWfB_writebackW (P : BParams) (W : WBuf) (R : RBuf) : fkWfB P (writebackW W R).bks :=
  fkWfB_of_abs (fkAbsB_writebackW P W R)

/-! ## The flag and the bit together: `fkOk` -/

theorem fkOk_put {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hP : P.Wf) (hbi : P.has bi) (hk : ¬ fkKey bi.name k) (f : Nat) (w : Bool)
    (h : fkOk P f w st) : fkOk P f w (st.put bi k v seq) := by
  refine ⟨fun h0 => fkAbsSt_put seq hP hbi hk (h.1 h0), fun hw => ?_⟩
  obtain ⟨hrv, hS, hW⟩ := h.2 hw
  refine ⟨hrv, fkWfD_put v hS (fun hf => absurd hf hk), ?_⟩
  unfold BSess.put
  cases seq
  · exact fkWfB_wbAdd hP hW hbi (fun hf => absurd hf hk)
  · exact fkWfB_wbAdd hP hW hbi (fun hf => absurd hf hk)

/-- A put of a compaction key, of a well-formed value: the flag raised to at least `1`. -/
theorem fkOk_putFk {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hP : P.Wf) (hbi : P.has bi) (hv : P.FV v) (f : Nat) (w : Bool) (h : fkOk P f w st) :
    fkOk P (max f 1) w (st.put bi k v seq) := by
  refine ⟨fun h0 => absurd h0 (by have := Nat.le_max_right f 1; omega), fun hw => ?_⟩
  obtain ⟨hrv, hS, hW⟩ := h.2 hw
  refine ⟨hrv, fkWfD_put v hS (fun _ => hv), ?_⟩
  unfold BSess.put
  cases seq
  · exact fkWfB_wbAdd hP hW hbi (fun _ => hv)
  · exact fkWfB_wbAdd hP hW hbi (fun _ => hv)

theorem fkOk_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString} (f : Nat) (w : Bool)
    (h : fkOk P f w st) : fkOk P f w (st.del bi k) :=
  ⟨fun h0 => fkAbsSt_del (h.1 h0), fun hw => ⟨(h.2 hw).1, fkWfD_delk (h.2 hw).2.1, (h.2 hw).2.2⟩⟩

theorem fkOk_create {P : BParams} {st : BSess} {bi : BucketInfo} (f : Nat) (w : Bool)
    (h : fkOk P f w st) : fkOk P f w (st.create bi) :=
  ⟨fun h0 => fkAbsSt_create (h.1 h0), fun hw => ⟨(h.2 hw).1, fkWfD_create (h.2 hw).2.1, (h.2 hw).2.2⟩⟩

theorem fkOk_delBucket {P : BParams} {st : BSess} {bi : BucketInfo} (f : Nat) (w : Bool)
    (h : fkOk P f w st) : fkOk P f w (st.delBucket bi) :=
  ⟨fun h0 => fkAbsSt_delBucket (h.1 h0),
   fun hw => ⟨(h.2 hw).1, fkWfD_delete (h.2 hw).2.1, (h.2 hw).2.2⟩⟩

theorem fkOk_wb {P : BParams} {st : BSess} (f : Nat) (w : Bool) (h : fkOk P f w st) :
    fkOk P f w (wbSt P st) :=
  ⟨fun h0 => fkAbsSt_wb (h.1 h0),
   fun hw => ⟨⟨(h.2 hw).1.1, fkWfB_wbMerge (h.2 hw).2.2 (h.2 hw).1.2⟩, (h.2 hw).2.1,
     fkWfB_writebackW P st.W st.R⟩⟩

theorem fkOk_commit {P : BParams} {st : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt}
    (hC : C' = st.S ∨ C' = st.C) (f : Nat) (w : Bool) (h : fkOk P f w st) :
    fkOk P f w (commitSt st C' tx' cnt') := by
  refine ⟨fun h0 => fkAbsSt_commit (h.1 h0) hC, fun hw => ?_⟩
  refine ⟨⟨?_, fkWfB_bksReset P _⟩, (h.2 hw).2.1, (h.2 hw).2.2⟩
  rcases hC with rfl | rfl
  · exact (h.2 hw).2.1
  · exact (h.2 hw).1.1

theorem fkOk_setHw {P : BParams} {st : BSess} (x : Bool) (f : Nat) (w : Bool)
    (h : fkOk P f w st) : fkOk P f w (st.setHw x) := h

/-- The readers' state of a batch state (its committed data and read buffer). -/
theorem fkOkRv_of {P : BParams} {st : BSess} {f : Nat} {w : Bool} (h : fkOk P f w st) :
    fkOkRv P f w (st.C, st.R) :=
  ⟨fun h0 => (h.1 h0).1, fun hw => (h.2 hw).1⟩

theorem fkInit_wf {P : BParams} {D : Data} (h : fkWInit P D = true) : fkWfD P D := by
  unfold fkWInit at h
  simpa using h

/-- The initial state's facts: committed data and writer's contents `D`, empty buffers. -/
theorem fkOk_init {P : BParams} {D : Data} {st : BSess} (hC : st.C = D) (hS : st.S = D)
    (hR : st.R.bks = ∅) (hW : st.W.bks = ∅) :
    fkOk P (fkInit D) (fkWInit P D) st := by
  refine ⟨fun h0 => ?_, fun hw => ?_⟩
  · have hD := fkInit_zero h0
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hC]; exact hD
    · rw [hR]; exact fkAbsB_empty P
    · rw [hS]; exact hD
    · rw [hW]; exact fkAbsB_empty P
  · have hD := fkInit_wf hw
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hC]; exact hD
    · rw [hR]; exact fkWfB_of_abs (fkAbsB_empty P)
    · rw [hS]; exact hD
    · rw [hW]; exact fkWfB_of_abs (fkAbsB_empty P)

/-- A well-formed readers' state's value at a compaction key is well formed. -/
theorem fkWfRv_vOf {P : BParams} {rv : RView} {bi : BucketInfo} {kb v : GoString}
    (h : fkWfRv P rv) (hbi : P.has bi) (hk : fkKey bi.name kb)
    (hv : vOf P rv bi.name kb = some v) : P.FV v := by
  unfold vOf ovB at hv
  unfold BParams.has at hbi
  rw [hbi] at hv
  simp only [Option.bind_some] at hv
  cases hl : lastVal (bkOf rv.2.bks bi.id) kb with
  | some v' =>
    rw [hl] at hv
    simp only [Option.some_or] at hv
    cases hv
    unfold lastVal at hl
    cases hf : (bkOf rv.2.bks bi.id).reverse.find? (fun e => decide (e.1 = kb)) with
    | none => rw [hf] at hl; cases hl
    | some e =>
      rw [hf] at hl
      simp only [Option.map_some] at hl
      cases hl
      have hm := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      exact h.2 bi.name kb bi.id hk hbi e (List.mem_reverse.1 hm) (by simpa using he)
  | none =>
    rw [hl] at hv
    simp only [Option.none_or] at hv
    exact h.1 bi.name kb v hk hv

/-! ## The compaction keys' values at the open (`fkOkG`; M2 storage plan, items 27/29) -/

theorem fkValD_put {S : Data} {n k : GoString} {v : FkVals} (x : GoString) (h : fkValD v S)
    (hk : ¬ fkKey n k) : fkValD v (S.insert n ((bktOf S n).insert k x)) := by
  intro n' k' hf
  rw [dget_insert]
  split
  · rename_i hn
    subst hn
    rw [GMap.lookup_insert_eq_iff]
    split
    · rename_i hkk; subst hkk; exact absurd hf hk
    · rw [← dget_eq_bktOf]; exact h _ _ hf
  · exact h _ _ hf

theorem fkValD_delk {S : Data} {n k : GoString} {v : FkVals} (h : fkValD v S) (hk : ¬ fkKey n k) :
    fkValD v (S.insert n ((bktOf S n).delete k)) := by
  intro n' k' hf
  rw [dget_insert]
  split
  · rename_i hn
    subst hn
    rw [GMap.lookup_delete_iff]
    split
    · rename_i hkk; subst hkk; exact absurd hf hk
    · rw [← dget_eq_bktOf]; exact h _ _ hf
  · exact h _ _ hf

theorem fkValD_create {S : Data} {n : GoString} {v : FkVals} (h : fkValD v S) :
    fkValD v (if S.lookup n = none then S.insert n ∅ else S) := by
  split
  · rename_i hnone
    intro n' k' hf
    rw [dget_insert]
    split
    · rename_i hn
      subst hn
      have h0 := h _ _ hf
      unfold dget at h0
      rw [hnone] at h0
      rw [← h0]
      rfl
    · exact h _ _ hf
  · exact h

theorem fkValD_delete {S : Data} {n : GoString} {v : FkVals} (h : fkValD v S)
    (hn : ∀ k, ¬ fkKey n k) : fkValD v (S.delete n) := by
  intro n' k' hf
  unfold dget
  rw [GMap.lookup_delete_iff]
  split
  · rename_i hnn; subst hnn; exact absurd hf (hn k')
  · exact h _ _ hf

/-- bbolt's data holds its own compaction-key values. -/
theorem fkValD_fkVals (D : Data) : fkValD (fkVals D) D := by
  intro n k hf
  obtain ⟨rfl, hk⟩ := hf
  unfold fkAt fkVals
  rcases hk with rfl | rfl
  · simp only; split
    · rename_i h; exact absurd h (by decide)
    · rfl
  · simp

/-- A readers' state holding `v` at the compaction keys reads `v` at one. -/
theorem vOf_fkVal {P : BParams} {rv : RView} {v : FkVals} {bi : BucketInfo} {kb : GoString}
    (h : fkValRv P v rv) (hbi : P.has bi) (hk : fkKey bi.name kb) :
    vOf P rv bi.name kb = fkAt v kb := by
  unfold vOf ovB
  unfold BParams.has at hbi
  rw [hbi]
  simp only [Option.bind_some]
  have hl : lastVal (bkOf rv.2.bks bi.id) kb = none := by
    unfold lastVal
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro e he
    have := h.2 bi.name kb bi.id hk hbi e (List.mem_reverse.1 he)
    simpa using this
  rw [hl, Option.none_or]
  exact h.1 _ _ hk

theorem fkValSt_put {P : BParams} {st : BSess} {bi : BucketInfo} {k x : GoString} {v : FkVals}
    (seq : Bool) (hP : P.Wf) (hbi : P.has bi) (hk : ¬ fkKey bi.name k) (h : fkValSt P v st) :
    fkValSt P v (st.put bi k x seq) := by
  obtain ⟨hC, hR, hS, hW⟩ := h
  refine ⟨hC, hR, fkValD_put x hS hk, ?_⟩
  unfold BSess.put
  cases seq
  · exact fkAbsB_wbAdd hP hW hbi hk
  · exact fkAbsB_wbAdd hP hW hbi hk

theorem fkValSt_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString} {v : FkVals}
    (hk : ¬ fkKey bi.name k) (h : fkValSt P v st) : fkValSt P v (st.del bi k) :=
  ⟨h.1, h.2.1, fkValD_delk h.2.2.1 hk, h.2.2.2⟩

theorem fkValSt_create {P : BParams} {st : BSess} {bi : BucketInfo} {v : FkVals}
    (h : fkValSt P v st) : fkValSt P v (st.create bi) :=
  ⟨h.1, h.2.1, fkValD_create h.2.2.1, h.2.2.2⟩

theorem fkValSt_delBucket {P : BParams} {st : BSess} {bi : BucketInfo} {v : FkVals}
    (hn : ∀ k, ¬ fkKey bi.name k) (h : fkValSt P v st) : fkValSt P v (st.delBucket bi) :=
  ⟨h.1, h.2.1, fkValD_delete h.2.2.1 hn, h.2.2.2⟩

theorem fkValSt_wb {P : BParams} {st : BSess} {v : FkVals} (h : fkValSt P v st) :
    fkValSt P v (wbSt P st) :=
  ⟨h.1, fkAbsB_wbMerge h.2.2.2 h.2.1, h.2.2.1, fkAbsB_writebackW P st.W st.R⟩

theorem fkValSt_commit {P : BParams} {st : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt}
    {v : FkVals} (h : fkValSt P v st) (hC : C' = st.S ∨ C' = st.C) :
    fkValSt P v (commitSt st C' tx' cnt') := by
  refine ⟨?_, fkAbsB_bksReset P _, h.2.2.1, h.2.2.2⟩
  rcases hC with rfl | rfl
  · exact h.2.2.1
  · exact h.1

theorem fkOkG_put {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hP : P.Wf) (hbi : P.has bi) (hk : ¬ fkKey bi.name k) (f : Nat) (g : FkG)
    (h : fkOkG P f g st) : fkOkG P f g (st.put bi k v seq) :=
  ⟨fkOk_put seq hP hbi hk f g.1 h.1, h.2.1, fun he => fkValSt_put seq hP hbi hk (h.2.2 he)⟩

/-- A put of a compaction key, of a well-formed value: the flag raised by one, past the open's
value, so the records clause no longer applies. -/
theorem fkOkG_putFk {P : BParams} {st : BSess} {bi : BucketInfo} {k v : GoString} (seq : Bool)
    (hP : P.Wf) (hbi : P.has bi) (hv : P.FV v) (f : Nat) (g : FkG) (h : fkOkG P f g st) :
    fkOkG P (f + 1) g (st.put bi k v seq) := by
  refine ⟨⟨fun h0 => absurd h0 (by omega), fun hw => ?_⟩, by have := h.2.1; omega,
    fun he => absurd he (by have := h.2.1; omega)⟩
  exact (fkOk_putFk seq hP hbi hv f g.1 h.1).2 hw

theorem fkOkG_del {P : BParams} {st : BSess} {bi : BucketInfo} {k : GoString}
    (hk : ¬ fkKey bi.name k) (f : Nat) (g : FkG) (h : fkOkG P f g st) :
    fkOkG P f g (st.del bi k) :=
  ⟨fkOk_del f g.1 h.1, h.2.1, fun he => fkValSt_del hk (h.2.2 he)⟩

theorem fkOkG_create {P : BParams} {st : BSess} {bi : BucketInfo} (f : Nat) (g : FkG)
    (h : fkOkG P f g st) : fkOkG P f g (st.create bi) :=
  ⟨fkOk_create f g.1 h.1, h.2.1, fun he => fkValSt_create (h.2.2 he)⟩

theorem fkOkG_delBucket {P : BParams} {st : BSess} {bi : BucketInfo}
    (hn : ∀ k, ¬ fkKey bi.name k) (f : Nat) (g : FkG) (h : fkOkG P f g st) :
    fkOkG P f g (st.delBucket bi) :=
  ⟨fkOk_delBucket f g.1 h.1, h.2.1, fun he => fkValSt_delBucket hn (h.2.2 he)⟩

theorem fkOkG_wb {P : BParams} {st : BSess} (f : Nat) (g : FkG) (h : fkOkG P f g st) :
    fkOkG P f g (wbSt P st) :=
  ⟨fkOk_wb f g.1 h.1, h.2.1, fun he => fkValSt_wb (h.2.2 he)⟩

theorem fkOkG_commit {P : BParams} {st : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt}
    (hC : C' = st.S ∨ C' = st.C) (f : Nat) (g : FkG) (h : fkOkG P f g st) :
    fkOkG P f g (commitSt st C' tx' cnt') :=
  ⟨fkOk_commit hC f g.1 h.1, h.2.1, fun he => fkValSt_commit (h.2.2 he) hC⟩

theorem fkOkG_setHw {P : BParams} {st : BSess} (x : Bool) (f : Nat) (g : FkG)
    (h : fkOkG P f g st) : fkOkG P f g (st.setHw x) := h

/-- The readers' state of a batch state: at a flag not past the open's value, it is the open's. -/
theorem fkOkRvG_of {P : BParams} {st : BSess} {f : Nat} {g : FkG} (h : fkOkG P f g st) :
    fkOkRvG P f g (st.C, st.R) :=
  ⟨fkOkRv_of h.1, fun hle => by
    have he : f = g.2.1 := by have := h.2.1; omega
    exact ⟨(h.2.2 he).1, (h.2.2 he).2.1⟩⟩

/-- The initial state's facts at the open's ghost value. -/
theorem fkOkG_init {P : BParams} {D : Data} {st : BSess} (hC : st.C = D) (hS : st.S = D)
    (hR : st.R.bks = ∅) (hW : st.W.bks = ∅) :
    fkOkG P (fkInit D) (fkWInit P D, fkInit D, fkVals D) st := by
  refine ⟨fkOk_init hC hS hR hW, Nat.le_refl _, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hC]; exact fkValD_fkVals D
  · rw [hR]; exact fkAbsB_empty P
  · rw [hS]; exact fkValD_fkVals D
  · rw [hW]; exact fkAbsB_empty P

end backend
end EtcdGrove
end Perennial
