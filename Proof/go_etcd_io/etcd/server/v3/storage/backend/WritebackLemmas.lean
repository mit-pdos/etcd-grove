/-
The batch transaction's state across an `Unlock`'s write-back (`Model2.lean`): the facts
(`sessWf_writeback`), the bounds and counters (`bgOk_writeback`), the readers' view
(`vData_writeback_same`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-- The state after the write-back of `st`'s write buffer into its read buffer, with the
counters reset (`p0` the pending count, `e` the hook's leftovers moved into the read buffer). -/
def wbSt (P : BParams) (st : BSess) : BSess :=
  { st with R := writebackR st.W st.R, W := writebackW st.W st.R,
            cnt := ⟨0, 0, sint.nat st.pend, st.cnt.e + P.hookMax * st.cnt.c, false⟩ }

section wbSt_proj
variable (P : BParams) (st : BSess)
theorem wbSt_C : (wbSt P st).C = st.C := rfl
theorem wbSt_S : (wbSt P st).S = st.S := rfl
theorem wbSt_R : (wbSt P st).R = writebackR st.W st.R := rfl
theorem wbSt_W : (wbSt P st).W = writebackW st.W st.R := rfl
theorem wbSt_pend : (wbSt P st).pend = st.pend := rfl
theorem wbSt_ndel : (wbSt P st).ndel = st.ndel := rfl
theorem wbSt_tx : (wbSt P st).tx = st.tx := rfl
end wbSt_proj

theorem bkOf_writebackW (W : WBuf) (R : RBuf) (i : w64) : bkOf (writebackW W R).bks i = [] :=
  bkOf_bksResetC _ i

theorem idsOk_writebackW {P : BParams} {W : WBuf} {R : RBuf} (h : idsOk P W.bks) :
    idsOk P (writebackW W R).bks := by
  intro i es hi
  unfold writebackW WBuf.reset at hi
  change ((bksReset (W.bks.filter _)).lookup i) = some es at hi
  unfold bksReset at hi
  change (((W.bks.lookup i).filter _).filter _).map _ = some es at hi
  cases hb : W.bks.lookup i with
  | none => rw [hb] at hi; simp at hi
  | some es0 => exact h i es0 hb

theorem idsOk_wbR {P : BParams} {W : WBuf} {R : RBuf} (hW : idsOk P W.bks)
    (hR : idsOk P R.bks) : idsOk P (writebackR W R).bks := by
  intro i es h
  simp only [writebackR, wbMerge] at h
  change ((gmapImap _ W.bks).lookup i).or (R.bks.lookup i) = some es at h
  cases hw : W.bks.lookup i with
  | some es' => exact hW i es' hw
  | none =>
    have : (gmapImap (fun id es => canon (bkOf R.bks id ++ es)) W.bks).lookup i = none := by
      show (W.bks.lookup i).map _ = none; rw [hw]; rfl
    rw [this, Option.none_or] at h
    exact hR i es h

/-- What the readers see after the write-back: the write buffer over the read buffer. -/
theorem vOf_writeback (P : BParams) (C : Data) (W : WBuf) (R : RBuf) :
    vOf P (C, writebackR W R) = ovB P.BT W.bks (vOf P (C, R)) := by
  unfold vOf writebackR
  exact ovB_wbMerge P.BT W.bks R.bks (dget C)

/-- A write-back of a write buffer empty off the hook's buckets leaves the readers' view. -/
theorem vData_writeback_same (P : BParams) (C : Data) (W : WBuf) (R : RBuf)
    (hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf W.bks i = []) :
    vData P (C, writebackR W R) = vData P (C, R) := by
  apply vData_eq_of_agree
  rw [vOf_writeback]
  exact agreeOff_ovB_nonHB P W.bks _ hW

theorem mem_canon {l : List Ent} {e : Ent} (h : e ∈ canon l) : e ∈ l := by
  unfold canon at h
  exact List.mem_mergeSort.1 ((dedupLast_sublist _).subset h)

/-- An entry of a merged bucket is the read buffer's or the write buffer's. -/
theorem mem_bkOf_wbMerge {W R : GMap w64 (List Ent)} {i : w64} {e : Ent}
    (h : e ∈ bkOf (wbMerge W R) i) : e ∈ bkOf R i ∨ e ∈ bkOf W i := by
  rw [bkOf_wbMerge] at h
  unfold bkOf
  cases hw : W.lookup i with
  | none => rw [hw] at h; exact Or.inl h
  | some es =>
    rw [hw] at h
    rcases List.mem_append.1 (mem_canon h) with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)

/-- The write-back keeps the safe-range discipline: the merged read buffer's keys are the read
buffer's and the write buffer's, both above the committed ones. -/
theorem safeSt_writeback {P : BParams} {st : BSess} (hs : safeSt P st) : safeSt P (wbSt P st) := by
  refine ⟨?_, fun n i hn hsb => ⟨?_, (hs.2 n i hn hsb).2⟩⟩
  · intro n i hn hsb kc vc e hc he
    rcases mem_bkOf_wbMerge (W := st.W.bks) (R := st.R.bks) he with he | he
    · exact hs.1 n i hn hsb kc vc e hc he
    · exact (hs.2 n i hn hsb).1 kc vc e hc he
  · intro kc vc e _ he
    exact absurd he (by show e ∉ bkOf (writebackW st.W st.R).bks i; rw [bkOf_writebackW]; simp)

theorem sessWf_writeback {P : BParams} {st : BSess} (hst : sessWf P st) (hpn : st.pend ≠ W64 0) :
    sessWf P (wbSt P st) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag, hsf⟩ := hst
  refine ⟨WBuf.WfR.of_Wf _ (writebackW_wf _ _), writebackR_wf _ hRf, idsOk_writebackW hWi, idsOk_wbR hWi hRi,
    hp0, hp1, hn0, hnp, ?_, ?_, safeSt_writeback hsf⟩
  · intro hp
    exact absurd hp hpn
  · intro hn
    show agreeOff P.HB (dget st.S) (ovB P.BT (writebackW st.W st.R).bks
      (ovB P.BT (writebackR st.W st.R).bks (dget st.C)))
    rw [ovB_empty P.BT _ _ (bkOf_writebackW st.W st.R)]
    have := hag hn
    unfold viewOf at this
    show agreeOff P.HB (dget st.S) (vOf P (st.C, writebackR st.W st.R))
    rw [vOf_writeback]
    exact this

/-- Out of the hook's window, a write-buffer bucket repeats a key only where the read buffer has
no bucket: what the write-back needs. -/
theorem wfR_closed {st : BSess} (h : st.W.WfR (wbDupOk st)) (hw : st.cnt.hw = false) :
    st.W.WfR (fun id => st.R.bks.lookup id = none) := by
  apply h.mono
  intro i hi
  rcases hi with hi | ⟨hi, -⟩
  · exact hi
  · rw [hw] at hi; cases hi

/-- The bounds after a write-back (one write-back token spent, one write-back more). -/
theorem bgOk_writeback {P : BParams} {st : BSess} {n w u : Nat}
    (h : bgOk P st false n w u) (hn : 1 ≤ n) :
    bgOk P (wbSt P st) true (n - 1) (w + 1) u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  have hv : 0 ≤ uint.Z st.R.ver := by word
  have hk : st.cnt.k < 2 ^ 40 := by omega
  have hc : st.cnt.c ≤ st.cnt.k + 2 := by split at h3 <;> omega
  refine ⟨?_, by omega, by simp [wbSt], by simp [wbSt], ⟨Or.inr rfl, Or.inl rfl⟩, ?_, ?_, ?_, ?_⟩
  · show uint.Z (st.R.ver + W64 1) + ((n - 1 : Nat) : Int) + ((0 : Nat) : Int) < 2 ^ 40
    have : uint.Z (st.R.ver + W64 1) = uint.Z st.R.ver + 1 := by word
    omega
  · show st.cnt.e + P.hookMax * st.cnt.c ≤ P.hookMax * (2 ^ 40 + 2)
    rcases h5.1 with he | hc0
    · rw [he, Nat.zero_add]
      exact Nat.mul_le_mul_left _ (by omega)
    · rw [hc0, Nat.mul_zero, Nat.add_zero]
      exact h6
  · intro i
    obtain ⟨a1, a2⟩ := h7 i
    have hl := length_bkOf_wbMerge st.W.bks st.R.bks i
    refine ⟨by show (bkOf (writebackW st.W st.R).bks i).length ≤ _; rw [bkOf_writebackW]; simp, ?_⟩
    show (bkOf (wbMerge st.W.bks st.R.bks) i).length ≤ sint.nat st.pend + (st.cnt.e + P.hookMax * st.cnt.c)
    omega
  · intro nm i _ _
    show (bkOf (writebackW st.W st.R).bks i).length ≤ _
    rw [bkOf_writebackW]; simp
  · intro _
    exact ⟨rfl, fun _ => by omega⟩

theorem bgOk_unfree {P : BParams} {st : BSess} {n w u : Nat} (h : bgOk P st true n w u) :
    bgOk P st false n w u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by simp⟩

/-- After a write-back with nothing to commit, the lock's state is free. -/
theorem freeOk_writeback {P : BParams} {st : BSess} (hst : sessWf P st) (hpn : st.pend ≠ W64 0)
    (hl : sint.Z st.pend < sint.Z P.limit) (hd : ¬ 0 < sint.Z st.ndel) :
    freeOk P (wbSt P st) := by
  refine ⟨sessWf_writeback hst hpn, hl, ?_, fun _ i _ _ => bkOf_writebackW _ _ i, rfl⟩
  have := hst.2.2.2.2.2.2.1
  show st.ndel = W64 0
  word

/-- At pending count 0, the lock's state is free. -/
theorem free_of_pend0 {P : BParams} {st : BSess} {n w u : Nat} (hP : P.Wf) (hst : sessWf P st)
    (h : bgOk P st false n w u) (hp : st.pend = W64 0) (hhw : st.cnt.hw = false) :
    freeOk P st ∧ bgOk P st true n w u := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  have hp' : sint.nat st.pend = 0 := by rw [hp]; rfl
  refine ⟨⟨hst, ?_, ?_, ?_, hhw⟩, h1, h2, h3, h4, h5, h6, h7, h8, fun _ => ⟨by omega, fun h => absurd hp h⟩⟩
  · rw [hp]; exact hP.2.1
  · have h1 := hst.2.2.2.2.2.2.1
    have h2 := hst.2.2.2.2.2.2.2.1
    have : sint.Z st.pend = 0 := by rw [hp]; rfl
    word
  · intro nm i hn hh
    have := h8 nm i hn hh
    rw [hp'] at this
    exact List.eq_nil_of_length_eq_zero (by omega)

end backend
end EtcdGrove
end Perennial
