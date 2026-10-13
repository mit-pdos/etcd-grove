/-
The batch transaction's operations keep `sessWf` (`Model2.lean`): `put`, `del`, `create` and
`delBucket`, under the public specs' premises. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

theorem lastVal_append_single (l : List Ent) (e : Ent) (k : GoString) :
    lastVal (l ++ [e]) k = if e.1 = k then some e.2 else lastVal l k := by
  unfold lastVal
  rw [List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.find?_cons]
  by_cases h : e.1 = k <;> simp [h]

theorem bktOf_insert_lookup (S : Data) (n : GoString) (f : BktData → BktData) (n' : GoString) :
    (S.insert n (f (bktOf S n))).lookup n' =
      if n = n' then some (f (bktOf S n)) else S.lookup n' := by
  simp only [GMap.lookup_insert_eq_iff]

/-- `dget` after the writer's put. -/
theorem dget_put (S : Data) (n k v n' k' : GoString) :
    dget (S.insert n ((bktOf S n).insert k v)) n' k' =
      if n = n' ∧ k = k' then some v else dget S n' k' := by
  unfold dget
  rw [bktOf_insert_lookup]
  by_cases hn : n = n'
  · subst hn
    simp only [true_and, ↓reduceIte, Option.bind_some, GMap.lookup_insert_eq_iff]
    by_cases hk : k = k'
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      unfold bktOf
      cases S.lookup n <;> simp
  · simp [hn]

/-- The writer's bucket creation does not change what it reads. -/
theorem dget_create (S : Data) (n : GoString) :
    dget (if S.lookup n = none then S.insert n ∅ else S) = dget S := by
  funext n' k'
  split
  · rename_i h
    unfold dget
    simp only [GMap.lookup_insert_eq_iff]
    by_cases hn : n = n'
    · subst hn; simp [h]
    · simp [hn]
  · rfl

theorem sessWf_put {P : BParams} {st : BSess} {bi : BucketInfo} {kb vb : GoString} {seq : Bool}
    (hP : P.Wf) (hst : sessWf P st) (hb : P.has bi)
    (hW : if seq then ∀ e ∈ bkOf st.W.bks bi.id, strLt e.1 kb
      else kb ∉ (bkOf st.W.bks bi.id).map Prod.fst)
    (hp : sint.Z st.pend + 1 < 2 ^ 58) :
    sessWf P (st.put bi kb vb seq) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag⟩ := hst
  have hWbks : (if seq then st.W.putSeq bi.id (kb, vb) else st.W.put bi.id (kb, vb)).bks =
      wbAdd st.W.bks bi.id (kb, vb) := by
    cases seq <;> rfl
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  refine ⟨?_, hRf, ?_, hRi, ?_, ?_, hn0, ?_, ?_, ?_⟩
  · show (if seq then st.W.putSeq bi.id (kb, vb) else st.W.put bi.id (kb, vb)).Wf
    cases seq
    · exact WBuf.put_wf hWf (by simpa using hW)
    · exact WBuf.putSeq_wf hWf (by simpa using hW)
  · show idsOk P (if seq then st.W.putSeq bi.id (kb, vb) else st.W.put bi.id (kb, vb)).bks
    rw [hWbks]
    intro i es h
    simp only [wbAdd, GMap.lookup_insert_eq_iff] at h
    split at h
    · rename_i hi; subst hi; exact ⟨bi.name, hb⟩
    · exact hWi i es h
  · show 0 ≤ sint.Z (st.pend + W64 1); omega
  · show sint.Z (st.pend + W64 1) < 2 ^ 58; omega
  · show sint.Z st.ndel ≤ sint.Z (st.pend + W64 1); omega
  · intro h
    exfalso
    have : sint.Z (st.pend + W64 1) = 0 := by rw [show st.pend + W64 1 = W64 0 from h]; rfl
    omega
  · intro hn n hHB k
    have hag' := hag hn n hHB k
    show dget (st.S.insert bi.name ((bktOf st.S bi.name).insert kb vb)) n k =
      ovB P.BT (if seq then st.W.putSeq bi.id (kb, vb) else st.W.put bi.id (kb, vb)).bks
        (viewOf P st) n k
    rw [hWbks, dget_put]
    unfold ovB at hag' ⊢
    by_cases hnk : bi.name = n ∧ kb = k
    · obtain ⟨rfl, rfl⟩ := hnk
      simp only [and_self, ↓reduceIte]
      rw [show P.BT.lookup bi.name = some bi.id from hb]
      simp [bkOf_wbAdd, lastVal_append_single]
    · simp only [hnk, ↓reduceIte]
      rw [hag']
      congr 1
      cases hl : P.BT.lookup n with
      | none => rfl
      | some i =>
        simp only [Option.bind_some]
        rw [bkOf_wbAdd]
        split
        · rename_i hi
          subst hi
          have hn' : bi.name = n := hP.1 _ _ _ hb hl
          have hk : ¬ kb = k := fun h => hnk ⟨hn', h⟩
          rw [lastVal_append_single]
          simp [hk]
        · rfl

theorem sessWf_del {P : BParams} {st : BSess} {bi : BucketInfo} {kb : GoString}
    (hst : sessWf P st) (hp : sint.Z st.pend + 1 < 2 ^ 58) :
    sessWf P (st.del bi kb) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hnz : sint.Z (st.ndel + W64 1) = sint.Z st.ndel + 1 := by word
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 ≤ sint.Z (st.pend + W64 1); omega
  · show sint.Z (st.pend + W64 1) < 2 ^ 58; omega
  · show 0 ≤ sint.Z (st.ndel + W64 1); omega
  · show sint.Z (st.ndel + W64 1) ≤ sint.Z (st.pend + W64 1); omega
  · intro h
    exfalso
    have : sint.Z (st.pend + W64 1) = 0 := by rw [show st.pend + W64 1 = W64 0 from h]; rfl
    omega
  · intro h
    exfalso
    have : sint.Z (st.ndel + W64 1) = 0 := by rw [show st.ndel + W64 1 = W64 0 from h]; rfl
    omega

theorem sessWf_delBucket {P : BParams} {st : BSess} {bi : BucketInfo}
    (hst : sessWf P st) (hp : sint.Z st.pend + 1 < 2 ^ 58) :
    sessWf P (st.delBucket bi) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hnz : sint.Z (st.ndel + W64 1) = sint.Z st.ndel + 1 := by word
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 ≤ sint.Z (st.pend + W64 1); omega
  · show sint.Z (st.pend + W64 1) < 2 ^ 58; omega
  · show 0 ≤ sint.Z (st.ndel + W64 1); omega
  · show sint.Z (st.ndel + W64 1) ≤ sint.Z (st.pend + W64 1); omega
  · intro h
    exfalso
    have : sint.Z (st.pend + W64 1) = 0 := by rw [show st.pend + W64 1 = W64 0 from h]; rfl
    omega
  · intro h
    exfalso
    have : sint.Z (st.ndel + W64 1) = 0 := by rw [show st.ndel + W64 1 = W64 0 from h]; rfl
    omega

theorem sessWf_create {P : BParams} {st : BSess} {bi : BucketInfo}
    (hst : sessWf P st) (hp : sint.Z st.pend + 1 < 2 ^ 58) :
    sessWf P (st.create bi) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, hn0, ?_, ?_, ?_⟩
  · show 0 ≤ sint.Z (st.pend + W64 1); omega
  · show sint.Z (st.pend + W64 1) < 2 ^ 58; omega
  · show sint.Z st.ndel ≤ sint.Z (st.pend + W64 1); omega
  · intro h
    exfalso
    have : sint.Z (st.pend + W64 1) = 0 := by rw [show st.pend + W64 1 = W64 0 from h]; rfl
    omega
  · intro hn
    show agreeOff P.HB (dget (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S))
      (ovB P.BT st.W.bks (viewOf P st))
    rw [dget_create]
    exact hag hn

/-! ## The buffers' size bounds (`bgOk`) -/

/-- An operation of a session (one more pending operation, at most one more entry per bucket of
the write buffer) keeps the bounds. -/
theorem bgOk_step {P : BParams} {st st' : BSess} {n w u : Nat}
    (h : bgOk P st false n w u) (hR : st'.R = st.R) (hc : st'.cnt = st.cnt)
    (hp : sint.nat st'.pend = sint.nat st.pend + 1)
    (hW : ∀ i, (bkOf st'.W.bks i).length ≤ (bkOf st.W.bks i).length + 1) :
    bgOk P st' false n w u := by
  unfold bgOk at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  rw [hR, hc]
  refine ⟨h1, h2, h3, by omega, h5, h6, ?_, ?_, by simp⟩
  · intro i
    obtain ⟨a1, a2⟩ := h7 i
    have := hW i
    constructor <;> omega
  · intro nm i hnm hHB
    have := h8 nm i hnm hHB
    have := hW i
    omega

theorem put_W_le (st : BSess) (bi : BucketInfo) (kb vb : GoString) (seq : Bool) (i : w64) :
    (bkOf (st.put bi kb vb seq).W.bks i).length ≤ (bkOf st.W.bks i).length + 1 := by
  have h : (st.put bi kb vb seq).W.bks = wbAdd st.W.bks bi.id (kb, vb) := by
    unfold BSess.put; cases seq <;> rfl
  rw [h, bkOf_wbAdd]
  split
  · rename_i hi; subst hi; simp
  · omega

theorem pend_succ_nat {st : BSess} {P : BParams} (hst : sessWf P st)
    (hp : sint.Z st.pend + 1 < 2 ^ 58) :
    sint.nat (st.pend + W64 1) = sint.nat st.pend + 1 := by
  have := hst.2.2.2.2.1
  word

/-- The bounds keep every bucket of both buffers below `bufBound`. -/
theorem bgOk_bufBound {P : BParams} {st : BSess} {free : Bool} {n w u : Nat}
    (hP : P.Wf) (hst : sessWf P st) (h : bgOk P st free n w u) (i : w64) :
    (bkOf st.R.bks i).length + (bkOf st.W.bks i).length < bufBound := by
  unfold bgOk at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := h
  obtain ⟨a1, a2⟩ := h7 i
  have hv : 0 ≤ uint.Z st.R.ver := by word
  have hk : st.cnt.k < 2 ^ 40 := by omega
  have hc : st.cnt.c ≤ st.cnt.k + 2 := by split at h3 <;> omega
  have hm := hP.2.2.2
  have hmc : P.hookMax * st.cnt.c ≤ 2 ^ 16 * (2 ^ 40 + 2) :=
    Nat.mul_le_mul hm (by omega)
  have hme : st.cnt.e ≤ 2 ^ 16 * (2 ^ 40 + 2) :=
    Nat.le_trans h6 (Nat.mul_le_mul_right _ hm)
  have hpn : sint.nat st.pend < 2 ^ 58 := by have := hst.2.2.2.2.2.1; word
  unfold bufBound
  omega

end backend
end EtcdGrove
end Perennial
