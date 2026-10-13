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

theorem dget_eq_bktOf (D : Data) (n k : GoString) : dget D n k = (bktOf D n).lookup k := by
  unfold dget bktOf
  cases D.lookup n <;> simp

/-- The writer's put leaves every other bucket, and keeps the put bucket's keys. -/
theorem bktOf_put_lookup (S : Data) (n k v n' kc : GoString) :
    (bktOf (S.insert n ((bktOf S n).insert k v)) n').lookup kc =
      if n = n' ∧ k = kc then some v else (bktOf S n').lookup kc := by
  rw [← dget_eq_bktOf, ← dget_eq_bktOf]
  exact dget_put S n k v n' kc

/-- A bucket's creation changes no bucket's contents (absent reads as empty). -/
theorem bktOf_create (S : Data) (n n' : GoString) :
    bktOf (if S.lookup n = none then S.insert n ∅ else S) n' = bktOf S n' := by
  split
  · rename_i h
    unfold bktOf
    simp only [GMap.lookup_insert_eq_iff]
    by_cases hn : n = n'
    · subst hn; simp [h]
    · simp [hn]
  · rfl

/-- A change of the writer's bucket `n` only leaves every other bucket. -/
theorem bktOf_insert_ne (S : Data) (n n' : GoString) (m : BktData) (h : n ≠ n') :
    bktOf (S.insert n m) n' = bktOf S n' := by
  unfold bktOf
  simp [GMap.lookup_insert_eq_iff, h]

theorem bktOf_delete_ne (S : Data) (n n' : GoString) (h : n ≠ n') :
    bktOf (S.delete n) n' = bktOf S n' := by
  unfold bktOf
  rw [GMap.lookup_delete_ne _ h]

/-- A put keeps the safe-range discipline, its key above the writer's contents of a safe-range
bucket. -/
theorem safeSt_put {P : BParams} {st : BSess} {bi : BucketInfo} {kb vb : GoString} {seq : Bool}
    (hP : P.Wf) (hb : P.has bi) (hs : safeSt P st)
    (hSB : P.SB bi.name = true → ∀ kc vc, (bktOf st.S bi.name).lookup kc = some vc → strLt kc kb) :
    safeSt P (st.put bi kb vb seq) := by
  have hWbks : (st.put bi kb vb seq).W.bks = wbAdd st.W.bks bi.id (kb, vb) := by
    unfold BSess.put; cases seq <;> rfl
  refine ⟨hs.1, fun n i hn hsb => ⟨?_, ?_⟩⟩
  · intro kc vc e hc he
    show strLt kc e.1
    rw [hWbks, bkOf_wbAdd] at he
    split at he
    · rename_i hi
      subst hi
      have hnm : bi.name = n := hP.1 _ _ _ hb hn
      subst hnm
      rcases List.mem_append.1 he with he | he
      · exact (hs.2 _ _ hn hsb).1 kc vc e hc he
      · rw [List.mem_singleton] at he
        subst he
        obtain ⟨vs, hvs⟩ := (hs.2 _ _ hn hsb).2 kc vc hc
        exact hSB hsb kc vs hvs
    · exact (hs.2 _ _ hn hsb).1 kc vc e hc he
  · intro kc vc hc
    obtain ⟨vs, hvs⟩ := (hs.2 _ _ hn hsb).2 kc vc hc
    show ∃ vs, (bktOf (st.S.insert bi.name ((bktOf st.S bi.name).insert kb vb)) n).lookup kc = some vs
    rw [bktOf_put_lookup]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨vs, hvs⟩

/-- An operation that changes only the writer's contents of a bucket that is not safe-range
keeps the discipline. -/
theorem safeSt_S_nonSB {P : BParams} {st st' : BSess} {name : GoString}
    (hs : safeSt P st) (hsb : P.SB name = false) (hC : st'.C = st.C) (hR : st'.R = st.R)
    (hW : st'.W = st.W) (hS : ∀ n, n ≠ name → bktOf st'.S n = bktOf st.S n) :
    safeSt P st' := by
  refine ⟨by rw [hC, hR]; exact hs.1, fun n i hn hsbn => ⟨?_, ?_⟩⟩
  · rw [hC, hW]; exact (hs.2 n i hn hsbn).1
  · have hne : n ≠ name := fun h => by subst h; rw [hsb] at hsbn; cases hsbn
    rw [hC, hS n hne]; exact (hs.2 n i hn hsbn).2

theorem sessWf_put {P : BParams} {st : BSess} {bi : BucketInfo} {kb vb : GoString} {seq : Bool}
    (hP : P.Wf) (hst : sessWf P st) (hb : P.has bi)
    (hW : if seq then ∀ e ∈ bkOf st.W.bks bi.id, strLt e.1 kb
      else kb ∉ (bkOf st.W.bks bi.id).map Prod.fst ∨ wbDupOk st bi.id)
    (hp : sint.Z st.pend + 1 < 2 ^ 58)
    (hSB : P.SB bi.name = true → ∀ kc vc, (bktOf st.S bi.name).lookup kc = some vc → strLt kc kb) :
    sessWf P (st.put bi kb vb seq) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag, hsf⟩ := hst
  have hWbks : (if seq then st.W.putSeq bi.id (kb, vb) else st.W.put bi.id (kb, vb)).bks =
      wbAdd st.W.bks bi.id (kb, vb) := by
    cases seq <;> rfl
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  refine ⟨?_, hRf, ?_, hRi, ?_, ?_, hn0, ?_, ?_, ?_, safeSt_put hP hb hsf hSB⟩
  · show (if seq then st.W.putSeq bi.id (kb, vb) else st.W.put bi.id (kb, vb)).WfR (wbDupOk st)
    cases seq
    · exact WBuf.WfR.put hWf (by simpa using hW)
    · exact WBuf.WfR.putSeq hWf (by simpa using hW)
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
    (hst : sessWf P st) (hp : sint.Z st.pend + 1 < 2 ^ 58) (hSB : P.SB bi.name = false) :
    sessWf P (st.del bi kb) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag, hsf⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hnz : sint.Z (st.ndel + W64 1) = sint.Z st.ndel + 1 := by word
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, ?_, ?_, ?_, ?_,
    safeSt_S_nonSB hsf hSB rfl rfl rfl (fun n hn => bktOf_insert_ne _ _ _ _ (Ne.symm hn))⟩
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
    (hst : sessWf P st) (hp : sint.Z st.pend + 1 < 2 ^ 58) (hSB : P.SB bi.name = false) :
    sessWf P (st.delBucket bi) := by
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag, hsf⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hnz : sint.Z (st.ndel + W64 1) = sint.Z st.ndel + 1 := by word
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, ?_, ?_, ?_, ?_,
    safeSt_S_nonSB hsf hSB rfl rfl rfl (fun n hn => bktOf_delete_ne _ _ _ (Ne.symm hn))⟩
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
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag, hsf⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hsf' : safeSt P (st.create bi) := by
    refine ⟨hsf.1, fun n i hn hsbn => ⟨(hsf.2 n i hn hsbn).1, ?_⟩⟩
    show ∀ kc vc, (bktOf st.C n).lookup kc = some vc →
      ∃ vs, (bktOf (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S) n).lookup kc = some vs
    rw [bktOf_create]; exact (hsf.2 n i hn hsbn).2
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, hn0, ?_, ?_, ?_, hsf'⟩
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
  have hm := hP.2.2.2.1
  have hmc : P.hookMax * st.cnt.c ≤ 2 ^ 16 * (2 ^ 40 + 2) :=
    Nat.mul_le_mul hm (by omega)
  have hme : st.cnt.e ≤ 2 ^ 16 * (2 ^ 40 + 2) :=
    Nat.le_trans h6 (Nat.mul_le_mul_right _ hm)
  have hpn : sint.nat st.pend < 2 ^ 58 := by have := hst.2.2.2.2.2.1; word
  unfold bufBound
  omega

/-! ## The hook's own keys (`hkData`) across a session's operations -/

theorem hkData_put_other {P : BParams} (st : BSess) (bi : BucketInfo) (kb vb : GoString)
    (seq : Bool) (h : P.hk bi.name kb = false) :
    hkData P (st.put bi kb vb seq).S = hkData P st.S := by
  apply hkData_eq
  intro n k hk
  show dget (st.S.insert bi.name ((bktOf st.S bi.name).insert kb vb)) n k = dget st.S n k
  rw [dget_put]
  split
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    rw [h] at hk; cases hk
  · rfl

theorem hkData_create {P : BParams} (st : BSess) (bi : BucketInfo) :
    hkData P (st.create bi).S = hkData P st.S := by
  apply hkData_eq
  intro n k _
  show dget (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S) n k = dget st.S n k
  rw [dget_create]

theorem hkData_del {P : BParams} (st : BSess) (bi : BucketInfo) (kb : GoString)
    (h : P.hk bi.name kb = false) :
    hkData P (st.del bi kb).S = hkData P st.S := by
  apply hkData_eq
  intro n k hk
  show dget (st.S.insert bi.name ((bktOf st.S bi.name).delete kb)) n k = dget st.S n k
  rw [dget_eq_bktOf, dget_eq_bktOf]
  by_cases hn : bi.name = n
  · subst hn
    have hne : kb ≠ k := fun he => by subst he; rw [h] at hk; cases hk
    unfold bktOf
    simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.getD_some]
    rw [GMap.lookup_delete_ne _ hne]
  · rw [bktOf_insert_ne _ _ _ _ hn]

theorem hkData_delBucket {P : BParams} (st : BSess) (bi : BucketInfo)
    (h : ∀ k, P.hk bi.name k = false) :
    hkData P (st.delBucket bi).S = hkData P st.S := by
  apply hkData_eq
  intro n k hk
  show dget (st.S.delete bi.name) n k = dget st.S n k
  rw [dget_eq_bktOf, dget_eq_bktOf]
  by_cases hn : bi.name = n
  · subst hn
    rw [h k] at hk; cases hk
  · rw [bktOf_delete_ne _ _ _ hn]

end backend
end EtcdGrove
end Perennial
