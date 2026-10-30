/-
Lean-first (no Rocq counterpart).

# The applier's table and the history, pure (2026-10-29, track C)

`examples/kv`'s lemmas (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Lemmas.lean`, "The applier's
table, pure"), over kvreconf's model (`Base.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The applier's table, pure -/

theorem histStep_mem (L : List (List w8)) (d : List w8) (h : d ∈ L) : histStep L (some d) = L := by
  show (if d ∈ L then _ else _) = _; rw [ite_eq_left h]

theorem histStep_nmem (L : List (List w8)) (d : List w8) (h : d ∉ L) :
    histStep L (some d) = L ++ [d] := by
  show (if d ∈ L then _ else _) = _; rw [ite_eq_right h]

theorem appliedOk_skip (A : GMap (List w8) (List w8)) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hd : decodeOp d = none ∨ d ∈ L) : AppliedOk A (histStep L (some d)) := by
  by_cases Hm : d ∈ L
  · rw [histStep_mem L d Hm]; exact HA
  · have Hd' : decodeOp d = none := by rcases Hd with h | h; exact h; exact absurd h Hm
    rw [histStep_nmem L d Hm]
    refine ⟨fun d' => ?_, fun d' v h => ansOk_mono _ _ _ _ (List.prefix_append _ _) (HA.2 d' v h)⟩
    rw [HA.1 d']
    by_cases Heq : d' = d
    · subst Heq; simp [Hd', Hm]
    · simp [List.mem_append, Heq]

/-- (2026-10-22) The first occurrence of `d` applied: the table records its answer, the key's
value after it. -/
theorem appliedOk_insert (A : GMap (List w8) (List w8)) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hm : d ∉ L) (Hd : (decodeOp d).isSome) :
    AppliedOk (A.insert d (kvFold (L ++ [d]) (dkey d))) (L ++ [d]) := by
  refine ⟨fun d' => ?_, fun d' v h => ?_⟩
  · show (A.insert d (kvFold (L ++ [d]) (dkey d)) !! d').isSome ↔ _
    by_cases Heq : d' = d
    · subst Heq; rw [GMap.lookup_insert_eq]; simp [Hd]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq), HA.1 d']
      simp [List.mem_append, Heq]
  · by_cases Heq : d' = d
    · subst Heq
      have h' : A.insert d' (kvFold (L ++ [d']) (dkey d')) !! d' = some v := h
      rw [GMap.lookup_insert_eq] at h'
      cases h'
      exact ansOk_last L d' Hm
    · have h' : A.insert d (kvFold (L ++ [d]) (dkey d)) !! d' = some v := h
      rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at h'
      exact ansOk_mono _ _ _ _ (List.prefix_append _ _) (HA.2 d' v h')

theorem appliedOk_lookup (A : GMap (List w8) (List w8)) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hd : (decodeOp d).isSome) : (A !! d).isSome = decide (d ∈ L) := by
  have h := HA.1 d
  by_cases Hm : d ∈ L
  · simp only [Hm, Hd, and_self, iff_true] at h; simp [Hm, h]
  · simp only [Hm, false_and, iff_false] at h; simp [Hm, h]

/-- A datum's first occurrence in `ods`: at `m`, not in the history before it. -/
theorem histOf_first (ods : List (Option (List w8))) (d : List w8) (h : some d ∈ ods) :
    ∃ m, ods[m]? = some (some d) ∧ d ∉ histOf (ods.take m) := by
  suffices H : ∃ m, ods[m]? = some (some d) ∧ some d ∉ ods.take m by
    obtain ⟨m, h1, h2⟩ := H
    exact ⟨m, h1, fun h' => h2 ((mem_histOf _ d).1 h')⟩
  induction ods with
  | nil => cases h
  | cons x ods ih =>
    by_cases hx : x = some d
    · subst hx; exact ⟨0, rfl, by simp⟩
    · have hin : some d ∈ ods := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨m, hm, hm2⟩ := ih hin
      refine ⟨m + 1, by simpa using hm, ?_⟩
      simp only [List.take_succ_cons, List.mem_cons, not_or]
      exact ⟨fun h' => hx h'.symm, hm2⟩

/-- (2026-10-22) Where the answer of an operation of the history `histOf ods` comes from: the
entry of its first occurrence in `ods`, at `m`, after which the key's value is the answer (what
`waitP` says of an answer). -/
theorem ansOk_histOf (ods : List (Option (List w8))) (d v : List w8)
    (h : AnsOk (histOf ods) d v) :
    ∃ m, ods[m]? = some (some d) ∧ d ∉ histOf (ods.take m) ∧
      v = kvFold (histOf (ods.take m) ++ [d]) (dkey d) := by
  obtain ⟨H0, Hpre, -, Hv⟩ := h
  obtain ⟨m, hm, hm2⟩ :=
    histOf_first ods d ((mem_histOf ods d).1 (Hpre.subset (by simp)))
  have Hsplit : ods.take (m + 1) = ods.take m ++ [some d] := by
    rw [List.take_add_one, hm]; rfl
  have Hp1 : histOf (ods.take m) ++ [d] <+: histOf ods := by
    have h1 : histOf (ods.take (m + 1)) = histOf (ods.take m) ++ [d] := by
      rw [Hsplit, histOf_snoc, histStep_nmem _ _ hm2]
    rw [← h1]
    have h2 := histOf_append_prefix (ods.take (m + 1)) (ods.drop (m + 1))
    rwa [List.take_append_drop] at h2
  have HH0 := hist_prefix_before_unique (histOf ods) H0 (histOf (ods.take m)) d
    (histOf_nodup ods) Hpre Hp1
  subst HH0
  exact ⟨m, hm, hm2, Hv⟩

theorem histOf_prefix_of_prefix (a b : List (Option (List w8))) (h : a <+: b) :
    histOf a <+: histOf b := by
  obtain ⟨t, rfl⟩ := h
  exact histOf_append_prefix a t

/-- The history of a log's prefix `l` is a prefix of the history of committed requested entries
`ops` extending its requested entries. -/
theorem logHist_le_ops [GooseExts] (l ops : List LogEntry) (h : opsOf l <+: ops) :
    logHist l <+: logHist ops := by
  rw [← logHist_opsOf l]; exact logHist_prefix _ _ h


/-- After `r.kv[key] = val`. -/
theorem kvMap_put (K : GMap (List w8) (List w8)) (m : KVMap) (key val : List w8)
    (h : ∀ k, (K !! k).getD [] = m k) :
    ∀ k, ((<[key := val]> K) !! k).getD [] = kvUpd m key val k := by
  intro k
  by_cases hk : k = key
  · subst hk; rw [GMap.lookup_insert, kvUpd_same]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), kvUpd_other _ _ _ _ hk]; exact h k

/-- The odOf of a normal entry with data. -/
theorem odOf_normal [GooseExts] (e : LogEntry) (ht : e.type = W32 0) (hd : e.data ≠ []) :
    odOf e = some e.data := by
  unfold odOf; rw [if_pos ⟨ht, hd⟩]

/-- The odOf of an entry without data. -/
theorem odOf_nil [GooseExts] (e : LogEntry) (hd : e.data = []) : odOf e = none := by
  unfold odOf; rw [if_neg (fun h => h.2 hd)]

/-- A decodable datum is not empty. -/
theorem decodeOp_ne_nil (d : List w8) (x : w64 × w8 × List w8 × List w8)
    (h : decodeOp d = some x) : d ≠ [] := by
  rintro rfl; simp [decodeOp] at h

theorem logHist_snoc [GooseExts] (l : List LogEntry) (e : LogEntry) :
    logHist (l ++ [e]) = histStep (logHist l) (odOf e) := by
  unfold logHist; rw [List.map_append, List.map_singleton, histOf_snoc]

/-- The replicated state past an entry that changes nothing: one without a datum, an undecodable
datum, or a datum applied before. -/
theorem hist_skip [GooseExts] (ap : List LogEntry) (e : LogEntry) (K A : GMap (List w8) (List w8))
    (HA : AppliedOk A (logHist ap)) (Hval : ∀ k, (K !! k).getD [] = kvFold (logHist ap) k)
    (Hs : odOf e = none ∨ ∃ d, odOf e = some d ∧ (decodeOp d = none ∨ d ∈ logHist ap)) :
    (∀ k, (K !! k).getD [] = kvFold (logHist (ap ++ [e])) k) ∧ AppliedOk A (logHist (ap ++ [e])) := by
  rw [logHist_snoc]
  rcases Hs with Ho | ⟨d, Ho, Hd⟩
  · rw [Ho]; exact ⟨Hval, HA⟩
  · rw [Ho]
    refine ⟨?_, appliedOk_skip A _ d HA Hd⟩
    by_cases Hm : d ∈ logHist ap
    · rw [histStep_mem _ d Hm]; exact Hval
    · have Hd0 : decodeOp d = none := by rcases Hd with h | h; exact h; exact absurd h Hm
      rw [histStep_nmem _ d Hm, kvFold_snoc, kvApply_none _ _ Hd0]; exact Hval

/-- The replicated state past the first occurrence of an operation `d`: a `Put` sets its key, and
the table records the key's value after it. -/
theorem hist_insert [GooseExts] (ap : List LogEntry) (e : LogEntry) (K A : GMap (List w8) (List w8))
    (d : List w8) (i : w64) (kd : w8) (key val : List w8)
    (HA : AppliedOk A (logHist ap)) (Hval : ∀ k, (K !! k).getD [] = kvFold (logHist ap) k)
    (Ho : odOf e = some d) (Hm : d ∉ logHist ap) (Hdec : decodeOp d = some (i, kd, key, val))
    (K' : GMap (List w8) (List w8)) (HK' : K' = if kd = opPutB then <[key := val]> K else K) :
    (∀ k, (K' !! k).getD [] = kvFold (logHist (ap ++ [e])) k) ∧
      AppliedOk (A.insert d ((K' !! key).getD [])) (logHist (ap ++ [e])) := by
  rw [logHist_snoc, Ho, histStep_nmem _ d Hm]
  have HappE : kvApply (kvFold (logHist ap)) d = kvNext kd key val (kvFold (logHist ap)) := by
    simp [kvApply, Hdec]
  have HvalN : ∀ k, (K' !! k).getD [] = kvFold (logHist ap ++ [d]) k := by
    intro k
    rw [kvFold_snoc, HappE, HK']
    unfold kvNext
    by_cases hp : kd = opPutB
    · rw [if_pos hp, if_pos hp]; exact kvMap_put K _ key val Hval k
    · rw [if_neg hp, if_neg hp]; exact Hval k
  refine ⟨HvalN, ?_⟩
  have Hk : dkey d = key := by simp [dkey, Hdec]
  have := appliedOk_insert A _ d HA Hm (by rw [Hdec]; rfl)
  rwa [← Hk, HvalN]

end kvreconf
end EtcdGrove
end Perennial
