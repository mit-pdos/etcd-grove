/- Lean-first (no Rocq counterpart).

# The segments of a prefix of a history (pure; `walCrash_pure`'s encoding facts)

A history `P` that agrees with `Q` up to the last cut `c` and whose operations from `c` on have
records that are a prefix of `Q`'s (a prefix `Q.take m`, `c ≤ m`; a crash image of `Q` at or past
`c`: `walImg_segPre`): the segments' records agree but for the last, whose records are a prefix of
`Q`'s (`segs_pre`); a cut position of `Q` below `c` is one of `P`'s, and the entry index before it
the same.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalHistLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section segpre
variable [GooseExts]

/-! ## Cut positions -/

theorem segStart_length (cuts : List Nat) :
    segStart cuts cuts.length = (cuts.getLast?).getD 0 := by
  unfold segStart
  cases cuts with
  | nil => rfl
  | cons a t => simp [List.getLast?_eq_getElem?]

theorem le_getLast?_getD {cuts : List Nat} (h : cuts.Pairwise (· < ·)) :
    ∀ b ∈ cuts, b ≤ (cuts.getLast?).getD 0 := by
  induction cuts with
  | nil => intro b hb; cases hb
  | cons a t ih =>
    intro b hb
    rw [List.pairwise_cons] at h
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hb; subst hb; simp
    | cons x t' =>
      have hl : (a :: x :: t').getLast? = (x :: t').getLast? := by simp [List.getLast?_cons_cons]
      rw [hl]
      rcases List.mem_cons.1 hb with rfl | hb
      · have hx := ih h.2 _ (List.mem_cons_self ..)
        have := h.1 x (List.mem_cons_self ..)
        omega
      · exact ih h.2 b hb

/-- Every cut is at most the last segment's start. -/
theorem le_segStart_length {cuts : List Nat} (h : cuts.Pairwise (· < ·)) :
    ∀ b ∈ cuts, b ≤ segStart cuts cuts.length := by
  rw [segStart_length]; exact le_getLast?_getD h

/-- Every segment starts at most where the last does. -/
theorem segStart_le_length {cuts : List Nat} (h : cuts.Pairwise (· < ·)) (i : Nat) :
    segStart cuts i ≤ segStart cuts cuts.length := by
  have e : segStart cuts i = ((0 :: cuts)[i]?).getD 0 := by
    unfold segStart; rw [List.getD_eq_getElem?_getD]
  rw [e]
  cases hi : (0 :: cuts)[i]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    rcases List.mem_cons.1 (List.mem_of_getElem? hi) with rfl | hx
    · exact Nat.zero_le _
    · exact le_segStart_length h x hx

/-! ## The segments, split at the last cut -/

/-- The segments before the last. -/
def segsInit (H : WalHist) (cuts : List Nat) : List WalHist :=
  (List.zip (0 :: cuts).dropLast cuts).map (fun be => (H.drop be.1).take (be.2 - be.1))

theorem zip_snoc_shift (L : Nat) : ∀ (a : Nat) (cuts : List Nat),
    List.zip (a :: cuts) (cuts ++ [L]) =
      List.zip (a :: cuts).dropLast cuts ++ [((a :: cuts).getLast (by simp), L)]
  | a, [] => rfl
  | a, b :: t => by
    have ih := zip_snoc_shift L b t
    simp only [List.cons_append, List.zip_cons_cons, List.dropLast_cons_cons, List.getLast_cons_cons]
    rw [ih]

theorem getLast_zero_cons (cuts : List Nat) :
    (0 :: cuts).getLast (by simp) = segStart cuts cuts.length := by
  rw [segStart_length, List.getLast_eq_getElem]
  cases cuts with
  | nil => rfl
  | cons a t => simp [List.getLast?_eq_getElem?]

theorem segsOf_split (H : WalHist) (cuts : List Nat) :
    segsOf H cuts = segsInit H cuts ++ [H.drop (segStart cuts cuts.length)] := by
  unfold segsOf segsInit
  rw [zip_snoc_shift, List.map_append, getLast_zero_cons]
  simp only [List.map_cons, List.map_nil]
  rw [List.take_of_length_le (by simp)]

theorem length_segsInit (H : WalHist) (cuts : List Nat) : (segsInit H cuts).length = cuts.length := by
  unfold segsInit; simp

theorem segsInit_congr {P Q : WalHist} {cuts : List Nat} {c : Nat} (hc : ∀ b ∈ cuts, b ≤ c)
    (h : P.take c = Q.take c) : segsInit P cuts = segsInit Q cuts := by
  unfold segsInit
  apply List.map_congr_left
  intro be hbe
  have hb : be.2 ∈ cuts := (List.of_mem_zip hbe).2
  have e : ∀ L : WalHist, (L.drop be.1).take (be.2 - be.1) = ((L.take c).take be.2).drop be.1 := by
    intro L
    rw [List.take_take, Nat.min_eq_left (hc _ hb), List.drop_take]
  rw [e P, e Q, h]

/-! ## The records of the segments -/

theorem length_segsDs (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist), (segsDs M md first P Ss).length = Ss.length
  | _, _, [] => rfl
  | _, _, _ :: Ss => by simp [segsDs, length_segsDs M md false _ Ss]

theorem length_chainSegs (C : WalCodec) :
    ∀ (c : w32) (Ds : List (List (w64 × List w8))), (chainSegs C c Ds).length = Ds.length
  | _, [] => rfl
  | _, _ :: Ds => by simp [chainSegs, length_chainSegs C _ Ds]

theorem chainSegs_snoc (C : WalCodec) :
    ∀ (c : w32) (Ds : List (List (w64 × List w8))) (D : List (w64 × List w8)),
    chainSegs C c (Ds ++ [D]) = chainSegs C c Ds ++ [chainRecs C (crcAfter C c Ds.flatten) D]
  | c, [], D => by simp [chainSegs, crcAfter]
  | c, D' :: Ds, D => by
    simp only [List.cons_append, chainSegs, List.flatten_cons, crcAfter_append]
    rw [chainSegs_snoc C _ Ds D]

theorem segsDs_snoc (M : WalMarshal) (md : List w8) (A : List WalHist) (S : WalHist) :
    segsDs M md true [] (A ++ [S]) = segsDs M md true [] A ++
      [segHdrDs M md (if A = [] then true else false) A.flatten ++ S.flatMap (opDs M)] := by
  rw [segsDs_append]
  simp [segsDs]

/-- **The segments' records of a history agreeing with `Q` up to the last cut, its records after
it a prefix of `Q`'s**: all of them a prefix of `Q`'s; each segment's but the last the same; the
last's a prefix. -/
theorem segs_pre (C : WalCodec) (M : WalMarshal) (md : List w8) {P Q : WalHist}
    {cuts : List Nat} (hc : ∀ b ∈ cuts, b ≤ segStart cuts cuts.length)
    (ht : P.take (segStart cuts cuts.length) = Q.take (segStart cuts cuts.length))
    (hp : (P.drop (segStart cuts cuts.length)).flatMap (opDs M) <+:
      (Q.drop (segStart cuts cuts.length)).flatMap (opDs M)) :
    recsOfSegs C M md (segsOf P cuts) <+: recsOfSegs C M md (segsOf Q cuts) ∧
    (∀ k, k < cuts.length →
      (chainSegs C 0#32 (segsDs M md true [] (segsOf P cuts))).getD k [] =
        (chainSegs C 0#32 (segsDs M md true [] (segsOf Q cuts))).getD k []) ∧
    (chainSegs C 0#32 (segsDs M md true [] (segsOf P cuts))).getD cuts.length [] <+:
      (chainSegs C 0#32 (segsDs M md true [] (segsOf Q cuts))).getD cuts.length [] := by
  rw [segsOf_split P, segsOf_split Q, segsInit_congr hc ht]
  have hA := length_segsInit Q cuts
  generalize segsInit Q cuts = A at hA ⊢
  rw [segsDs_snoc, segsDs_snoc]
  generalize hh : segHdrDs M md (if A = [] then true else false) A.flatten = hdr
  have hl : (chainSegs C 0#32 (segsDs M md true [] A)).length = cuts.length := by
    rw [length_chainSegs, length_segsDs, hA]
  refine ⟨?_, ?_, ?_⟩
  · unfold recsOfSegs
    rw [segsDs_snoc, segsDs_snoc, hh, List.flatten_append, List.flatten_append]
    apply chainRecs_prefix
    rw [List.prefix_append_right_inj]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.prefix_append_right_inj]
    exact hp
  · intro k hk
    rw [chainSegs_snoc, chainSegs_snoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · rw [chainSegs_snoc, chainSegs_snoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    apply chainRecs_prefix
    rw [List.prefix_append_right_inj]
    exact hp

/-! ## Histories agreeing up to the last cut -/

theorem flatMap_take_prefix {α β : Type} (f : α → List β) (L : List α) (n : Nat) :
    (L.take n).flatMap f <+: L.flatMap f := by
  conv => rhs; rw [← List.take_append_drop n L]
  rw [List.flatMap_append]
  exact List.prefix_append _ _

/-- A prefix `Q.take m` of `Q`, the last cut at most `m`. -/
theorem take_segPre {Q : WalHist} {c m : Nat} (M : WalMarshal) (hcm : c ≤ m) :
    (Q.take m).take c = Q.take c ∧
      ((Q.take m).drop c).flatMap (opDs M) <+: (Q.drop c).flatMap (opDs M) := by
  refine ⟨by rw [List.take_take, Nat.min_eq_left hcm], ?_⟩
  rw [List.drop_take]
  exact flatMap_take_prefix _ _ _

/-- A crash image of `Q` at or past the last cut. -/
theorem walImg_segPre {Q I : WalHist} {c m : Nat} (M : WalMarshal) (hI : walImg Q m I)
    (hcm : c ≤ m) :
    I.take c = Q.take c ∧ (I.drop c).flatMap (opDs M) <+: (Q.drop c).flatMap (opDs M) := by
  obtain ⟨j, h1, h2, rfl | ⟨h, es, k, hj, hk, rfl⟩⟩ := hI
  · exact take_segPre M (by omega)
  · have hjl : j < Q.length := by
      rcases Nat.lt_or_ge j Q.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj; cases hj
    have htj : (Q.take j).length = j := by simp; omega
    refine ⟨?_, ?_⟩
    · rw [List.take_append_of_le_length (by omega), List.take_take, Nat.min_eq_left (by omega)]
    · rw [List.drop_append_of_le_length (by omega), List.flatMap_append, List.drop_take]
      have hQ : Q.drop c = (Q.drop c).take (j - c) ++ Q.drop j := by
        conv => lhs; rw [← List.take_append_drop (j - c) (Q.drop c)]
        rw [List.drop_drop, Nat.add_sub_cancel' (by omega)]
      have hQj : Q.drop j = .save h es :: Q.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hjl]
        rw [List.getElem?_eq_getElem hjl] at hj
        injection hj with hj
        rw [hj]
      conv => rhs; rw [hQ, hQj]
      rw [List.flatMap_append, List.prefix_append_right_inj, List.flatMap_cons,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      apply List.IsPrefix.trans _ (List.prefix_append _ _)
      simp only [opDs]
      rw [ite_eq_left hsEmptyP_zero, List.append_nil, List.map_take]
      exact List.IsPrefix.trans (List.take_prefix _ _) (List.prefix_append _ _)

/-- A cut position below where two histories agree is a cut position of both. -/
theorem walCutPos_of_take {P Q : WalHist} {b c : Nat} (hbc : b ≤ c) (ht : P.take c = Q.take c)
    (h : walCutPos Q b) : walCutPos P b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact Or.inl rfl
  rcases h with h | ⟨hs, es, hq, hne⟩
  · exact Or.inl h
  · right
    refine ⟨hs, es, ?_, hne⟩
    · have e : ∀ L : WalHist, L[b - 1]? = (L.take c)[b - 1]? := fun L => by
        rw [List.getElem?_take_of_lt (by omega)]
      rw [e P, ht, ← e Q]; exact hq

theorem take_of_take {P Q : WalHist} {b c : Nat} (hbc : b ≤ c) (ht : P.take c = Q.take c) :
    P.take b = Q.take b := by
  have e : ∀ L : WalHist, L.take b = (L.take c).take b := fun L => by
    rw [List.take_take, Nat.min_eq_left hbc]
  rw [e P, ht, ← e Q]

/-- The frames of a prefix of records are a prefix of the frames. -/
theorem recFrames_prefix (C : WalCodec) {xs ys : List WalRec} (h : xs <+: ys) :
    recFrames C xs <+: recFrames C ys := by
  obtain ⟨zs, rfl⟩ := h
  rw [recFrames_append]; exact List.prefix_append _ _

end segpre

end WalFs
end EtcdGrove
end Perennial

end
