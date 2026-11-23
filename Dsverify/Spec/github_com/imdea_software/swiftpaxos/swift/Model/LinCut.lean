/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/LinCut.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/l2-design.md §5, notes/prove-s2-d.md): the linearization order of the present and the
predictions, and **the strategy invariant** `StratOk` with its steps (W1-W3).

* The cut: `cutS N Ns S P`, the final state of the maximal valid cut of the predictions `P` from
  the present state `S` (`Cut.nfOf` with `okE`/`apE`): unique by locality (Trace.lean, `diamond`),
  kept by every real event (`cutS_rep`, `cutS_inv`, `cutS_resp`; a real pre-acceptance's path
  changes only a path of the cut's state, `cutS_setPath`).
* `topB N S`: the highest ballot whose leader ordered something; `L0 N S` its leader sequence.
* `linOrd N Ns S h P`: `L0` of the cut's state, stably sorted by `tau` with `tau` taken from the
  **present** history `h` (a command not invoked in `h`: after every present event), so that it
  does not depend on the cut's interleaving.
* `StratOk N fr Ns S h P G`: `PInv`, `HistOk`, invoked ⇒ registered, the committed prefix `G` a
  prefix of `linOrd` whose every element has all its conflict-chain predecessors invoked in `h`
  (`tau < h.length`), and every accepted command of `h` in `G` with its result.
* Steps: `StratOk.init`, `StratOk.rep` (a replica's real event, the head of its predictions),
  `StratOk.inv` (a client's invocation), `StratOk.resp` (a client's acceptance, possibly chosen
  with leader result `v`: commits `D`, `linOrd`'s commands up to `x`, every one invoked in `h`).
  The witness facts come from `top_witness_at` on the cut's state and the present history with
  the cut's invocations (`cut_hist`); W3 (the committed prefix stays a prefix when `tau`
  changes) is `sortW_prefix_stable`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.LinWitness
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Trace

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

open Classical
open scoped List

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## The sort with only distinct ids (LinWitness.lean's lemmas, `Witness` weakened to its
`nodup`) -/

section keepNd
variable {H : Hist} {L0 : Seq}

theorem sortW_nodup_nd (hW : (L0.map Prod.fst).Nodup) : ((sortW H L0).map Prod.fst).Nodup :=
  (List.Perm.map Prod.fst (sortW_perm H L0)).nodup_iff.mpr hW

theorem sortW_keep_nd (hW : (L0.map Prod.fst).Nodup) {a b : CmdId × Cmd} (ha : a ∈ L0) (hb : b ∈ L0)
    (hc : Cmd.conflict a.2 b.2 = true) :
    precedes (L0.map Prod.fst) a.1 b.1 ↔ precedes ((sortW H L0).map Prod.fst) a.1 b.1 := by
  have fwd : ∀ a b, a ∈ L0 → b ∈ L0 → Cmd.conflict a.2 b.2 = true →
      precedes (L0.map Prod.fst) a.1 b.1 → precedes ((sortW H L0).map Prod.fst) a.1 b.1 := by
    intro a b ha hb hc hp
    exact precedes_of_sublist_pair _ (sortW_nodup_nd (H := H) hW) a b
      (sortW_pair H L0 ⟨sublist_pair_of_precedes L0 hW a b ha hb hp, hc⟩)
  have hcs : Cmd.conflict b.2 a.2 = true := by
    unfold Cmd.conflict at hc ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc ⊢
    exact ⟨hc.1.symm, hc.2.symm⟩
  refine ⟨fwd a b ha hb hc, fun h => ?_⟩
  have hab : a.1 ≠ b.1 := fun e => by rw [e] at h; exact precedes_irrefl _ _ h
  rcases precedes_total (L0.map Prod.fst) a.1 b.1 (List.mem_map_of_mem ha)
    (List.mem_map_of_mem hb) hab with h' | h'
  · exact h'
  · exact (precedes_antisymm _ _ _ h (fwd b a hb ha hcs h')).elim

theorem seqOf_stOf_nd (hW : (L0.map Prod.fst).Nodup) {s : Seq} (hs : s ~ L0) :
    (stOf L0).seqOf (s.map Prod.fst) = s := by
  unfold PState.seqOf
  have hnd : (s.map Prod.fst).Nodup := (List.Perm.map Prod.fst hs).nodup_iff.mpr hW
  exact filterMap_ids _ s hnd (fun p hp => cmdIn_of_mem L0 hW p (hs.mem_iff.mp hp))

theorem stOf_cmds_nd (hW : (L0.map Prod.fst).Nodup) {p : CmdId × Cmd} (hp : p ∈ L0) :
    (stOf L0).cmds p.1 = some p.2 := cmdIn_of_mem L0 hW p hp

theorem sortW_result_nd (hW : (L0.map Prod.fst).Nodup) {x : CmdId} (hx : x ∈ L0.map Prod.fst) :
    resultIn (sortW H L0) x = resultIn L0 x := by
  obtain ⟨cx, hcx⟩ := pair_of_id hx
  let S := stOf L0
  have hS : S.cmds x = some cx := stOf_cmds_nd hW hcx
  have hreg : ∀ (s : Seq), s ~ L0 → ∀ y ∈ s.map Prod.fst, S.cmds y ≠ none := by
    intro s hs y hy
    obtain ⟨c, hc⟩ := pair_of_id hy
    rw [show y = (y, c).1 from rfl, stOf_cmds_nd hW (hs.mem_iff.mp hc)]; simp
  have hndW := sortW_nodup_nd (H := H) hW
  have hxW : x ∈ (sortW H L0).map Prod.fst := ids_sortW.mpr hx
  have e1 : resultIn (sortW H L0) x = resultIn (S.seqOf ((sortW H L0).map Prod.fst)) x := by
    rw [seqOf_stOf_nd hW (sortW_perm H L0)]
  have e2 : resultIn L0 x = resultIn (S.seqOf (L0.map Prod.fst)) x := by
    rw [seqOf_stOf_nd hW (List.Perm.refl L0)]
  rw [e1, e2]
  by_cases hg : cx.isGet = true
  · obtain ⟨p, hp⟩ := Ctx.lastPut_exists (S := S) (L0.map Prod.fst) hW x cx.key
    rw [PState.resultIn_lastPut S _ hW (hreg L0 (List.Perm.refl _)) x cx hx hS p hp,
      PState.resultIn_lastPut S _ hndW (hreg _ (sortW_perm H L0)) x cx hxW hS p ?_]
    -- a put of `x`'s key and `x` (a get) conflict; two puts of a key conflict
    have hput : ∀ y, S.isPutOf cx.key y → ∃ c, (y, c) ∈ L0 ∧ Cmd.conflict c cx = true := by
      intro y ⟨cy, hcy, hk, hp⟩
      have hy : y ∈ L0.map Prod.fst := by
        unfold S stOf at hcy; exact mem_ids_of_cmdIn hcy
      obtain ⟨c, hc⟩ := pair_of_id hy
      have := stOf_cmds_nd hW hc; rw [this] at hcy; cases hcy
      simp only at hk hp
      exact ⟨c, hc, by simp [Cmd.conflict, hk, hp]⟩
    have hpp : ∀ y z, S.isPutOf cx.key y → S.isPutOf cx.key z →
        ∃ cy cz, (y, cy) ∈ L0 ∧ (z, cz) ∈ L0 ∧ Cmd.conflict cy cz = true := by
      intro y z hy hz
      obtain ⟨cy, hcy, -⟩ := hput y hy
      obtain ⟨cz, hcz, -⟩ := hput z hz
      obtain ⟨cy', hcy', hky, hpy⟩ := hy
      obtain ⟨cz', hcz', hkz, hpz⟩ := hz
      rw [show y = (y, cy).1 from rfl, stOf_cmds_nd hW hcy] at hcy'
      rw [show z = (z, cz).1 from rfl, stOf_cmds_nd hW hcz] at hcz'
      cases hcy'; cases hcz'
      simp only at hky hkz hpy
      exact ⟨cy, cz, hcy, hcz, by simp [Cmd.conflict, hky, hkz, hpy]⟩
    -- transfer `LastPut` from `L0`'s order to the sort's
    have tr : ∀ y, S.isPutOf cx.key y → (precedes (L0.map Prod.fst) y x ↔
        precedes ((sortW H L0).map Prod.fst) y x) := by
      intro y hy
      obtain ⟨c, hc, hcf⟩ := hput y hy
      exact sortW_keep_nd hW (a := (y, c)) (b := (x, cx)) hc hcx hcf
    cases p with
    | none =>
      intro y hy hput'
      exact hp y ((tr y hput').mpr hy) hput'
    | some p =>
      obtain ⟨hpx, hpP, hmax⟩ := hp
      refine ⟨(tr p hpP).mp hpx, hpP, fun y hy hyP => ?_⟩
      rcases hmax y ((tr y hyP).mpr hy) hyP with h | h
      · exact Or.inl h
      · obtain ⟨cy, cp, hcy, hcp, hc⟩ := hpp y p hyP hpP
        exact Or.inr ((sortW_keep_nd hW (a := (y, cy)) (b := (p, cp)) hcy hcp hc).mp h)
  · have hg' : cx.isGet = false := by simpa using hg
    rw [Ctx.resultIn_nonget (S := S) _ (hreg _ (sortW_perm H L0)) x cx hxW hS hg',
      Ctx.resultIn_nonget (S := S) _ (hreg L0 (List.Perm.refl _)) x cx hx hS hg']



end keepNd

/-! ## Stable sorts are unique; the prefix below a key bound is stable -/

section stable
variable {α : Type} [DecidableEq α]

theorem sublist_tail_of_ne {x a : α} {m l : List α} (h : (x :: m) <+ (a :: l)) (hne : x ≠ a) :
    (x :: m) <+ l := by
  cases h with
  | cons _ h => exact h
  | cons_cons _ h => exact absurd rfl hne

theorem pair_order : ∀ {L : List α} {a b : α}, a ∈ L → b ∈ L → a ≠ b → [a, b] <+ L ∨ [b, a] <+ L
  | [], _, _, ha, _, _ => by simp at ha
  | c :: L, a, b, ha, hb, hab => by
    by_cases hca : c = a
    · subst hca
      have hb' : b ∈ L := by simp at hb; rcases hb with h | h; exact absurd h.symm hab; exact h
      exact .inl (.cons_cons _ (List.singleton_sublist.mpr hb'))
    · by_cases hcb : c = b
      · subst hcb
        have ha' : a ∈ L := by simp at ha; rcases ha with h | h; exact absurd h.symm hca; exact h
        exact .inr (.cons_cons _ (List.singleton_sublist.mpr ha'))
      · have ha' : a ∈ L := by simp at ha; rcases ha with h | h; exact absurd h.symm hca; exact h
        have hb' : b ∈ L := by simp at hb; rcases hb with h | h; exact absurd h.symm hcb; exact h
        rcases pair_order ha' hb' hab with h | h
        · exact .inl (.cons _ h)
        · exact .inr (.cons _ h)

/-- A stable sort of `L` by `k`. -/
structure StableSort (k : α → Nat) (L T : List α) : Prop where
  perm : T.Perm L
  sorted : T.Pairwise (fun a b => k a ≤ k b)
  stable : ∀ a b, k a = k b → [a, b] <+ L → [a, b] <+ T

/-- **A stable sort of a list without duplicates is unique.** -/
theorem StableSort.unique (k : α → Nat) : ∀ (T1 : List α) {L T2 : List α}, L.Nodup →
    StableSort k L T1 → StableSort k L T2 → T1 = T2
  | [], L, T2, _, h1, h2 => by
    have := h2.perm.trans h1.perm.symm
    exact (List.Perm.eq_nil this).symm
  | a :: T1, L, T2, hnd, h1, h2 => by
    have hnd1 : (a :: T1).Nodup := h1.perm.nodup_iff.mpr hnd
    cases T2 with
    | nil => exact absurd (h1.perm.trans h2.perm.symm).length_eq (by simp)
    | cons b T2 =>
      have hnd2 : (b :: T2).Nodup := h2.perm.nodup_iff.mpr hnd
      by_cases hab : a = b
      · subst hab
        have haL : a ∈ L := h1.perm.mem_iff.mp (by simp)
        have hp1 : T1.Perm (L.erase a) := by
          have := (List.perm_cons_erase haL)
          exact (List.perm_cons a).mp (h1.perm.trans this)
        have hp2 : T2.Perm (L.erase a) := by
          have := (List.perm_cons_erase haL)
          exact (List.perm_cons a).mp (h2.perm.trans this)
        have st : ∀ (T : List α), (a :: T).Nodup → StableSort k L (a :: T) →
            ∀ x y, k x = k y → [x, y] <+ L.erase a → [x, y] <+ T := by
          intro T hT hs x y hk hxy
          have hx : x ∈ L.erase a := hxy.subset (by simp)
          have hxa : x ≠ a := ((List.Nodup.mem_erase_iff hnd).mp hx).1
          exact sublist_tail_of_ne (hs.stable x y hk (hxy.trans List.erase_sublist)) hxa
        rw [StableSort.unique k T1 (hnd.erase a)
          ⟨hp1, (List.pairwise_cons.mp h1.sorted).2, st T1 hnd1 h1⟩
          ⟨hp2, (List.pairwise_cons.mp h2.sorted).2, st T2 hnd2 h2⟩]
      · exfalso
        have hbT1 : b ∈ T1 := by
          have : b ∈ a :: T1 := (h1.perm.trans h2.perm.symm).mem_iff.mpr (by simp)
          simp at this; rcases this with h | h; exact absurd h.symm hab; exact h
        have haT2 : a ∈ T2 := by
          have : a ∈ b :: T2 := (h2.perm.trans h1.perm.symm).mem_iff.mpr (by simp)
          simp at this; rcases this with h | h; exact absurd h hab; exact h
        have k1 := (List.pairwise_cons.mp h1.sorted).1 b hbT1
        have k2 := (List.pairwise_cons.mp h2.sorted).1 a haT2
        have hk : k a = k b := by omega
        rcases pair_order (h1.perm.mem_iff.mp (List.mem_cons_self ..))
            (h2.perm.mem_iff.mp (List.mem_cons_self ..)) hab with h | h
        · have := sublist_tail_of_ne (h2.stable a b hk h) hab
          exact (List.nodup_cons.mp hnd2).1 (this.subset (by simp))
        · have := sublist_tail_of_ne (h1.stable b a hk.symm h) (Ne.symm hab)
          exact (List.nodup_cons.mp hnd1).1 (this.subset (by simp))

theorem stableSort_mergeSort (k : α → Nat) (L : List α) :
    StableSort k L (L.mergeSort (fun a b => decide (k a ≤ k b))) :=
  ⟨List.mergeSort_perm _ _,
    (List.pairwise_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
      (fun a b => by simp; omega) L).imp (fun h => by simpa using h),
    fun a b hk h => List.pair_sublist_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
      (fun a b => by simp; omega) (by simp [hk]) h⟩

/-- In a list sorted along a relation for which `p` is downward closed, the `p` elements come
first. -/
theorem filter_split (p : α → Bool) (R : α → α → Prop) :
    ∀ (T : List α), T.Pairwise R → (∀ a ∈ T, ∀ b ∈ T, R a b → p b = true → p a = true) →
    T = T.filter p ++ T.filter (fun a => !p a)
  | [], _, _ => rfl
  | a :: T, hT, hd => by
    have ih := filter_split p R T (List.pairwise_cons.mp hT).2
      (fun x hx y hy => hd x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, ite_true, Bool.not_true, Bool.false_eq_true, ite_false,
        List.cons_append]
      rw [← ih]
    · have hall : ∀ b ∈ T, p b = false := by
        intro b hb
        cases e : p b
        · rfl
        · exact absurd (hd a (by simp) b (List.mem_cons_of_mem _ hb)
            ((List.pairwise_cons.mp hT).1 b hb) e) hp
      have h1 : T.filter p = [] := List.filter_eq_nil_iff.mpr (fun b hb => by simp [hall b hb])
      have h2 : T.filter (fun a => !p a) = T := List.filter_eq_self.mpr (fun b hb => by simp [hall b hb])
      simp only [List.filter_cons, hp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false, h1, h2]
      simp

theorem prefix_of_append_filter {p : α → Bool} : ∀ {A B G : List α}, G <+: A ++ B →
    (∀ g ∈ G, p g = true) → (∀ b ∈ B, p b = false) → G <+: A
  | [], B, G, hG, hp, hB => by
    cases G with
    | nil => exact List.nil_prefix
    | cons g G =>
      have : g ∈ B := hG.subset (by simp)
      have := hB g this; rw [hp g (by simp)] at this; cases this
  | a :: A, B, G, hG, hp, hB => by
    cases G with
    | nil => exact List.nil_prefix
    | cons g G =>
      obtain ⟨t, ht⟩ := hG
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      have := prefix_of_append_filter (A := A) (B := B) (G := G) ⟨t, ht⟩
        (fun x hx => hp x (by simp [hx])) hB
      exact List.cons_prefix_cons.mpr ⟨rfl, this⟩

/-- **W3, the sort's part**: changing the keys only at or above `n` (keys below `n` kept, keys at
or above `n` staying there) keeps any prefix of the sort whose keys are below `n`. -/
theorem sort_prefix_stable (k k' : α → Nat) (n : Nat) {L G : List α} (hnd : L.Nodup)
    (h1 : ∀ a ∈ L, k a < n → k' a = k a) (h2 : ∀ a ∈ L, n ≤ k a → n ≤ k' a)
    (hG : G <+: L.mergeSort (fun a b => decide (k a ≤ k b))) (hGn : ∀ g ∈ G, k g < n) :
    G <+: L.mergeSort (fun a b => decide (k' a ≤ k' b)) := by
  let p : α → Bool := fun a => decide (k a < n)
  have sT := stableSort_mergeSort k L
  have sT' := stableSort_mergeSort k' L
  generalize L.mergeSort (fun a b => decide (k a ≤ k b)) = T at hG sT
  generalize L.mergeSort (fun a b => decide (k' a ≤ k' b)) = T' at sT' ⊢
  have hndf : (L.filter p).Nodup := hnd.sublist List.filter_sublist
  have memL : ∀ {a}, a ∈ L.filter p → a ∈ L ∧ k a < n := fun h => by
    have := List.mem_filter.mp h; exact ⟨this.1, by simpa [p] using this.2⟩
  -- both filtered sorts are the stable sort of `L.filter p` by `k`
  have e : T.filter p = T'.filter p := by
    apply StableSort.unique k _ hndf
    · refine ⟨sT.perm.filter p, sT.sorted.filter p, fun a b hk h => ?_⟩
      have := (sT.stable a b hk (h.trans List.filter_sublist)).filter p
      have ha := memL (a := a) (h.subset (by simp)); have hb := memL (a := b) (h.subset (by simp))
      simpa [p, ha.2, hb.2] using this
    · refine ⟨sT'.perm.filter p, ?_, fun a b hk h => ?_⟩
      · refine (sT'.sorted.filter p).imp_of_mem (fun {a b} ha hb hab => ?_)
        have ha' := List.mem_filter.mp ha; have hb' := List.mem_filter.mp hb
        have haL := sT'.perm.mem_iff.mp ha'.1; have hbL := sT'.perm.mem_iff.mp hb'.1
        have ka : k a < n := by simpa [p] using ha'.2
        have kb : k b < n := by simpa [p] using hb'.2
        rw [← h1 _ haL ka, ← h1 _ hbL kb]; exact hab
      · have ha := memL (a := a) (h.subset (by simp)); have hb := memL (a := b) (h.subset (by simp))
        have hk' : k' a = k' b := by rw [h1 a ha.1 ha.2, h1 b hb.1 hb.2]; exact hk
        have := (sT'.stable a b hk' (h.trans List.filter_sublist)).filter p
        simpa [p, ha.2, hb.2] using this
  -- the `p` elements come first in both
  have splitT : T = T.filter p ++ T.filter (fun a => !p a) :=
    filter_split p _ T sT.sorted (fun a _ b _ hab hb => by simp [p] at hb ⊢; omega)
  have splitT' : T' = T'.filter p ++ T'.filter (fun a => !p a) := by
    apply filter_split p _ T' sT'.sorted
    intro a ha b hb hab hpb
    have haL := sT'.perm.mem_iff.mp ha; have hbL := sT'.perm.mem_iff.mp hb
    have hb' : k b < n := by simpa [p] using hpb
    simp only [p, decide_eq_true_eq]
    apply Classical.byContradiction; intro hna
    have := h2 a haL (by omega)
    rw [h1 b hbL hb'] at hab; omega
  have hGA : G <+: T.filter p := by
    rw [splitT] at hG
    exact prefix_of_append_filter (p := p) hG (fun g hg => by simpa [p] using hGn g hg)
      (fun b hb => by have := (List.mem_filter.mp hb).2; simpa using this)
  rw [e] at hGA
  rw [splitT']
  exact hGA.trans (List.prefix_append _ _)

end stable

/-! ## `tau` when the history grows -/

theorem invIdx_append_lt {H u : Hist} {z : CmdId} (h : invIdx H z < H.length) :
    invIdx (H ++ u) z = invIdx H z := by
  unfold invIdx at h ⊢; rw [List.findIdx_append, ite_cond_eq_true _ _ (eq_true h)]

theorem invIdx_append_ge {H u : Hist} {z : CmdId} (h : H.length ≤ invIdx H z) :
    H.length ≤ invIdx (H ++ u) z := by
  unfold invIdx at h ⊢; rw [List.findIdx_append]
  split
  · omega
  · omega

theorem tau_append_lt {H u : Hist} {L0 : Seq} {a : CmdId × Cmd} (h : tau H L0 a < H.length) :
    tau (H ++ u) L0 a = tau H L0 a := by
  unfold tau
  congr 1
  apply List.map_congr_left
  intro z hz
  have hz' := List.mem_filter.mp hz
  exact invIdx_append_lt (Nat.lt_of_le_of_lt (le_tau H L0 hz'.1 (by simpa using hz'.2)) h)

theorem tau_append_ge {H u : Hist} {L0 : Seq} {a : CmdId × Cmd} (ha : a ∈ L0)
    (h : H.length ≤ tau H L0 a) : H.length ≤ tau (H ++ u) L0 a := by
  obtain ⟨z, hz, hcp, he⟩ := tau_mem H L0 ha
  rw [he] at h
  exact Nat.le_trans (invIdx_append_ge h) (le_tau (H ++ u) L0 hz hcp)

/-- **W3**: a prefix of the sort all of whose elements have their conflict-chain predecessors
invoked in `H` stays a prefix when the history grows. -/
theorem sortW_prefix_stable {H u : Hist} {L0 G : Seq} (hnd : (L0.map Prod.fst).Nodup)
    (hG : G <+: sortW H L0) (hGn : ∀ g ∈ G, tau H L0 g < H.length) :
    G <+: sortW (H ++ u) L0 :=
  sort_prefix_stable (tau H L0) (tau (H ++ u) L0) H.length (List.Pairwise.of_map Prod.fst (fun a b h e => h (congrArg _ e)) hnd)
    (fun _ _ h => tau_append_lt h) (fun _ ha h => tau_append_ge ha h) hG hGn

theorem invoked_of_invIdx {H : Hist} {z : CmdId} (h : invIdx H z < H.length) :
    ∃ c, H[invIdx H z]? = some (Ev.inv z c) := by
  have hp := List.findIdx_getElem (p := fun e => decide (∃ c, e = Ev.inv z c)) (w := h)
  simp only [decide_eq_true_eq] at hp
  obtain ⟨c, hc⟩ := hp
  exact ⟨c, by unfold invIdx at h ⊢; rw [List.getElem?_eq_getElem h]; exact congrArg some hc⟩

/-! ## The cut, its top ballot, the linearization order -/

/-- The nodes' predictions. -/
abbrev Preds := Nd → List PEv

/-- The maximal valid cut's final configuration (the cut's normal form). -/
def cutC (N : Nat) (Ns : List Nd) (S : PState) (P : Preds) : Cut.Conf Nd PState PEv :=
  Cut.nfOf Ns (okE N) (apE N) (S, P)

/-- The maximal valid cut's final state `S⁺`. -/
def cutS (N : Nat) (Ns : List Nd) (S : PState) (P : Preds) : PState := (cutC N Ns S P).1

/-- The highest ballot any replica reached (a bound of the ordered ballots). -/
def maxBal (N : Nat) (S : PState) : Nat := ((List.range N).map (fun r => (S.rs r).ballot)).foldr max 0

/-- The top ballot: the highest whose leader ordered something (0 if none). -/
def topB (N : Nat) (S : PState) : Nat :=
  ((List.range (maxBal N S + 1)).filter (fun b => decide (S.ord N b ≠ []))).foldr max 0

/-- The top ballot's leader sequence. -/
def L0 (N : Nat) (S : PState) : Seq := S.ordSeq N (topB N S)

/-- **The linearization order** of the present `(S, h)` and the predictions `P`: the cut's
top order, stably sorted by `tau` taken from the present history. -/
def linOrd (N : Nat) (Ns : List Nd) (S : PState) (h : SHist) (P : Preds) : Seq :=
  sortW (SHist.hist h) (L0 N (cutS N Ns S P))

section top
variable {S : PState} {N : Nat} {fr : Bool}

theorem topB_ge (hI : S.PInv N fr) {b : Nat} (h : S.ord N b ≠ []) : b ≤ topB N S := by
  have hl := (hI.loc_ok (leaderOf N b) b).2.2 h
  have hm : b ≤ maxBal N S :=
    Nat.le_trans hl.2.1 (le_foldr_max _ _ (List.mem_map.mpr ⟨_, List.mem_range.mpr hl.1, rfl⟩))
  exact le_foldr_max _ _ (List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simpa using h⟩)

theorem topB_ord (h : 0 < topB N S) : ∃ y, y ∈ S.ord N (topB N S) := by
  unfold topB at h ⊢
  generalize hl : (List.range (maxBal N S + 1)).filter (fun b => decide (S.ord N b ≠ [])) = l
    at h ⊢
  by_cases e : l = []
  · subst e; simp at h
  · have hall : ∀ z ∈ l, S.ord N z ≠ [] := by
      intro z hz; rw [← hl] at hz; simpa using (List.mem_filter.mp hz).2
    exact List.exists_mem_of_ne_nil _ (hall _ (foldr_max_mem l e))

end top

section cut
variable {N : Nat} {fr : Bool} {Ns : List Nd}

theorem cutC_spec (S : PState) (P : Preds) :
    Cut.NF Ns (okE N) (apE N) (S, P) (cutC N Ns S P) := Cut.nfOf_spec _

/-- A predicted event that is its node's next and ok now keeps the cut. -/
theorem cutC_step {S : PState} {P : Preds} (hI : S.PInv N fr) {n : Nd} {e : PEv}
    {rest : List PEv} (hn : n ∈ Ns) (hP : P n = e :: rest) (hok : okE N S n e) :
    cutC N Ns (apE N S n e) (Cut.upd P n rest) = cutC N Ns S P :=
  Cut.nfOf_step (diamond N fr) (c := (S, P)) hI (Cut.step_of_head hn hP hok)

/-- A real pre-acceptance's path changes only that path of the cut's state. -/
theorem cutS_setPath {S : PState} {P : Preds} (hI : (S.setPath r b y Q).PInv N fr)
    (hJ : S.PInv N fr) (hp : S.path r b y ≠ none) :
    cutS N Ns (S.setPath r b y Q) P = (cutS N Ns S P).setPath r b y Q := by
  unfold cutS cutC
  have := Cut.nfOf_map (Ns := Ns) (diamond N fr) (fun s => s.setPath r b y Q)
    (fun s => s.PInv N fr ∧ s.path r b y ≠ none)
    (fun s n e hs hok => ⟨apE_pinv hs.1 hok, fun h0 => hs.2 (by
      cases e' : s.path r b y with
      | none => rfl
      | some P0 => rw [(apE_le hs.1 hok).path _ _ _ _ e'] at h0; cases h0)⟩)
    (fun s n e hs => setPath_okE hs.2 n e) (fun s n e hs hok => setPath_apE hs.2 hok)
    (c := (S, P)) ⟨hJ, hp⟩ hI
  rw [this]

theorem L0_setPath (X : PState) (r b : Nat) (y : CmdId) (Q : List CmdId) :
    L0 N (X.setPath r b y Q) = L0 N X := rfl

/-- **The present with the cut's invocations satisfies `HistOk` at the cut's state.** -/
theorem run_hist {c d : Cut.Conf Nd PState PEv} (hr : Cut.Star Ns (okE N) (apE N) c d) :
    ∀ (hh : SHist), c.1.PInv N fr → HistOk N fr hh c.1 →
    (∀ x cm, Ev.inv x cm ∈ SHist.hist hh → c.1.cmds x = some cm) →
    ∃ u : SHist, (∀ q ∈ u, ∃ x cm, q.1 = Ev.inv x cm) ∧ HistOk N fr (hh ++ u) d.1 ∧
      d.1.PInv N fr ∧ c.1.le d.1 := by
  induction hr with
  | refl c => exact fun hh hI hH _ => ⟨[], by simp, by simpa using hH, hI, PState.le_refl _⟩
  | @head c c' d st _ ih =>
    intro hh hI hH hreg
    obtain ⟨n, hn, e, rest, he, hok, rfl⟩ := st
    have hI' := apE_pinv (fr := fr) hI hok
    have hle := apE_le (fr := fr) hI hok
    cases n with
    | rep r =>
      have hc := apE_cmds_rep hok
      obtain ⟨u, hu, hH', hId, hle'⟩ := ih hh hI' (HistOk_mono hH hle hc)
        (fun x cm h => by rw [hc]; exact hreg x cm h)
      exact ⟨u, hu, hH', hId, PState.le_trans hle hle'⟩
    | cl k =>
      cases e with
      | inv x cm =>
        obtain ⟨hx, -, hpg⟩ := hok
        have hnew : ∀ c' S', (Ev.inv x c', S') ∉ hh := by
          intro c' S' hm
          have := hreg x c' (SHist.mem_hist.mpr ⟨S', hm⟩); rw [hx] at this; cases this
        have hH1 : HistOk N fr (hh ++ [(Ev.inv x cm, c.1)]) (c.1.register x cm) :=
          HistOk_register (HistOk_inv hH hx hnew hpg) hx
            (by unfold SHist.hist; simp)
        have hreg1 : ∀ y cy, Ev.inv y cy ∈ SHist.hist (hh ++ [(Ev.inv x cm, c.1)]) →
            (c.1.register x cm).cmds y = some cy := by
          intro y cy hy
          unfold SHist.hist at hy; simp only [List.map_append, List.map_cons, List.map_nil,
            List.mem_append, List.mem_singleton, Ev.inv.injEq] at hy
          rcases hy with hy | ⟨rfl, rfl⟩
          · have := hreg y cy (by unfold SHist.hist; exact hy)
            have hyx : y ≠ x := by rintro rfl; rw [hx] at this; cases this
            simp [PState.register, hyx, this]
          · simp [PState.register]
        obtain ⟨u, hu, hH', hId, hle'⟩ := ih _ hI' hH1 hreg1
        refine ⟨[(Ev.inv x cm, c.1)] ++ u, fun q hq => ?_, by simpa using hH', hId,
          PState.le_trans hle hle'⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨x, cm, rfl⟩
        · exact hu q hq
      | resp x v =>
        obtain ⟨u, hu, hH', hId, hle'⟩ := ih hh hI' hH hreg
        exact ⟨u, hu, hH', hId, PState.le_trans hle hle'⟩
      | _ => exact hok.elim

/-- **The witness of the present and the cut** (`top_witness_at` on the cut's state, at its top
ballot, with the present history and the cut's invocations). -/
theorem cut_witness {S : PState} {h : SHist} (P : Preds) (hI : S.PInv N fr)
    (hH : HistOk N fr h S) (hreg : ∀ x cm, Ev.inv x cm ∈ SHist.hist h → S.cmds x = some cm) :
    ∃ u : SHist, (∀ q ∈ u, ∃ x cm, q.1 = Ev.inv x cm) ∧
      Witness (SHist.hist (h ++ u)) (L0 N (cutS N Ns S P)) ∧ S.le (cutS N Ns S P) ∧
      (cutS N Ns S P).PInv N fr := by
  obtain ⟨u, hu, hH', hI', hle⟩ := run_hist (cutC_spec (N := N) (Ns := Ns) S P).1 h hI hH hreg
  refine ⟨u, hu, top_witness_at hI' hH' _ (fun x v S' hm => ?_) topB_ord, hle, hI'⟩
  obtain ⟨hIS', b, hpc, hv⟩ := hH'.resp x v S' hm
  refine ⟨b, topB_ge hI' (fun e => ?_), hpc, hv⟩
  have := ord_le (hH'.le_now _ hm) hpc.1
  rw [e] at this; cases this

end cut

/-! ## Facts from the witness -/

section wit
variable {H : Hist} {u : Hist} {L : Seq}

/-- W2: an accepted command's conflict-chain predecessors were invoked before its acceptance;
so its `tau` (from the present history) is below the acceptance's index. -/
theorem tau_accepted (hW : Witness (H ++ u) L) {i : Nat} {x : CmdId × Cmd} {v : List w8}
    (hx : x ∈ L) (hi : H[i]? = some (Ev.resp x.1 v)) : tau H L x < i := by
  have hil : i < H.length := by
    rcases Nat.lt_or_ge i H.length with e | e
    · exact e
    · rw [List.getElem?_eq_none e] at hi; cases hi
  obtain ⟨z, hz, hcp, he⟩ := tau_mem H L hx
  obtain ⟨j, c, hj, hjz⟩ := hW.rt i x v hx (by rw [List.getElem?_append_left hil]; exact hi) z hz hcp
  rw [List.getElem?_append_left (by omega)] at hjz
  rw [he]; exact Nat.lt_of_le_of_lt (invIdx_le H hjz) hj

end wit

/-- A command of the cut's order with `tau` below `m` (at most the present history's length) was
invoked in the present, with its command. -/
theorem invoked_of_tau {N : Nat} {S Sp : PState} {h : SHist} {w : Hist} {p : CmdId × Cmd} {m : Nat}
    (hreg : ∀ x cm, Ev.inv x cm ∈ SHist.hist h → S.cmds x = some cm) (hle : S.le Sp)
    (hp : p ∈ L0 N Sp) (ht : tau (SHist.hist h ++ w) (L0 N Sp) p < m)
    (hm : m ≤ h.length) : Ev.inv p.1 p.2 ∈ SHist.hist h := by
  have hi := Nat.lt_of_le_of_lt (le_tau _ _ hp (CP.refl' _ p)) ht
  have hlen : (SHist.hist h).length = h.length := by simp [SHist.hist]
  have hi' : invIdx (SHist.hist h ++ w) p.1 < (SHist.hist h ++ w).length := by
    simp only [List.length_append]; omega
  obtain ⟨c, hc⟩ := invoked_of_invIdx hi'
  rw [List.getElem?_append_left (by omega)] at hc
  have hmem := List.mem_of_getElem? hc
  have h1 := hle.cmds _ _ (hreg _ _ hmem)
  have h2 := (Ctx.mem_seqOf (S := Sp) (y := p.1) (c := p.2) hp).1
  rw [h1] at h2; cases h2; exact hmem

/-! ## The strategy invariant and its steps -/

/-- **The strategy invariant**: the present `(S, h)` with the protocol's invariants, the
committed prefix `G` a prefix of the linearization order whose every element has its
conflict-chain predecessors invoked in `h`, and every accepted command committed with its
result. -/
structure StratOk (N : Nat) (fr : Bool) (Ns : List Nd) (S : PState) (h : SHist) (P : Preds)
    (G : Seq) : Prop where
  pinv : S.PInv N fr
  hist : HistOk N fr h S
  reg : ∀ x cm, Ev.inv x cm ∈ SHist.hist h → S.cmds x = some cm
  pre : G <+: linOrd N Ns S h P
  tauG : ∀ g ∈ G, tau (SHist.hist h) (L0 N (cutS N Ns S P)) g < h.length
  accepted : ∀ x v, Ev.resp x v ∈ SHist.hist h → x ∈ G.map Prod.fst ∧ resultIn G x = v

/-- What an acceptance commits: invoked commands, new to `G`, distinct, not accepted. -/
structure Commits (h : SHist) (G D : Seq) : Prop where
  invoked : ∀ p ∈ D, Ev.inv p.1 p.2 ∈ SHist.hist h
  fresh : ∀ p ∈ D, p.1 ∉ G.map Prod.fst
  nodup : (D.map Prod.fst).Nodup
  pending : ∀ p ∈ D, ∀ w, Ev.resp p.1 w ∉ SHist.hist h

section strat
variable {N : Nat} {fr : Bool} {Ns : List Nd} {S : PState} {h : SHist} {P : Preds} {G : Seq}

/-- Every committed command was invoked, with its command. -/
theorem StratOk.invG (hS : StratOk N fr Ns S h P G) : ∀ p ∈ G, Ev.inv p.1 p.2 ∈ SHist.hist h := by
  intro p hp
  obtain ⟨u, -, -, hle, -⟩ := cut_witness (Ns := Ns) P hS.pinv hS.hist hS.reg
  have hpL : p ∈ L0 N (cutS N Ns S P) := mem_sortW.mp (hS.pre.subset hp)
  exact invoked_of_tau (w := []) hS.reg hle hpL (by simpa using hS.tauG p hp) (Nat.le_refl _)

/-- **The start**: nothing registered, no history, nothing committed. -/
theorem StratOk.init (hI : S.PInv N fr) (hS : ∀ x, S.cmds x = none) :
    StratOk N fr Ns S [] P [] :=
  ⟨hI, HistOk.nil N fr S hS, by simp [SHist.hist], List.nil_prefix, by simp,
    by simp [SHist.hist]⟩

/-- **A replica's real event** (its next prediction `e`, ok now; a pre-acceptance with its real
path `Q`): the same committed prefix. -/
theorem StratOk.rep (hS : StratOk N fr Ns S h P G) {r : Nat} {e : PEv} {rest : List PEv}
    {Q : List CmdId} (hn : Nd.rep r ∈ Ns) (hP : P (.rep r) = e :: rest)
    (hok : okR N S (.rep r) e Q) :
    StratOk N fr Ns (apR N S (.rep r) e Q) h (Cut.upd P (.rep r) rest) G := by
  have hI := hS.pinv
  have hokE := hok.1
  -- the new state: PInv, an extension, the same commands; the same cut order
  have facts : (apR N S (.rep r) e Q).PInv N fr ∧ S.le (apR N S (.rep r) e Q) ∧
      (apR N S (.rep r) e Q).cmds = S.cmds ∧
      L0 N (cutS N Ns (apR N S (.rep r) e Q) (Cut.upd P (.rep r) rest)) =
        L0 N (cutS N Ns S P) := by
    have hstep := cutC_step (fr := fr) (Ns := Ns) hI hn hP hokE
    cases e with
    | preaccept b y D =>
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10⟩ := hok
      have hIr : (S.preaccept r b y D Q).PInv N fr :=
        PState.PInv_preaccept hI r b y D Q h1 h2 h3 h4 h5 h8 h9 h10
      refine ⟨hIr, PState.le_preaccept r b y D Q h6 h7, rfl, ?_⟩
      show L0 N (cutS N Ns (S.preaccept r b y D Q) _) = _
      have e1 : S.preaccept r b y D Q = (apE N S (.rep r) (.preaccept b y D)).setPath r b y Q :=
        preaccept_setPath hI h7
      rw [e1] at hIr ⊢
      have hI0 := apE_pinv (fr := fr) hI hokE
      rw [cutS_setPath hIr hI0 (by simp [apE, PState.preaccept]), L0_setPath]
      unfold cutS; rw [hstep]
    | _ =>
      first
      | exact hokE.elim
      | exact ⟨apE_pinv hI hokE, apE_le hI hokE, apE_cmds_rep hokE,
          by unfold cutS; exact congrArg (fun c => L0 N c.1) hstep⟩
  obtain ⟨hI', hle, hc, hL⟩ := facts
  refine ⟨hI', HistOk_mono hS.hist hle hc, fun x cm hx => by rw [hc]; exact hS.reg x cm hx,
    ?_, ?_, hS.accepted⟩
  · unfold linOrd; rw [hL]; exact hS.pre
  · rw [hL]; exact hS.tauG

theorem SHist.hist_snoc (h : SHist) (e : Ev) (S : PState) :
    SHist.hist (h ++ [(e, S)]) = SHist.hist h ++ [e] := by simp [SHist.hist]

/-- **A client's real invocation** (its next prediction, ok now): the same committed prefix. -/
theorem StratOk.inv (hS : StratOk N fr Ns S h P G) {k : Nat} {x : CmdId} {c : Cmd}
    {rest : List PEv} (hn : Nd.cl k ∈ Ns) (hP : P (.cl k) = .inv x c :: rest)
    (hok : okE N S (.cl k) (.inv x c)) :
    StratOk N fr Ns (S.register x c) (h ++ [(Ev.inv x c, S)]) (Cut.upd P (.cl k) rest) G := by
  have hI := hS.pinv
  have hstep := cutC_step (fr := fr) (Ns := Ns) hI hn hP hok
  have hcut : cutS N Ns (S.register x c) (Cut.upd P (.cl k) rest) = cutS N Ns S P := by
    unfold cutS; exact congrArg Prod.fst hstep
  obtain ⟨hx, -, hpg⟩ := hok
  have hnew : ∀ c' S', (Ev.inv x c', S') ∉ h := by
    intro c' S' hm
    have := hS.reg x c' (SHist.mem_hist.mpr ⟨S', hm⟩); rw [hx] at this; cases this
  obtain ⟨u, -, hW, -, -⟩ := cut_witness (Ns := Ns) P hI hS.hist hS.reg
  have hnd := hW.nodup
  refine ⟨PState.PInv_register hI x c hx,
    HistOk_register (HistOk_inv hS.hist hx hnew hpg) hx (by unfold SHist.hist; simp), ?_, ?_, ?_, ?_⟩
  · intro y cy hy
    rw [SHist.hist_snoc] at hy
    simp only [List.mem_append, List.mem_singleton, Ev.inv.injEq] at hy
    rcases hy with hy | ⟨rfl, rfl⟩
    · have := hS.reg y cy hy
      have hyx : y ≠ x := by rintro rfl; rw [hx] at this; cases this
      simp [PState.register, hyx, this]
    · simp [PState.register]
  · unfold linOrd; rw [hcut, SHist.hist_snoc]
    exact sortW_prefix_stable hnd hS.pre (fun g hg => by
      have := hS.tauG g hg; simpa [SHist.hist] using this)
  · intro g hg
    rw [hcut, SHist.hist_snoc]
    have := hS.tauG g hg
    have hl : (SHist.hist h).length = h.length := by simp [SHist.hist]
    rw [tau_append_lt (by omega)]; simp; omega
  · intro y v hy
    rw [SHist.hist_snoc] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · exact hS.accepted y v hy
    · cases hy

/-- **A client's real acceptance** of `x` with `v` (its next prediction; `x` possibly chosen in
some ballot with leader result `v`): the strategy commits `D`, `linOrd`'s commands after `G` up
to `x` (each invoked in `h`, so its update is deposited, new, distinct, not yet accepted), and
`x` is committed with result `v`. -/
theorem StratOk.resp (hS : StratOk N fr Ns S h P G) {k : Nat} {x : CmdId} {v : List w8}
    {rest : List PEv} {b : Nat} (hn : Nd.cl k ∈ Ns) (hP : P (.cl k) = .resp x v :: rest)
    (hpc : S.possiblyChosen N b x) (hv : resultIn (S.ordSeq N b) x = v) :
    ∃ D, StratOk N fr Ns S (h ++ [(Ev.resp x v, S)]) (Cut.upd P (.cl k) rest) (G ++ D) ∧
      Commits h G D ∧ x ∈ (G ++ D).map Prod.fst ∧ resultIn (G ++ D) x = v := by
  have hI := hS.pinv
  have hstep := cutC_step (fr := fr) (Ns := Ns) (e := .resp x v) hI hn hP trivial
  have hcut : cutS N Ns S (Cut.upd P (.cl k) rest) = cutS N Ns S P := by
    unfold cutS; exact congrArg Prod.fst hstep
  set_option linter.unusedVariables false in
  let h' := h ++ [(Ev.resp x v, S)]
  have hH' : HistOk N fr h' S := HistOk_resp hS.hist hI hpc hv
  have hreg' : ∀ y cm, Ev.inv y cm ∈ SHist.hist h' → S.cmds y = some cm := by
    intro y cm hy
    rw [SHist.hist_snoc] at hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · exact hS.reg y cm hy
    · cases hy
  obtain ⟨u, hu, hW, hle, -⟩ := cut_witness (Ns := Ns) P hI hH' hreg'
  generalize hLdef : L0 N (cutS N Ns S P) = L at hW
  have hnd := hW.nodup
  have hlen : (SHist.hist h).length = h.length := by simp [SHist.hist]
  -- the order now: `T`
  have hT : linOrd N Ns S h' (Cut.upd P (.cl k) rest) = sortW (SHist.hist h ++ [Ev.resp x v]) L := by
    unfold linOrd; rw [hcut, hLdef, SHist.hist_snoc]
  generalize hTdef : sortW (SHist.hist h ++ [Ev.resp x v]) L = T at hT
  have hGT : G <+: T := by
    rw [← hTdef]
    have := hS.pre; unfold linOrd at this; rw [hLdef] at this
    exact sortW_prefix_stable hnd this (fun g hg => by
      have := hS.tauG g hg; rw [hLdef] at this; omega)
  have tauG' : ∀ g ∈ G, tau (SHist.hist h ++ [Ev.resp x v]) L g < h.length := by
    intro g hg
    have := hS.tauG g hg; rw [hLdef] at this
    rw [tau_append_lt (by omega)]; exact this
  -- `x` in the order with its result (W1), its `tau` below its acceptance (W2)
  have hmem : Ev.resp x v ∈ SHist.hist (h' ++ u) := by
    unfold SHist.hist; simp [h']
  obtain ⟨hxL, hxv⟩ := hW.resp x v hmem
  obtain ⟨cx, hcx⟩ := pair_of_id hxL
  have hidx : (SHist.hist h ++ [Ev.resp x v])[h.length]? = some (Ev.resp (x, cx).1 v) := by
    rw [List.getElem?_append_right (by omega)]; simp [hlen]
  have hW' : Witness (SHist.hist h ++ [Ev.resp x v] ++ SHist.hist u) L := by
    have : SHist.hist (h' ++ u) = SHist.hist h ++ [Ev.resp x v] ++ SHist.hist u := by
      simp [SHist.hist, h']
    rw [← this]; exact hW
  have tx : tau (SHist.hist h ++ [Ev.resp x v]) L (x, cx) < h.length :=
    tau_accepted hW' hcx hidx
  have hresT : resultIn T x = v := by rw [← hTdef, sortW_result_nd hnd hxL]; exact hxv
  have hTnd : (T.map Prod.fst).Nodup := by rw [← hTdef]; exact sortW_nodup_nd hnd
  have hTsub : ∀ p ∈ T, p ∈ L := fun p hp => by rw [← hTdef] at hp; exact mem_sortW.mp hp
  -- the elements before `x` in `T` have `tau` at most `x`'s
  have hxT : x ∈ T.map Prod.fst := by rw [← hTdef]; exact ids_sortW.mpr hxL
  have hjl : (T.map Prod.fst).idxOf x < T.length := by
    have := List.idxOf_lt_length_of_mem hxT; simpa using this
  have hTj : T[(T.map Prod.fst).idxOf x] = (x, cx) := by
    have h1 : (T.map Prod.fst)[(T.map Prod.fst).idxOf x]'(by simpa using hjl) = x :=
      List.getElem_idxOf _
    simp only [List.getElem_map] at h1
    have hm : T[(T.map Prod.fst).idxOf x] ∈ L := hTsub _ (List.getElem_mem _)
    have := cmdIn_of_mem L hnd _ hm
    rw [h1, cmdIn_of_mem L hnd _ hcx] at this
    cases this
    exact Prod.ext h1 rfl
  have below : ∀ p ∈ T.take ((T.map Prod.fst).idxOf x + 1),
      tau (SHist.hist h ++ [Ev.resp x v]) L p < h.length := by
    intro p hp
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hp
    simp only [List.length_take] at hm
    rw [List.getElem_take]
    rcases Nat.lt_or_ge m ((T.map Prod.fst).idxOf x) with e | e
    · have hs : T.Pairwise (fun a b => decide (tau (SHist.hist h ++ [Ev.resp x v]) L a ≤
          tau (SHist.hist h ++ [Ev.resp x v]) L b) = true) := by
        rw [← hTdef]; exact sortW_pairwise _ _
      have := List.pairwise_iff_getElem.mp hs m _ (by omega) hjl e
      rw [hTj] at this; simp at this; omega
    · have : m = (T.map Prod.fst).idxOf x := by omega
      subst this; rw [hTj]; exact tx
  by_cases hxG : x ∈ G.map Prod.fst
  · -- already committed
    refine ⟨[], ⟨hI, hH', hreg', by rw [hT, List.append_nil]; exact hGT,
      fun g hg => ?_, fun y w hy => ?_⟩, ⟨by simp, by simp, by simp, by simp⟩,
      by simpa using hxG, by rw [List.append_nil, resultIn_of_prefix hGT hxG] at *; exact hresT⟩
    · rw [List.append_nil] at hg; rw [hcut, hLdef, SHist.hist_snoc]
      have := tauG' g hg; simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [SHist.hist_snoc] at hy
      simp only [List.mem_append, List.mem_singleton, Ev.resp.injEq] at hy
      rw [List.append_nil]
      rcases hy with hy | ⟨rfl, rfl⟩
      · exact hS.accepted y w hy
      · exact ⟨hxG, by rw [resultIn_of_prefix hGT hxG] at hresT; exact hresT⟩
  · -- commit up to `x`
    generalize hjdef : (T.map Prod.fst).idxOf x = j at hjl hTj below
    have hGj : G.length ≤ j := by
      apply Classical.byContradiction; intro hc
      have hGeq : G = T.take G.length := List.prefix_iff_eq_take.mp hGT
      have : T[j] ∈ G := by
        rw [hGeq]; exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
      rw [hTj] at this
      exact hxG (List.mem_map_of_mem this)
    have hGG' : G <+: T.take (j + 1) := List.prefix_take_iff.mpr ⟨hGT, by omega⟩
    have hsplit : G ++ (T.take (j + 1)).drop G.length = T.take (j + 1) := by
      have hGeq : G = (T.take (j + 1)).take G.length := List.prefix_iff_eq_take.mp hGG'
      conv => rhs; rw [← List.take_append_drop G.length (T.take (j + 1))]
      rw [← hGeq]
    have hxTake : x ∈ (T.take (j + 1)).map Prod.fst := by
      have : T[j] ∈ T.take (j + 1) :=
        List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
      rw [hTj] at this; exact List.mem_map_of_mem (f := Prod.fst) this
    have hresTake : resultIn (T.take (j + 1)) x = v := by
      rw [← resultIn_of_prefix (List.take_prefix (j + 1) T) hxTake]; exact hresT
    refine ⟨(T.take (j + 1)).drop G.length, ?_, ?_, ?_, ?_⟩
    · rw [hsplit]
      refine ⟨hI, hH', hreg', by rw [hT]; exact List.take_prefix _ _, fun g hg => ?_,
        fun y w hy => ?_⟩
      · rw [hcut, hLdef, SHist.hist_snoc]
        have := below g hg; simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · rw [SHist.hist_snoc] at hy
        simp only [List.mem_append, List.mem_singleton, Ev.resp.injEq] at hy
        rcases hy with hy | ⟨rfl, rfl⟩
        · obtain ⟨h1, h2⟩ := hS.accepted y w hy
          exact ⟨(hGG'.sublist.map Prod.fst).subset h1,
            by rw [resultIn_of_prefix hGG' h1]; exact h2⟩
        · exact ⟨hxTake, hresTake⟩
    · -- the commits
      have hnd' : ((G ++ (T.take (j + 1)).drop G.length).map Prod.fst).Nodup := by
        rw [hsplit]; exact hTnd.sublist ((List.take_sublist _ _).map _)
      rw [List.map_append, List.nodup_append] at hnd'
      have hmemT : ∀ p ∈ (T.take (j + 1)).drop G.length, p ∈ T.take (j + 1) :=
        fun p hp => List.mem_of_mem_drop hp
      refine ⟨fun p hp => ?_, fun p hp hpG => ?_, hnd'.2.1, fun p hp w hw => ?_⟩
      · have hpT := hmemT p hp
        have hpL : p ∈ L := hTsub p ((List.take_sublist _ _).subset hpT)
        rw [← hLdef] at hpL
        exact invoked_of_tau hS.reg hle hpL (by rw [hLdef]; exact below p hpT) (Nat.le_refl _)
      · exact hnd'.2.2 p.1 hpG p.1 (List.mem_map_of_mem hp) rfl
      · have := (hS.accepted p.1 w hw).1
        exact hnd'.2.2 p.1 this p.1 (List.mem_map_of_mem hp) rfl
    · rw [hsplit]; exact hxTake
    · rw [hsplit]; exact hresTake

end strat


end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
