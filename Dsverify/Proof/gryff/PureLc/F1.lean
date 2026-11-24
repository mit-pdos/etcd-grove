/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/F1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: **F1** (`lin_replay`) from the abstract replay (`PureLc/Replay.lean`), L1
(`PureL/L1.lean`) and the facts of `PureLc/Facts.lean` (L3 for the carriers read, producer
uniqueness, the RMW chain step).
-/
module

public import Dsverify.Proof.gryff.PureLc.Facts
public import Dsverify.Proof.gryff.PureL.F2

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## Small lemmas -/

theorem Tag.toP_inj {a b : model.Tag} (h : a.toP = b.toP) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [model.Tag.toP, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold sint.Z at h1 h2 h3
  rw [BitVec.toInt_inj] at h1 h2 h3
  subst h1 h2 h3; rfl

theorem mem_lin {l : List Label} {k : Nat} {o : Op} : o ∈ lin l k ↔
    o ∈ ops l ∧ o.g < k ∧ ∃ t, place l o = some t ∧ tagLe t.toP (front l k) := by
  unfold lin
  rw [List.mem_mergeSort, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, placeLe_iff]

theorem front_zero (l : List Label) : front l 0 = proto.tag0 := by
  have hc : ∀ r, cutSt l 0 r = RState.init r.val := by
    intro r; show stOf r (projR (l.take 0) r) = _; rw [List.take_zero]; rfl
  simp only [front, hc, RState.init, model.tag0, model.Tag.toP]
  unfold sint.Z median3 tagMax
  simp [tagLt, proto.tag0]

theorem front_ge0 {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (k : Nat) :
    tagLe proto.tag0 (front l k) := by
  have := front_mono h (Nat.zero_le k); rwa [front_zero] at this

theorem pl_some {l : List Label} {o : Op} {t : model.Tag} (ht : place l o = some t) :
    pl l o = t.toP := by
  simp [pl, ht]

theorem findSome?_map' {α β γ : Type} (f : α → Option β) (g : β → γ) (L : List α) :
    L.findSome? (fun x => (f x).map g) = (L.findSome? f).map g := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.findSome?_cons]; cases f a <;> simp [ih]

theorem execTag_eq (r : Fin 3) (es : List Ev) (x : w32 × w32) :
    execTag r es x = (execVT r es x).map ValTag.t := by
  unfold execTag execVT; rw [← findSome?_map']; congr 1; funext j
  split <;> (try split) <;> simp_all

theorem rmwPlace_eq (l : List Label) (o : Op) : rmwPlace l o = (rmwRes l o).map ValTag.t := by
  unfold rmwPlace rmwRes; rw [← findSome?_map']; congr 1; funext r; exact execTag_eq ..

theorem place_cas {l : List Label} {o : Op} {a b : w64} (hi : o.inp = .cas a b) :
    place l o = (rmwRes l o).map ValTag.t := by
  unfold place; rw [hi]; exact rmwPlace_eq l o

theorem rank_write {o : Op} {v : w64} (hi : o.inp = .write v) : o.rank = 0 := by
  simp [Op.rank, hi]
theorem rank_cas {o : Op} {a b : w64} (hi : o.inp = .cas a b) : o.rank = 0 := by
  simp [Op.rank, hi]

/-! ## Producers in `lin` -/

section
variable {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {k : Nat}
include h

/-- A produced pair below the frontier is `(0, proto.tag0)` or a producer's in `lin` (L1: producers
created at or after the cut are placed above the frontier). -/
theorem prod_lin {v : w64} {t : model.Tag} (hp : Prod l v t) (hle : tagLe t.toP (front l k)) :
    (t.toP = proto.tag0 ∧ v = 0) ∨ ∃ p ∈ lin l k, p.rank = 0 ∧ pl l p = t.toP ∧ pv l p = v := by
  have key : ∀ o ∈ ops l, o.rank = 0 → place l o = some t → o ∈ lin l k := by
    intro o ho h0 ht
    refine mem_lin.2 ⟨ho, ?_, t, ht, hle⟩
    refine Classical.byContradiction fun hg => ?_
    exact (not_tagLt_iff _ _).2 hle ((l1_cut h ho ht (by omega)).2 h0)
  rcases hp with hp | ⟨o, ho, hi, ht⟩ | ⟨o, ho, a, b, hi, hr⟩
  · exact Or.inl hp
  · exact Or.inr ⟨o, key o ho (rank_write hi) ht, rank_write hi, pl_some ht, by simp [pv, hi]⟩
  · have ht : place l o = some t := by rw [place_cas hi, hr]; rfl
    exact Or.inr ⟨o, key o ho (rank_cas hi) ht, rank_cas hi, pl_some ht, by simp [pv, hi, hr]⟩

theorem lin_ops {o : Op} (ho : o ∈ lin l k) : o ∈ ops l := (mem_lin.1 ho).1

theorem lin_pos {o : Op} (ho : o ∈ lin l k) (h0 : o.rank = 0) : tagLt proto.tag0 (pl l o) := by
  obtain ⟨hops, -, t, ht, -⟩ := mem_lin.1 ho
  rw [pl_some ht]
  exact tagLt_of_le_of_lt (front_ge0 h o.g) ((l1 h hops ht).2 h0)

theorem lin_ge0 {o : Op} (ho : o ∈ lin l k) : tagLe proto.tag0 (pl l o) := by
  obtain ⟨hops, -, t, ht, -⟩ := mem_lin.1 ho
  rw [pl_some ht]
  exact tagLe_trans (front_ge0 h o.g) (l1 h hops ht).1

/-- Under producer uniqueness, `val` at a producer's place is its value. -/
theorem val_eq (U : ∀ p ∈ lin l k, ∀ p' ∈ lin l k, p.rank = 0 → p'.rank = 0 → pl l p = pl l p' →
      p = p') {p : Op} (hp : p ∈ lin l k) (h0 : p.rank = 0) : val l k (pl l p) = pv l p := by
  have hex : ∃ o ∈ lin l k, o.rank = 0 ∧ pl l o = pl l p := ⟨p, hp, h0, rfl⟩
  unfold val; rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  rw [U _ h1 p hp h2 h0 h3]

theorem val_zero : val l k proto.tag0 = 0 := by
  unfold val
  rw [dif_neg]
  rintro ⟨o, ho, h0, he⟩
  exact tagLt_ne (lin_pos h ho h0) he.symm

theorem val_prod (U : ∀ p ∈ lin l k, ∀ p' ∈ lin l k, p.rank = 0 → p'.rank = 0 → pl l p = pl l p' →
      p = p') {v : w64} {t : model.Tag} (hp : Prod l v t) (hle : tagLe t.toP (front l k)) :
    pureLc.IsP (pl l) Op.rank (lin l k) t.toP ∧ val l k t.toP = v := by
  rcases prod_lin h hp hle with ⟨h1, h2⟩ | ⟨p, hp, h0, he, hv⟩
  · exact ⟨Or.inl h1, by rw [h1, h2]; exact val_zero h⟩
  · exact ⟨Or.inr ⟨p, hp, h0, he⟩, by rw [← he, val_eq h U hp h0, hv]⟩

end

/-! ## Writes' places -/

theorem extsAt_append {l1 l2 : List Label} {n : Nat} (hn : n < l1.length) :
    extsAt (l1 ++ l2) n = extsAt l1 n := by
  unfold extsAt outsAt
  rw [List.getElem?_append_left hn, List.take_append_of_le_length (by omega)]

theorem repliesTo_append {l1 l2 : List Label} {n : Nat} {o : Op} (hr : RepliesTo l1 n o) :
    RepliesTo (l1 ++ l2) n o := by
  obtain ⟨h1, h2, x, hx, hk⟩ := hr
  have hn : n < l1.length := by
    cases e : l1[n]? with
    | none => rw [e] at h2; cases h2
    | some _ => exact (List.getElem?_eq_some_iff.1 e).1
  refine ⟨h1, ?_, x, ?_, hk⟩
  · rw [List.getElem?_append_left hn]; exact h2
  · rw [extsAt_append hn]; exact hx

theorem lin_ops_l1 {l1 l2 : List Label} {k : Nat} (hk : k ≤ l1.length) {o : Op}
    (ho : o ∈ lin (l1 ++ l2) k) : o ∈ ops l1 := by
  obtain ⟨hops, hg, -⟩ := mem_lin.1 ho
  have := ops_take (l1 ++ l2) l1.length
  rw [List.take_left' rfl] at this
  rw [← this]; exact List.mem_filter.2 ⟨hops, by simp; omega⟩

theorem ops_l1_sub {l1 l2 : List Label} {o : Op} (ho : o ∈ ops l1) : o ∈ ops (l1 ++ l2) := by
  have := ops_take (l1 ++ l2) l1.length
  rw [List.take_left' rfl] at this
  rw [← this] at ho; exact (List.mem_filter.1 ho).1

/-- **Writes' places are distinct** within `lin` (`WB`): two writes with one place have one client
id (`write_place_cid`), so they are sequential; the earlier is replied to before the later's
creation, so its place is at most the frontier then (`l2_write`), below the later's (L1). -/
theorem write_place_uniq {l1 l2 : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) (l1 ++ l2) c)
    (hwb : WB l1) {k : Nat} (hk : k ≤ l1.length) {o o' : Op} (ho : o ∈ lin (l1 ++ l2) k)
    (ho' : o' ∈ lin (l1 ++ l2) k) {v v' : w64} (hi : o.inp = .write v) (hi' : o'.inp = .write v')
    {t : model.Tag} (ht : place (l1 ++ l2) o = some t) (ht' : place (l1 ++ l2) o' = some t) :
    o = o' := by
  have hcid : o.cid = o'.cid := (write_place_cid h hi ht).symm.trans (write_place_cid h hi' ht')
  have h1 := lin_ops_l1 hk ho
  have h1' := lin_ops_l1 hk ho'
  have key : ∀ {a b : Op} {va vb : w64}, a ∈ ops l1 → b ∈ ops l1 → b ∈ lin (l1 ++ l2) k →
      a.inp = .write va → b.inp = .write vb → place (l1 ++ l2) a = some t →
      place (l1 ++ l2) b = some t → a.cid = b.cid → a.g < b.g → False := by
    intro a b va vb ha hb hbl hia hib hta htb hc hlt
    obtain ⟨-, n, hn, hrep⟩ := hwb.2 a ha b hb hc hlt
    have hl2 := l2_write h (ops_l1_sub ha) hia (repliesTo_append hrep) hta
    have hm := front_mono h (show n + 1 ≤ b.g by omega)
    have hl1 := l1_write h (lin_ops h hbl) hib htb
    exact tagLt_irrefl _ (tagLt_of_lt_of_le hl1 (tagLe_trans hl2 hm))
  rcases Nat.lt_trichotomy o.g o'.g with hlt | heq | hlt
  · exact (key h1 h1' ho' hi hi' ht ht' hcid hlt).elim
  · exact ops_g_inj h1 h1' heq
  · exact (key h1' h1 ho hi' hi ht' ht hcid.symm hlt).elim

/-! ## Producer uniqueness in `lin` -/

theorem lin_uniq {l1 l2 : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) (l1 ++ l2) c)
    (hwb : WB l1) {k : Nat} (hk : k ≤ l1.length) :
    ∀ p ∈ lin (l1 ++ l2) k, ∀ p' ∈ lin (l1 ++ l2) k, p.rank = 0 → p'.rank = 0 →
      pl (l1 ++ l2) p = pl (l1 ++ l2) p' → p = p' := by
  intro p hp p' hp' h0 h0' he
  obtain ⟨hops, -, t, ht, -⟩ := mem_lin.1 hp
  obtain ⟨hops', -, t', ht', -⟩ := mem_lin.1 hp'
  rw [pl_some ht, pl_some ht'] at he
  have he := Tag.toP_inj he; subst he
  -- the RMW case's tag has `rmwc ≠ 0`
  have hcas : ∀ q ∈ ops (l1 ++ l2), ∀ a b, q.inp = .cas a b → place (l1 ++ l2) q = some t →
      t.rmwc ≠ 0 := by
    intro q hq a b hi hq'
    rw [place_cas hi] at hq'
    obtain ⟨vt, hr, rfl⟩ := Option.map_eq_some_iff.1 hq'
    obtain ⟨vt0, -, hge, hlt, htt, -⟩ := prod_exec h hq hi hr
    rw [htt]; intro hz
    have : sint.Z (vt0.t.rmwc + 1) = sint.Z vt0.t.rmwc + 1 := by
      unfold sint.Z at *
      rw [BitVec.toInt_add_of_not_saddOverflow]
      · simp
      · simp [BitVec.saddOverflow]; omega
    simp only at hz
    have h2 : sint.Z (vt0.t.rmwc + 1) = 0 := by rw [hz]; rfl
    omega
  cases hi : p.inp with
  | read => simp [Op.rank, hi] at h0
  | write v =>
    cases hi' : p'.inp with
    | read => simp [Op.rank, hi'] at h0'
    | write v' => exact write_place_uniq h hwb hk hp hp' hi hi' ht ht'
    | cas a b => exact absurd (write_place_rmwc h hops hi ht) (hcas p' hops' a b hi' ht')
  | cas a b =>
    cases hi' : p'.inp with
    | read => simp [Op.rank, hi'] at h0'
    | write v' => exact absurd (write_place_rmwc h hops' hi' ht') (hcas p hops a b hi ht)
    | cas a' b' =>
      rw [place_cas hi] at ht; rw [place_cas hi'] at ht'
      obtain ⟨vt, hr, rfl⟩ := Option.map_eq_some_iff.1 ht
      obtain ⟨vt', hr', he⟩ := Option.map_eq_some_iff.1 ht'
      exact rmw_res_uniq h hops hops' hi hi' hr hr' he.symm

/-! ## F1 -/

theorem lin_nodup (l : List Label) (k : Nat) : (lin l k).Nodup := by
  unfold lin
  apply (List.mergeSort_perm _ _).nodup_iff.2
  apply List.Pairwise.filter
  have : (ops l).Pairwise fun a b => a.g < b.g := by
    unfold ops
    apply List.Pairwise.filterMap
    · intro a b hab x hx y hy
      split at hx
      · split at hy
        · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hx
          obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hy
          exact hab
        · cases hy
      · cases hx
    · exact List.pairwise_lt_range
  exact this.imp fun h e => by subst e; omega

theorem rmwTag_toP {t : model.Tag} (hb : sint.Z t.rmwc < 2 ^ 31 - 1) :
    ({ t with rmwc := t.rmwc + 1 } : model.Tag).toP = rmwTag t.toP := by
  have : sint.Z (t.rmwc + 1) = sint.Z t.rmwc + 1 := by
    unfold sint.Z at *
    rw [BitVec.toInt_add_of_not_saddOverflow]
    · simp
    · have := BitVec.le_toInt t.rmwc
      simp [BitVec.saddOverflow]; omega
  simp only [model.Tag.toP, rmwTag_eq, this]

/-- **F1** over a run with well-behaved clients in `l1`, at a cut within `l1`. -/
theorem lin_replay_run {l1 l2 : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) (l1 ++ l2) c)
    (hwb : WB l1) {k : Nat} (hk : k ≤ l1.length) :
    replayOk (0 : w64) ((lin (l1 ++ l2) k).map fun o => (o.inp, opOut (l1 ++ l2) o))
      (frontVal (l1 ++ l2) k) := by
  generalize hl : l1 ++ l2 = l at h
  have U := lin_uniq (hl ▸ h) hwb hk
  rw [hl] at U
  -- the frontier: a store's pair
  obtain ⟨r, hr⟩ : ∃ r, (cutSt l k r).tag.toP = front l k := by
    unfold front
    rcases median3_mem (cutSt l k 0).tag.toP (cutSt l k 1).tag.toP (cutSt l k 2).tag.toP with
      e | e | e
    · exact ⟨0, e.symm⟩
    · exact ⟨1, e.symm⟩
    · exact ⟨2, e.symm⟩
  have hFv : frontVal l k = val l k (front l k) := by
    have hs : ∀ r', (cutSt l k r').tag.toP = front l k → val l k (front l k) = (cutSt l k r').val :=
      fun r' e => by
        have := (val_prod h U (prod_store h k r') (by rw [e]; exact tagLe_refl _)).2
        rwa [e] at this
    unfold frontVal
    split
    · rename_i e; exact (hs 0 e).symm
    · split
      · rename_i e; exact (hs 1 e).symm
      · -- the median is one of the three
        rename_i e0 e1
        have e2 : (cutSt l k 2).tag.toP = front l k := by
          rcases median3_mem (cutSt l k 0).tag.toP (cutSt l k 1).tag.toP (cutSt l k 2).tag.toP
            with e | e | e
          · exact absurd e.symm e0
          · exact absurd e.symm e1
          · exact e.symm
        exact (hs 2 e2).symm
  rw [hFv]
  have hFP : pureLc.IsP (pl l) Op.rank (lin l k) (front l k) := by
    have := (val_prod h U (prod_store h k r) (by rw [hr]; exact tagLe_refl _)).1
    rwa [hr] at this
  apply pureLc.replay (pl := pl l) (rk := Op.rank)
  refine
    { rank := ?_, sort := ?_, uniq := ?_, ge0 := fun a ha => lin_ge0 h ha,
      pos := fun a ha h0 => lin_pos h ha h0, read := ?_, write := ?_, cas := ?_,
      val0 := val_zero h, front := hFP, le := ?_, ge0F := front_ge0 h k }
  · intro a _
    unfold Op.rank; split
    · right; exact ⟨rfl, by assumption⟩
    · left; refine ⟨rfl, ?_⟩; rename_i hne; intro e; exact hne e
  · unfold lin
    apply (List.pairwise_mergeSort (le := opLe l) (fun a b c => opLe_trans l a b c)
      (opLe_total l) _).imp
    intro a b hab
    rw [opLe_eq] at hab
    simp only [pureL.lexB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
    unfold pureLc.SortRel pl
    rcases hab with h1 | ⟨h1, h2 | ⟨h2, -⟩⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  · apply (lin_nodup l k).imp_of_mem
    intro a b ha hb hne h0 h0' he
    exact absurd (U a ha b hb h0 h0' he) hne
  · intro a ha hi
    obtain ⟨hops, -, t, ht, hle⟩ := mem_lin.1 ha
    have ht' : readPlace l a = some t := by unfold place at ht; rw [hi] at ht; exact ht
    obtain ⟨⟨j, v⟩, hrr, -⟩ := Option.bind_eq_some_iff.1 ht'
    have hp := val_prod h U (prod_read h hops hi hrr ht') hle
    rw [pl_some ht]
    refine ⟨hp.1, ?_⟩
    simp [opOut, hi, hrr, hp.2]
  · intro a ha v hi
    refine ⟨?_, by simp [opOut, hi]⟩
    rw [val_eq h U ha (rank_write hi)]; simp [pv, hi]
  · intro a ha x y hi
    refine ⟨by simp [opOut, hi], ?_⟩
    obtain ⟨hops, -, t, ht, hle⟩ := mem_lin.1 ha
    have ht2 := ht
    rw [place_cas hi] at ht2
    obtain ⟨vt, hrr, rfl⟩ := Option.map_eq_some_iff.1 ht2
    obtain ⟨vt0, hp0, -, hb, htt, hvv⟩ := prod_exec h hops hi hrr
    have hpl : pl l a = rmwTag vt0.t.toP := by rw [pl_some ht, htt, rmwTag_toP hb]
    have hlt : tagLt vt0.t.toP (pl l a) := by rw [hpl]; exact tagLt_rmwTag _
    have hle0 : tagLe vt0.t.toP (front l k) :=
      tagLe_trans (tagLe_of_lt hlt) (by rw [pl_some ht]; exact hle)
    obtain ⟨hP0, hv0⟩ := val_prod h U hp0 hle0
    refine ⟨vt0.t.toP, hP0, hlt, fun z h1 h2 => rmwTag_no_between _ z h1 (hpl ▸ h2), ?_⟩
    rw [val_eq h U ha (rank_cas hi), hv0]
    simp only [pv, hi, hrr, Option.map_some, Option.getD_some, hvv]
  · intro a ha
    obtain ⟨-, -, t, ht, hle⟩ := mem_lin.1 ha
    rw [pl_some ht]; exact hle

end Perennial.gryff.pure
