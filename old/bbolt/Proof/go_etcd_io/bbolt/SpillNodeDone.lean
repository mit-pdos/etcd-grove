/-
`node.spill`'s part step (`Proof/go_etcd_io/bbolt/SpillNodeCore.lean`), its end: the parent's
entries after the part's `put` (`parentWs` one part longer, still sorted), as `partsP` keeps them.

The part's `put` searches the parent's entries for the part's old key `ok` and puts the part's
first key `p.2` there (`spParentWs_step`). The first part replaces the node's own entry (at
`i0`, its key `ok`), or is the first entry of a new parent; a later part (no key: `ok = p.2`)
goes after the parts before it, its key above theirs and below the entries after the node's.
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeStep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem spSortedK (ws : List WEntry) : wsSorted ws ↔ (ws.map WEntry.key).Pairwise go.GoStringLt := by
  unfold wsSorted
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    have hj' : j < ws.length := by simpa using hj
    have hi' : i < ws.length := by simpa using hi
    have := h i j hij hj'
    unfold wKey at this
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj'] at this
    simpa using this
  · intro h i j hij hj
    have hi : i < ws.length := by omega
    unfold wKey
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    have := h i j (by simpa using hi) (by simpa using hj) hij
    rw [List.getElem_map, List.getElem_map] at this; exact this

theorem spWKey_keys (ws : List WEntry) (k : Nat) : wKey ws k = ((ws.map WEntry.key)[k]?).getD [] := by
  unfold wKey; rw [List.getElem?_map]

theorem spPairwise_ins {α : Type} {R : α → α → Prop} (L1 L2 : List α) (x : α)
    (h : (L1 ++ L2).Pairwise R) (h1 : ∀ a ∈ L1, R a x) (h2 : ∀ b ∈ L2, R x b) :
    (L1 ++ x :: L2).Pairwise R := by
  rw [List.pairwise_append] at h ⊢
  obtain ⟨p1, p2, p12⟩ := h
  refine ⟨p1, List.pairwise_cons.2 ⟨h2, p2⟩, fun a ha b hb => ?_⟩
  rcases List.mem_cons.1 hb with rfl | hb
  · exact h1 a ha
  · exact p12 a ha b hb

theorem spSearch_unique (ws : List WEntry) (ok : List w8) (a b : Nat)
    (ha : a ≤ ws.length ∧ (∀ k < a, go.GoStringLt (wKey ws k) ok) ∧
      (a < ws.length → ¬ go.GoStringLt (wKey ws a) ok))
    (hb : b ≤ ws.length ∧ (∀ k < b, go.GoStringLt (wKey ws k) ok) ∧
      (b < ws.length → ¬ go.GoStringLt (wKey ws b) ok)) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd (hb.2.1 a h) (ha.2.2 (by omega))
  · exact h
  · exact absurd (ha.2.1 b h) (hb.2.2 (by omega))

theorem spF2_append {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} (a : α) (b : β), List.Forall₂ R l1 l2 → R a b →
      List.Forall₂ R (l1 ++ [a]) (l2 ++ [b])
  | [], [], _, _, .nil, h => List.Forall₂.cons h List.Forall₂.nil
  | _ :: _, _ :: _, a, b, .cons hab ht, h => List.Forall₂.cons hab (spF2_append a b ht h)

theorem spLt_asymm {a b : List w8} (h : go.GoStringLt a b) : ¬ go.GoStringLt b a := fun h' =>
  goStringLt_irrefl_w _ (goStringLt_trans h h')

/-- The parent's entries after a part's `put` (see the module doc). -/
theorem spParentWs_step (ws0 : List WEntry) (i0 : Nat) (ps : List (w64 × List w8)) (ws ws' : List WEntry)
    (p : w64 × List w8) (e : WEntry) (idx : Nat) (ok : List w8)
    (hpw : parentWs ws0 i0 ps ws) (hs : wsSorted ws)
    (hidx : idx ≤ ws.length ∧ (∀ k < idx, go.GoStringLt (wKey ws k) ok) ∧
      (idx < ws.length → ¬ go.GoStringLt (wKey ws idx) ok))
    (hput : ws'.map ownFresh =
      (putList ws idx (decide (idx < ws.length ∧ wKey ws idx = ok)) e).map ownFresh)
    (he : e.flags = W32 0 ∧ e.pgid = p.1 ∧ e.key = p.2 ∧ e.value = [] ∧ e.ks ≠ Src.stale ∧
      e.vs ≠ Src.stale)
    (hfirst : ps = [] → (∃ w, ws0[i0]? = some w ∧ w.key = ok) ∨ (ws0 = [] ∧ i0 = 0))
    (hlater : ps ≠ [] → ok = p.2)
    (hlo : ∀ w ∈ ws0.take i0, go.GoStringLt w.key p.2)
    (hhi : ∀ w ∈ ws0.drop (i0 + 1), go.GoStringLt p.2 w.key)
    (hes : ∀ q ∈ ps, go.GoStringLt q.2 p.2) :
    parentWs ws0 i0 (ps ++ [p]) ws' ∧ wsSorted ws' := by
  have hpe1 : pieceEntries [p] [e] := List.Forall₂.cons he List.Forall₂.nil
  have hk' : ws'.map WEntry.key =
      (putList ws idx (decide (idx < ws.length ∧ wKey ws idx = ok)) e).map WEntry.key := by
    rw [← spFresh_key ws', hput, spFresh_key]
  rcases hpw with ⟨hps0, hws⟩ | ⟨hne, E, hpe, hws⟩
  · subst hps0
    have hk : ws.map WEntry.key = ws0.map WEntry.key := by rw [← spFresh_key ws, hws, spFresh_key]
    have hlen : ws.length = ws0.length := by simpa using congrArg List.length hk
    have hwk : ∀ k, wKey ws k = wKey ws0 k := fun k => by rw [spWKey_keys, spWKey_keys, hk]
    rcases hfirst rfl with ⟨w, hw, hwk0⟩ | ⟨rfl, rfl⟩
    · -- the node's own entry replaced
      have hi0 : i0 < ws0.length := (List.getElem?_eq_some_iff.1 hw).1
      have hs0 : wsSorted ws0 := by rw [spSortedK, ← hk]; exact (spSortedK ws).1 hs
      have hw0 : wKey ws0 i0 = ok := by unfold wKey; rw [hw]; exact hwk0
      have hm : i0 ≤ ws.length ∧ (∀ k < i0, go.GoStringLt (wKey ws k) ok) ∧
          (i0 < ws.length → ¬ go.GoStringLt (wKey ws i0) ok) :=
        ⟨by omega, fun k hk => by rw [hwk, ← hw0]; exact hs0 k i0 hk hi0,
          fun _ => by rw [hwk, hw0]; exact goStringLt_irrefl_w _⟩
      have hix := spSearch_unique ws ok idx i0 hidx hm
      subst hix
      have hbx : decide (idx < ws.length ∧ wKey ws idx = ok) = true :=
        decide_eq_true ⟨by omega, by rw [hwk, hw0]⟩
      rw [hbx] at hput hk'
      unfold putList at hput hk'
      simp only [ite_true] at hput hk'
      have h2 : ws0[idx] = w := by
        have := hw; rw [List.getElem?_eq_getElem hi0] at this; exact Option.some.inj this
      have hdec : ws0.map WEntry.key =
          (ws0.take idx).map WEntry.key ++ w.key :: (ws0.drop (idx + 1)).map WEntry.key := by
        have e0 : ws0 = ws0.take idx ++ w :: ws0.drop (idx + 1) := by
          rw [← h2, ← List.drop_eq_getElem_cons hi0, List.take_append_drop]
        have e := congrArg (List.map WEntry.key) e0
        simp only [List.map_append, List.map_cons] at e
        exact e
      have hP := (spSortedK ws0).1 hs0
      rw [hdec] at hP
      have hP' : ((ws0.take idx).map WEntry.key ++ (ws0.drop (idx + 1)).map WEntry.key).Pairwise
          go.GoStringLt :=
        hP.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
      refine ⟨Or.inr ⟨by simp, [e], hpe1, ?_⟩, ?_⟩
      · rw [hput, List.map_set, hws, ← List.map_set, List.set_eq_take_append_cons_drop, if_pos hi0]
        simp
      · rw [spSortedK, hk', List.map_set, hk, List.set_eq_take_append_cons_drop, if_pos (by simpa using hi0),
          ← List.map_take, ← List.map_drop, he.2.2.1]
        refine spPairwise_ins _ _ _ hP' (fun a ha => ?_) (fun b hb => ?_)
        · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 ha; exact hlo w' hw'
        · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hb; exact hhi w' hw'
    · -- the first entry of a new parent
      have hw0 : ws = [] := by simpa using hlen
      subst hw0
      have hi0 : idx = 0 := by have := hidx.1; simp at this; exact this
      subst hi0
      have hbx : decide (0 < ([] : List WEntry).length ∧ wKey [] 0 = ok) = false := by simp
      rw [hbx] at hput hk'
      refine ⟨Or.inr ⟨by simp, [e], hpe1, ?_⟩, ?_⟩
      · rw [hput]; rfl
      · rw [spSortedK, hk']; simp [putList]
  · -- a later part: after the parts before it
    have hok := hlater hne
    subst hok
    have hk : ws.map WEntry.key = (ws0.take i0).map WEntry.key ++ E.map WEntry.key ++
        (ws0.drop (i0 + 1)).map WEntry.key := by
      rw [← spFresh_key ws, hws, spFresh_key]; simp only [List.map_append]
    have hlen : ws.length = (ws0.take i0).length + E.length + (ws0.drop (i0 + 1)).length := by
      have := congrArg List.length hk; simp only [List.length_map, List.length_append] at this; exact this
    have hEk : ∀ k ∈ E.map WEntry.key, go.GoStringLt k p.2 := fun k hk => by
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hk
      obtain ⟨q, hq, hqw⟩ := spF2_mem_r hpe w' hw'
      rw [hqw.2.2.1]; exact hes q hq
    have hlAE : ((ws0.take i0).map WEntry.key ++ E.map WEntry.key).length =
        (ws0.take i0).length + E.length := by simp
    have hwm : (ws0.take i0).length + E.length < ws.length →
        go.GoStringLt p.2 (wKey ws ((ws0.take i0).length + E.length)) := fun h => by
      rw [spWKey_keys, hk, List.getElem?_append_right (by rw [hlAE]; exact Nat.le_refl _), hlAE, Nat.sub_self]
      have hC : 0 < ((ws0.drop (i0 + 1)).map WEntry.key).length := by
        simp only [List.length_map]; omega
      rw [List.getElem?_eq_getElem hC]
      obtain ⟨w', hw', he'⟩ := List.mem_map.1 (List.getElem_mem hC)
      simp only [Option.getD_some]; rw [← he']; exact hhi w' hw'
    have hm : (ws0.take i0).length + E.length ≤ ws.length ∧
        (∀ k < (ws0.take i0).length + E.length, go.GoStringLt (wKey ws k) p.2) ∧
        ((ws0.take i0).length + E.length < ws.length →
          ¬ go.GoStringLt (wKey ws ((ws0.take i0).length + E.length)) p.2) := by
      refine ⟨by omega, fun k hk3 => ?_, fun h => spLt_asymm (hwm h)⟩
      have hk2 : k < ((ws0.take i0).map WEntry.key ++ E.map WEntry.key).length := by rw [hlAE]; exact hk3
      rw [spWKey_keys, hk, List.getElem?_append_left hk2, List.getElem?_eq_getElem hk2]
      simp only [Option.getD_some]
      rcases List.mem_append.1 (List.getElem_mem hk2) with h | h
      · obtain ⟨w', hw', he'⟩ := List.mem_map.1 h; rw [← he']; exact hlo w' hw'
      · exact hEk _ h
    have hix := spSearch_unique ws p.2 idx _ hidx hm
    subst hix
    have hbx : decide ((ws0.take i0).length + E.length < ws.length ∧
        wKey ws ((ws0.take i0).length + E.length) = p.2) = false := by
      apply decide_eq_false; intro ⟨h1, h2⟩
      have := hwm h1; rw [h2] at this; exact goStringLt_irrefl_w _ this
    rw [hbx] at hput hk'
    unfold putList at hput hk'
    simp only [Bool.false_eq_true, if_false] at hput hk'
    have hlf : ((ws0.take i0).map ownFresh ++ E.map ownFresh).length = (ws0.take i0).length + E.length := by
      simp
    refine ⟨Or.inr ⟨by simp, E ++ [e], spF2_append p e hpe he, ?_⟩, ?_⟩
    · rw [hput, List.map_append, List.map_cons, List.map_take, List.map_drop, hws]
      simp only [List.map_append]
      rw [List.take_left' hlf, List.drop_left' hlf]
      simp
    · rw [spSortedK, hk', List.map_append, List.map_cons, List.map_take, List.map_drop, hk,
        List.take_left' hlAE, List.drop_left' hlAE, he.2.2.1]
      have hP := (spSortedK ws).1 hs
      rw [hk] at hP
      refine spPairwise_ins _ _ _ hP (fun a ha => ?_) (fun b hb => ?_)
      · rcases List.mem_append.1 ha with h | h
        · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 h; exact hlo w' hw'
        · exact hEk _ h
      · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hb; exact hhi w' hw'

theorem spLt_le {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot b c with h | rfl | h
  · exact goStringLt_trans h1 h
  · exact h1
  · exact absurd h h2

theorem spLe_lt {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot a b with h | rfl | h
  · exact goStringLt_trans h h2
  · exact h2
  · exact absurd h h1

/-- The parts' first keys increase (a split in two or more parts: every part non-empty). -/
theorem spChunkHeads_lt (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (hil : rc.ins.length = rc.ws.length)
    (hs : wsSorted rc.ws) (lo hi : Option (List w8))
    (hkb : ∀ w ∈ rc.ws, 0 < w.key.length ∧ keyIn lo hi w.key) (h2 : 2 ≤ xs.length) :
    ∀ j j', j < j' → j' < xs.length →
      go.GoStringLt (wHead ((chunksOf rc xs).getD j [])).key (wHead ((chunksOf rc xs).getD j' [])).key := by
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [← hil, ← hst.2.2.2.1.1, List.length_flatten, List.map_map]; exact Nat.le_refl _
  have hcl : (chunksOf rc xs).length = xs.length := by
    unfold chunksOf; rw [spWsChunks_length, List.length_map]
  have hne : ∀ k, k < xs.length → (chunksOf rc xs).getD k [] ≠ [] := by
    intro k hk h
    have hk' : (xs.map (fun x => x.2.2.length))[k]? = some xs[k].2.2.length := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    obtain ⟨hlen, -⟩ := wsChunks_get rc.ws _ k _ hk' hsum
    have hlen' : ((chunksOf rc xs).getD k []).length = xs[k].2.2.length := hlen
    rw [h] at hlen'
    rcases hsr with ⟨hxs1, -⟩ | ⟨-, -, -, -, hsp, -⟩
    · rw [hxs1] at h2; simp at h2
    · have := hsp.2.2 h2 xs[k] (List.getElem_mem hk); simp at hlen'; omega
  have hstep : ∀ j, j + 1 < xs.length →
      go.GoStringLt (wHead ((chunksOf rc xs).getD j [])).key (wHead ((chunksOf rc xs).getD (j + 1) [])).key := by
    intro j hj
    obtain ⟨-, hkc⟩ := spChunkKeysOf bl n rc rp xs T B K Ts Bs Ks par ws0 i0 hst hsr hil hs lo hi hkb j
      (hne j (by omega))
    have hm : wHead ((chunksOf rc xs).getD j []) ∈ (chunksOf rc xs).getD j [] := by
      cases h : (chunksOf rc xs).getD j [] with
      | nil => exact absurd h (hne j (by omega))
      | cons a l => exact List.mem_cons_self
    have := (hkc _ hm).2.2
    have hhi : hiAt (chunksOf rc xs) hi j = some (wHead ((chunksOf rc xs).getD (j + 1) [])).key := by
      unfold hiAt
      rw [List.getElem?_eq_getElem (by rw [hcl]; exact hj)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hcl]; exact hj)]; rfl
    exact this _ hhi
  intro j j' hjj hj'
  induction j' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjj with h | rfl
    · exact goStringLt_trans (ih h (by omega)) (hstep k hj')
    · exact hstep j hj'

/-- A dereference changes no bucket's nodes but by `derefStarX`. -/
theorem spFrame_deref (T3 T0 : WTx) (h : T0 = T3 ∨ (derefRelX T3 T0 ∧ derefKeep T3 T0)) (X : Loc → Prop) :
    spillFrame T3 T0 X := by
  rcases h with rfl | ⟨hd, hk⟩
  · exact spillFrame_reflN _ _
  refine ⟨hd.2.2.2.2.1, by rw [hd.2.1], by rw [hd.2.1]; try exact Nat.le_refl _,
    by rw [hd.2.2.2.1]; exact GMap.map_subseteq_refl _, hd.1,
    fun c C C' _ hC hC' => ⟨Or.inr (hd.2.2.2.2.2 c C C' hC hC'), fun l r r' hr hr' => hk c C C' l r r' hC hC' hr hr'⟩⟩

theorem spFrame_stats (T : WTx) (st : TxStats) (X : Loc → Prop) :
    spillFrame T { T with t := { T.t with stats' := st } } X := by
  refine ⟨fun _ => Iff.rfl, rfl, Nat.le_refl _, GMap.map_subseteq_refl _, rfl, ?_⟩
  intro c C C' _ hC hC'
  have hC2 : T.bs !! c = some C' := hC'
  rw [hC] at hC2; cases hC2
  exact ⟨Or.inl rfl, fun l r r' hr hr' => by rw [hr] at hr'; cases hr'; rfl⟩

/-- Two frames glued over a step `T0` to `T5` that changes only the bucket `bl` and the
buffers (`hbuf` the buffers' frame for the whole). -/
theorem spFrame_glue (T1 T0 T5 T6 : WTx) (bl : Loc) (h0 : spillFrame T1 T0 (· = bl))
    (h5 : spillFrame T5 T6 (· = bl)) (hbs : ∀ c, c ≠ bl → T5.bs !! c = T0.bs !! c)
    (hdom : ∀ c, (T0.bs !! c).isSome ↔ (T5.bs !! c).isSome) (htx : T5.mv.txid' = T0.mv.txid')
    (hpg : uint.nat T0.mv.pgid' ≤ uint.nat T5.mv.pgid') (hbuf : T1.bufs ⊆ T6.bufs)
    (ht : T5.t = { T0.t with stats' := T5.t.stats' }) : spillFrame T1 T6 (· = bl) := by
  obtain ⟨a0, b0, c0, -, e0, f0⟩ := h0
  obtain ⟨a5, b5, c5, -, e5, f5⟩ := h5
  refine ⟨fun c => (a0 c).trans ((hdom c).trans (a5 c)), b5.trans (htx.trans b0),
    Nat.le_trans c0 (Nat.le_trans hpg c5), hbuf, by rw [e5, ht, e0], ?_⟩
  intro c C C' hX hC hC'
  obtain ⟨C0, hC0⟩ := Option.isSome_iff_exists.1 ((a0 c).1 (by rw [hC]; rfl))
  obtain ⟨s1, k1⟩ := f0 c C C0 hX hC hC0
  have hC5 : T5.bs !! c = some C0 := by rw [hbs c hX]; exact hC0
  obtain ⟨s2, k2⟩ := f5 c C0 C' hX hC5 hC'
  refine ⟨derefStarX_trans _ _ _ s1 s2, fun l r r' hr hr' => ?_⟩
  obtain ⟨r2, hr2⟩ := derefStarX_ns C0 C' s2 l r' hr'
  rw [k2 l r2 r' hr2 hr', k1 l r r2 hr hr2]

theorem spDnK_keyNN (r r' : NRec) (h : dnK r r') (hk : r.nv.key' ≠ slice.nil) (hl : 0 < r.key.length) :
    r'.nv.key' ≠ slice.nil ∧ r'.key = r.key := by
  rcases h with rfl | ⟨⟨hd, hx⟩, -⟩
  · exact ⟨hk, rfl⟩
  · exact ⟨hx hk hl, hd.2.2.2.1⟩

theorem spDnK_ksrc (r r' : NRec) (h : dnK r r') : r'.ksrc = r.ksrc ∨ r'.ksrc = Src.own (DFrac.own 1) := by
  rcases h with rfl | ⟨⟨hd, -⟩, -⟩
  · exact Or.inl rfl
  · exact Or.inr hd.2.2.2.2.2.1

theorem spSorted_fresh (a b : List WEntry) (h : a.map ownFresh = b.map ownFresh) (hs : wsSorted a) :
    wsSorted b := by
  rw [spSortedK] at hs ⊢
  rw [← spFresh_key b, ← h, spFresh_key]; exact hs

theorem spParentWs_fresh (ws0 : List WEntry) (i0 : Nat) (ps : List (w64 × List w8)) (a b : List WEntry)
    (h : a.map ownFresh = b.map ownFresh) (hp : parentWs ws0 i0 ps a) : parentWs ws0 i0 ps b := by
  unfold parentWs at hp ⊢; rw [← h]; exact hp

/-- What a part's record keeps of the node's key (the first part) or has none (the others). -/
theorem spPartKeys (bl n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0) (j : Nat)
    (xe : Loc × node × List Inode) (hxe : xs[j]? = some xe) (rs rx : NRec)
    (hrs : Bs.ns !! xe.1 = some rs) (hdn : dnK rs rx) :
    (j = 0 → rc.nv.key' ≠ slice.nil → 0 < rc.key.length → rx.nv.key' ≠ slice.nil ∧ rx.key = rc.key) ∧
    (0 < j → rx.nv.key' = slice.nil) := by
  obtain ⟨-, -, -, -, -, -, -, hpr, -, hhd, hdrop⟩ := hst
  have h1 := hpr j xe hxe
  rw [hrs] at h1; cases h1
  obtain ⟨-, -, -, -, -, -, -, -, hkn⟩ := spDnK_facts _ rx hdn
  refine ⟨fun hj hk hl => ?_, fun hj => ?_⟩
  · subst hj
    have hh := hhd xe (by rw [List.head?_eq_getElem?]; exact hxe)
    have e1 : (partRec rc 0 xe ((chunksOf rc xs).getD 0 [])).nv.key' = rc.nv.key' := by
      simp only [partRec, ↓reduceIte]; rw [hh]
    have e2 : (partRec rc 0 xe ((chunksOf rc xs).getD 0 [])).key = rc.key := by
      simp only [partRec, ↓reduceIte]
    obtain ⟨a, b⟩ := spDnK_keyNN _ rx hdn (by rw [e1]; exact hk) (by rw [e2]; exact hl)
    exact ⟨a, by rw [b, e2]⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hx : xe ∈ xs.drop 1 := by
      rw [List.mem_iff_getElem?]; exact ⟨k, by rw [List.getElem?_drop]; simpa [Nat.add_comm] using hxe⟩
    apply hkn
    simp only [partRec, Nat.add_one_ne_zero, ↓reduceIte]
    exact (hdrop xe hx).2

/-- The split's parent, the node's existing one: its entries `ws0`, the node's at `i0`. -/
theorem spParentEntry (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx)
    (B : BRec) (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc)
    (ws0 : List WEntry) (i0 : Nat) (hst : startP bl n rc xs par Bs ws0 i0)
    (hsr : splitRes bl n rc rp xs T B K Ts Bs Ks par) (hp : rc.nv.parent' ≠ null)
    (hrp : B.ns !! rc.nv.parent' = some rp) (hs : wsSorted rp.ws) (i1 : Nat) (w : WEntry)
    (hw : rp.ws[i1]? = some w) (hk : w.key = rc.key) :
    par = rc.nv.parent' ∧ ws0 = rp.ws ∧ i0 = i1 := by
  obtain ⟨hne, -, -, -, h1, h2, h3, -⟩ := hst
  have hpar : par = rc.nv.parent' := by
    by_cases hl : xs.length = 1
    · exact h1 hl
    · have : xs.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.1 h)
      exact (h2 (by omega)).2 hp
  obtain ⟨rp0, hrp0, hws0, hcase⟩ := h3 (by rw [hpar]; exact hp)
  have hrp0' : rp0.ws = rp.ws := by
    rcases hsr with ⟨-, -, rfl, -⟩ | ⟨pv', pcs', st, -, -, -, hfr, -, hBs, -⟩
    · rw [hpar, hrp] at hrp0; cases hrp0; rfl
    · rw [hBs] at hrp0
      have := splitNs_par B.ns rc rp xs par pv' pcs' hfr.2.2.1
      have hrp0e : splitNs B.ns rc rp xs par pv' pcs' !! par = some rp0 := hrp0
      rw [this] at hrp0e; cases hrp0e
      unfold parentRec; rw [if_neg hp]
  refine ⟨hpar, by rw [← hws0, hrp0'], ?_⟩
  rcases hcase with ⟨-, w', hw', hk', -⟩ | ⟨h, -⟩
  · rw [← hws0, hrp0'] at hw'
    have hl1 : i1 < rp.ws.length := (List.getElem?_eq_some_iff.1 hw).1
    have hl0 : i0 < rp.ws.length := (List.getElem?_eq_some_iff.1 hw').1
    refine wsSorted_inj rp.ws hs i0 i1 hl0 hl1 ?_
    unfold wKey; rw [hw, hw']; simp only [Option.map_some, Option.getD_some]; rw [hk, hk']
  · exact absurd h hp

/-- `derefOK` survives a dereference. -/
theorem spDerefOK_dnK (bl : Loc) (r r' : NRec) (h : dnK r r') (hd : derefOK bl r) : derefOK bl r' := by
  obtain ⟨hlv, hil, hws, hnv, -, hkey, -, hks, hkn⟩ := spDnK_facts r r' h
  obtain ⟨d1, d2, d3, d4⟩ := hd
  refine ⟨by rw [hnv]; exact d1, hil d2, fun w hw => ?_, ?_⟩
  · have hl := hlv (fun w hw => ⟨(d3 w hw).1, (d3 w hw).2.1⟩) w hw
    have hm : ownFresh w ∈ r.ws.map ownFresh := by rw [← hws]; exact List.mem_map_of_mem hw
    obtain ⟨w0, hw0, he⟩ := List.mem_map.1 hm
    have hk : w0.key = w.key := by have := congrArg WEntry.key he; exact this
    exact ⟨hl.1, hl.2, by rw [← hk]; exact (d3 w0 hw0).2.2⟩
  · rcases d4 with h4 | ⟨h4, h5⟩
    · exact Or.inl (hkn h4)
    · refine Or.inr ⟨hks h4, ?_⟩
      have hpg : r'.nv.pgid' = r.nv.pgid' := by rw [hnv]
      rw [hpg, hkey]; exact h5

theorem spNvUpd2 (a b c : node) (h1 : a = { b with inodes' := a.inodes', key' := a.key' })
    (h2 : b = { c with inodes' := b.inodes', key' := b.key' }) :
    a = { c with inodes' := a.inodes', key' := a.key' } := by
  rw [h1]; rw [h2]

theorem spMem_take_succ {α β : Type} (f : α → β) (l : List α) (k : Nat) (y : β)
    (h : y ∈ (l.take k).map f) : y ∈ (l.take (k + 1)).map f := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  refine List.mem_map_of_mem ?_
  rw [List.take_succ]; exact List.mem_append_left _ ha

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `partsP` one part longer: the part `xs[ps.length]` written at `p`, put into the parent. -/
theorem spPartsP_step (bl txl : Loc) (txid : w64) (n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode))
    (par : Loc) (ws0 : List WEntry) (i0 : Nat) (lo hi : Option (List w8))
    (Ws : WView) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool)
    (W : WView) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec)
    (ps : List (w64 × List w8))
    (hpp : partsP (hG := hG) bl txl txid n rc xs par ws0 i0 lo hi Ws Ts Bs Ks W T ρ F K B ps)
    (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)) (B' : BRec) (p : w64 × List w8)
    (xe : Loc × node × List Inode) (hxe : xs[ps.length]? = some xe)
    (hnd : (xs.map (fun x => x.1)).Nodup)
    (hg : spillG (hG := hG) W' txl txid T' ρ' F') (hT' : T'.bs !! bl = some B')
    (hfr : spillFrame T T' (· = bl)) (hWp : W'.pages = W.pages) (hWps : W'.ps = W.ps)
    (hPP : spillPages W T ⊆ spillPages W' T')
    (hbv : B'.bv = B.bv) (hib : B'.ib = B.ib) (hnm : B'.nm = B.nm) (hbm : B'.bm = B.bm)
    (rx' : NRec) (hx' : B'.ns !! xe.1 = some rx') (hsp' : rx'.nv.spilled' = true) (hcs' : rx'.cs = [])
    (hb' : rx'.nv.bucket' = bl) (hil' : rx'.ins.length = rx'.ws.length) (hdok' : derefOK bl rx')
    (hpg' : rx'.nv.pgid' = p.1) (hpar' : rx'.nv.parent' = par)
    (hws' : rx'.ws.map ownFresh = ((chunksOf rc xs).getD ps.length []).map ownFresh)
    (hlf' : rx'.nv.isLeaf' = rc.nv.isLeaf') (hpos' : par ≠ null → 0 < rx'.ins.length)
    (hp2 : p.2 = (wHead ((chunksOf rc xs).getD ps.length [])).key)
    (hf1 : T.bufs !! p.1 = none) (hf2 : W.pages !! uint.nat p.1 = none) (hf3 : (T'.bufs !! p.1).isSome)
    (hf4 : B.nm !! p.1 = none) (hf5 : 2 ≤ uint.nat p.1)
    (hoth : ∀ y r, y ≠ xe.1 → (par ≠ null → y ≠ par) → B.ns !! y = some r →
      ∃ r', B'.ns !! y = some r' ∧ dnK r r')
    (hdom : ∀ y, (B'.ns !! y).isSome → (B.ns !! y).isSome)
    (hparP : par ≠ null → ∀ rp, B.ns !! par = some rp → ∃ rp', B'.ns !! par = some rp' ∧
      parentWs ws0 i0 (ps ++ [p]) rp'.ws ∧ wsSorted rp'.ws ∧ wsLive rp'.ws ∧
      rp'.ins.length = rp'.ws.length ∧
      rp'.nv = { rp.nv with inodes' := rp'.nv.inodes', key' := rp'.nv.key' } ∧ rp'.cs = rp.cs ∧
      rp'.key = rp.key ∧ (rp.nv.key' = slice.nil → rp'.nv.key' = slice.nil) ∧
      (rp.nv.key' ≠ slice.nil → 0 < rp.key.length → rp'.nv.key' ≠ slice.nil) ∧
      (rp'.ksrc = rp.ksrc ∨ rp'.ksrc = Src.own (DFrac.own 1)))
    (hlv : ∃ S, liveNodesX B' S ∧ (∀ l ∈ S, ∃ r, B'.ns !! l = some r ∧ derefOK bl r) ∧
      (∀ (j : Nat) (x : Loc), (xs[j]?).map (fun x => x.1) = some x → x ∈ S) ∧ (par ≠ null → par ∈ S) ∧
      (∀ l r, B'.ns !! l = some r → l ∉ S → noViewRec r)) :
    partsP (hG := hG) bl txl txid n rc xs par ws0 i0 lo hi Ws Ts Bs Ks W' T' ρ' F' K B' (ps ++ [p]) := by
  obtain ⟨-, -, P3, P4, P5, P6, P7, P8, P9, P10, -, P12, P13, P14, P15, P16, P17, P18, P19, P20, -⟩ := hpp
  have hlt : ps.length < xs.length := (List.getElem?_eq_some_iff.1 hxe).1
  have hlen : (ps ++ [p]).length = ps.length + 1 := by simp
  have hsub : ∀ k v, T.bufs !! k = some v → T'.bufs !! k = some v := hfr.2.2.2.1
  have hsubs : ∀ k v, Ts.bufs !! k = some v → T.bufs !! k = some v := P3.2.2.2.1
  -- the location of part j
  have hxj : ∀ (j : Nat) (x : Loc), (xs[j]?).map (fun x => x.1) = some x → j < xs.length ∧ (x = xe.1 ↔ j = ps.length) := by
    intro j x hj
    cases h : xs[j]? with
    | none => rw [h] at hj; cases hj
    | some y =>
      rw [h] at hj; cases hj
      have hjl : j < xs.length := (List.getElem?_eq_some_iff.1 h).1
      refine ⟨hjl, fun e => ?_, fun e => by subst e; rw [hxe] at h; cases h; rfl⟩
      have h1 : (xs.map (fun x => x.1))[j]? = some y.1 := by rw [List.getElem?_map, h]; rfl
      have h2 : (xs.map (fun x => x.1))[ps.length]? = some y.1 := by
        rw [List.getElem?_map, hxe]; simp only [Option.map_some, Option.some.injEq]; simp only at e; exact e.symm
      exact (List.Nodup.getElem?_inj (by simpa using hjl) hnd).1 (h1.trans h2.symm)
  have hpnx : par ≠ null → ∀ (j : Nat) (x : Loc), (xs[j]?).map (fun x => x.1) = some x → x ≠ par := by
    intro hp j x hj e
    obtain ⟨rp, -, -, -, -, -, -, -, hnot, -⟩ := P17 hp
    apply hnot; rw [← e]
    cases h : xs[j]? with
    | none => rw [h] at hj; cases hj
    | some y => rw [h] at hj; cases hj; exact List.mem_map_of_mem (List.mem_of_getElem? h)
  refine ⟨hg, hT', spillFrame_transN _ _ _ _ _ P3 hfr (fun _ h => h), hWp.trans P4, hWps.trans P5,
    GMap.map_subseteq_trans P6 hPP, hbv.trans P7, hib.trans P8, hnm.trans P9, hbm.trans P10,
    by rw [hlen]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlv⟩
  · -- the parts written
    intro j x hj hjx
    rw [hlen] at hj
    obtain ⟨-, hxe1⟩ := hxj j x hjx
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · obtain ⟨hsN, rx, q, hrx, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := P12 j x hj hjx
      have hxn : x ≠ xe.1 := fun e => by have := hxe1.1 e; omega
      obtain ⟨r', hr', hdn⟩ := hoth x rx hxn (fun hp => hpnx hp j x hjx) hrx
      obtain ⟨hlv1, hil1, hws1, hnv1, hcs1, -, hwl1, -, -⟩ := spDnK_facts rx r' hdn
      have hq : (ps ++ [p])[j]? = some q := by rw [List.getElem?_append_left hj]; exact h6
      refine ⟨fun hp => ?_, r', q, hr', by rw [hnv1]; exact h1, by rw [hcs1]; exact h2,
        by rw [hnv1]; exact h3, hil1 h4, spDerefOK_dnK bl rx r' hdn h5, hq, by rw [hnv1]; exact h7,
        by rw [hnv1]; exact h8, by rw [hws1]; exact h9, by rw [hnv1]; exact h10⟩
      obtain ⟨r0, hr0, s1, s2, s3, s4, s5, s6, s7⟩ := hsN hp
      rw [hrx] at hr0; cases hr0
      refine ⟨r', hr', by rw [hnv1]; exact s1, by rw [hcs1]; exact s2, by rw [hnv1]; exact s3,
        by rw [hil1 s5, hwl1, ← s5]; exact s4, hil1 s5, spDerefOK_dnK bl rx r' hdn s6, ?_⟩
      have hpg1 : r'.nv.pgid' = rx.nv.pgid' := by rw [hnv1]
      rw [hnm, hpg1]; exact s7
    · have hxx : x = xe.1 := hxe1.2 rfl
      subst hxx
      have hq : (ps ++ [p])[ps.length]? = some p := by simp
      refine ⟨fun hp => ⟨rx', hx', hsp', hcs', hb', hpos' hp, hil', hdok', by rw [hnm, hpg']; exact hf4⟩,
        rx', p, hx', hsp', hcs', hb', hil', hdok', hq, hpg', hpar', hws', hlf'⟩
  · -- the parts not written
    intro j x hj hjx
    rw [hlen] at hj
    obtain ⟨-, hxe1⟩ := hxj j x hjx
    obtain ⟨rs, rx, hrs, hrx, hdn0, hz⟩ := P13 j x (by omega) hjx
    have hxn : x ≠ xe.1 := fun e => by have := hxe1.1 e; omega
    obtain ⟨r', hr', hdn⟩ := hoth x rx hxn (fun hp => hpnx hp j x hjx) hrx
    obtain ⟨-, -, -, hnv1, -, -, -, -, -⟩ := spDnK_facts rx r' hdn
    refine ⟨rs, r', hrs, hr', ?_, fun h0 => by rw [hnv1]; exact hz h0⟩
    rcases hdn with rfl | hdn
    · exact hdn0
    · exact dnK_step _ _ _ hdn0 (Or.inr hdn)
  · -- the parts' keys
    intro j q hq
    by_cases hj : j < ps.length
    · rw [List.getElem?_append_left hj] at hq; exact P14 j q hq
    · have hj' : j = ps.length := by
        have := (List.getElem?_eq_some_iff.1 hq).1; rw [hlen] at this; omega
      subst hj'
      simp at hq; subst hq; exact hp2
  · -- the parts' pages
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨a, b, c, d, e⟩ := P15 q hq
      refine ⟨a, b, ?_, d, e⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 c
      rw [hsub _ _ hv]; rfl
    · rw [List.mem_singleton] at hq; rw [hq]
      refine ⟨?_, by rw [← P4]; exact hf2, hf3, by rw [← P9]; exact hf4, hf5⟩
      cases h : Ts.bufs !! p.1 with
      | none => rfl
      | some v => rw [hsubs _ _ h] at hf1; cases hf1
  · -- the parts' pages distinct
    rw [List.map_append, List.nodup_append]
    refine ⟨P16, by simp, fun a ha b hb e => ?_⟩
    simp at hb; subst hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    have := (P15 q hq).2.2.1
    rw [e, hf1] at this; cases this
  · -- the parent
    intro hp
    obtain ⟨rp, hrp, hK, -, -, -, -, hbp, hnot, rp0, hrp0, hcs0, hkey0, hnv0, hkn0, hknn0, hks0⟩ := P17 hp
    obtain ⟨rp', hrp', hpw, hsrt, hlvp, hilp, hnv', hcs', hkey', hkn', hknn', hks'⟩ := hparP hp rp hrp
    refine ⟨rp', hrp', hK, hpw, hlvp, hilp, hsrt, ?_, hnot, rp0, hrp0, by rw [hcs', hcs0],
      by rw [hkey', hkey0], spNvUpd2 _ _ _ hnv' hnv0, fun h => hkn' (hkn0 h),
      fun h hl => hknn' (hknn0 h hl) (by rw [hkey0]; exact hl), ?_⟩
    · have : rp'.nv.bucket' = rp.nv.bucket' := by rw [hnv']
      rw [this]; exact hbp
    · rcases hks' with h | h
      · rw [h]; exact hks0
      · exact Or.inr h
  · -- the others
    intro x rs hx hxp hrs
    obtain ⟨rx, hrx, hdn0⟩ := P18 x rs hx hxp hrs
    have hxn : x ≠ xe.1 := fun e => hx (by rw [e]; exact List.mem_map_of_mem (List.mem_of_getElem? hxe))
    obtain ⟨r', hr', hdn⟩ := hoth x rx hxn (fun _ => hxp) hrx
    refine ⟨r', hr', ?_⟩
    rcases hdn with rfl | hdn
    · exact hdn0
    · exact dnK_step _ _ _ hdn0 (Or.inr hdn)
  · intro x hx; exact P19 x (hdom x hx)
  · intro x hx
    rw [hlen] at hx
    exact P20 x (fun h => hx (spMem_take_succ _ _ _ _ h))

end own

end bbolt
end EtcdGrove
end Perennial
