/-
`node.spill`'s children loop (`Proof/go_etcd_io/bbolt/SpillNodeCore.lean`): its invariant.

At iteration `i` of the loop over `n.children` (the node `n`, its record `rn`, the bucket's
`B`, the transaction `T`): the children before `i` are spilled parts (`spilledN`); each child
from `i` on is a spilled part (`sp c`) or an unspilled child with its tree `sub c` (`subU`); the
nodes outside `n`'s tree `S0` at the loop's start are as they were, possibly dereferenced
(`dnK`); of `S0`, only `n`, its children and the trees of the unspilled ones remain; the nodes
added are `n`'s children (the parts of its children). `n` holds its entries' trees (`rtoks`,
over the pages `spillPages W T`); each unspilled child's tree its nodes' (`subToks`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeSort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- `r'` is `r`, possibly dereferenced. -/
def dnK (r r' : NRec) : Prop := r' = r ∨ derefNodeK r r'

/-- `r'` is `r`, or `r` dereferenced or made stale (`dnX3`) keeping its struct but its key. -/
def dnS (r r' : NRec) : Prop := r' = r ∨ (dnX3 r r' ∧ r'.nv = { r.nv with key' := r'.nv.key' })

theorem dnS_trans (r r1 r2 : NRec) (h : dnS r r1) (h' : dnS r1 r2) : dnS r r2 := by
  rcases h with rfl | ⟨h1, n1⟩
  · exact h'
  · rcases h' with rfl | ⟨h2, n2⟩
    · exact Or.inr ⟨h1, n1⟩
    · refine Or.inr ⟨dnX3_trans _ _ _ h1 h2, ?_⟩
      rw [n2]; rw [n1]

theorem dnS_of_dnK (r r' : NRec) (h : dnK r r') : dnS r r' := by
  rcases h with rfl | ⟨hx, hnv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Or.inl hx, hnv⟩

theorem dnS_stale (r : NRec) : dnS r (staleRec r) := Or.inr ⟨Or.inr (Or.inr rfl), rfl⟩

theorem dnS_agree (r r' : NRec) (h : dnS r r') :
    r'.nv = { r.nv with key' := r'.nv.key' } ∧ r'.cs = r.cs := by
  rcases h with rfl | ⟨h1, n1⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨n1, (dnX3_agree r r' h1).2⟩

/-- The facts of the bucket's nodes `node.spill` keeps (its premises). -/
def nodesOK (W : WView) (T : WTx) (B : BRec) : Prop :=
  (∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
  (∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) ∧
  (∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome) ∧
  (∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
    (spillPages W T !! uint.nat w.pgid).isSome)


theorem wKey_fresh (ws : List WEntry) : wKey (ws.map ownFresh) = wKey ws := by
  funext i; unfold wKey; rw [List.getElem?_map]; cases ws[i]? <;> rfl

theorem wsSorted_inj (ws : List WEntry) (hs : wsSorted ws) (i j : Nat) (hi : i < ws.length)
    (hj : j < ws.length) (he : wKey ws i = wKey ws j) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := hs i j h hj; rw [he] at this; exact absurd this (goStringLt_irrefl_w _)
  · exact h
  · have := hs j i h hi; rw [he] at this; exact absurd this (goStringLt_irrefl_w _)


theorem node_upd3_trans (a b c : node)
    (h1 : a = { b with inodes' := a.inodes', children' := a.children', key' := a.key' })
    (h2 : b = { c with inodes' := b.inodes', children' := b.children', key' := b.key' }) :
    a = { c with inodes' := a.inodes', children' := a.children', key' := a.key' } := by
  rw [h1]; rw [h2]

theorem node_upd1_trans (a b c : node) (h1 : a = { b with key' := a.key' })
    (h2 : b = { c with key' := b.key' }) : a = { c with key' := a.key' } := by
  rw [h1]; rw [h2]

theorem derefNodeK_trans (r r1 r2 : NRec) (h1 : derefNodeK r r1) (h2 : derefNodeK r1 r2) :
    derefNodeK r r2 :=
  ⟨derefNodeX_trans _ _ _ h1.1 h2.1, node_upd1_trans _ _ _ h2.2 h1.2⟩

theorem dnK_step (r r1 r2 : NRec) (h1 : dnK r r1) (h2 : r2 = r1 ∨ derefNodeK r1 r2) : dnK r r2 := by
  rcases h2 with rfl | h2
  · exact h1
  · rcases h1 with rfl | h1
    · exact Or.inr h2
    · exact Or.inr (derefNodeK_trans _ _ _ h1 h2)

/-- What a dereference keeps of a node. -/
theorem dK_facts (r r' : NRec) (h : r' = r ∨ derefNodeK r r') :
    r'.nv = { r.nv with key' := r'.nv.key' } ∧ r'.cs = r.cs ∧ r'.key = r.key ∧
      (r'.ws = r.ws ∨ r'.ws = r.ws.map ownFresh) ∧ r'.ins.length = r'.ws.length ∨ r' = r := by
  rcases h with rfl | ⟨⟨⟨hnv, hws, hcs, hkey, -, -, hil⟩, -⟩, hnv'⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨hnv', hcs, hkey, Or.inr hws, hil⟩

theorem spilledN_keep (bl : Loc) (B B' : BRec) (c : Loc) (rc rc' : NRec) (hs : spilledN bl B c)
    (hrc : B.ns !! c = some rc) (hrc' : B'.ns !! c = some rc') (hd : rc' = rc ∨ derefNodeK rc rc')
    (hnmB : B'.nm = B.nm) :
    spilledN bl B' c := by
  obtain ⟨r0, hr0, hsp, hcs, hbk, hpos, hil, hok, hnm0⟩ := hs
  rw [hrc] at hr0; cases hr0
  rcases hd with rfl | ⟨⟨hd, -⟩, hnv⟩
  · exact ⟨rc', hrc', hsp, hcs, hbk, hpos, hil, hok, by rw [hnmB]; exact hnm0⟩
  · have hd0 := hd
    obtain ⟨-, hws, hcs', -, -, -, hil'⟩ := hd
    have e1 : rc'.nv.spilled' = rc.nv.spilled' := by rw [hnv]
    have e2 : rc'.nv.bucket' = rc.nv.bucket' := by rw [hnv]
    have e3 : rc'.nv.pgid' = rc.nv.pgid' := by rw [hnv]
    refine ⟨rc', hrc', by rw [e1]; exact hsp, by rw [hcs']; exact hcs, by rw [e2]; exact hbk,
      by rw [hil', hws, List.length_map, ← hil]; exact hpos, hil', derefOK_derefNode bl _ _ hok hd0,
      by rw [hnmB, e3]; exact hnm0⟩

theorem kidsTree_child (ns : GMap Loc NRec) :
    ∀ (N : Nat) (t : Loc) (S : List Loc), S.length ≤ N → kidsTree ns t S →
      ∀ l ∈ S, l ≠ t → ∃ y ∈ S, ∃ ry, ns !! y = some ry ∧ l ∈ ry.cs := by
  intro N
  induction N with
  | zero =>
    intro t S hl hk
    cases hk with
    | mk _ _ _ _ _ _ => simp at hl
  | succ N ih =>
    intro t S hl hk l hlS hlt
    cases hk with
    | mk _ r subs hr hF hnd =>
      rcases List.mem_cons.1 hlS with rfl | hl2
      · exact absurd rfl hlt
      · have key : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
            ss.flatten.length ≤ N → (∀ c ∈ cs, c ∈ r.cs) → (∀ x ∈ ss.flatten, x ∈ subs.flatten) →
            l ∈ ss.flatten → ∃ y ∈ t :: subs.flatten, ∃ ry, ns !! y = some ry ∧ l ∈ ry.cs := by
          intro cs ss hF2
          induction hF2 with
          | nil => intro _ _ _ h; simp at h
          | @cons c s cs' ss' hk2 _ ih2 =>
            intro hlen hcs hsub hl3
            simp only [List.flatten_cons, List.length_append, List.mem_append] at hlen hl3
            rcases hl3 with hl3 | hl3
            · by_cases hlc : l = c
              · subst hlc
                exact ⟨t, List.mem_cons_self, r, hr, hcs l List.mem_cons_self⟩
              · obtain ⟨y, hy, ry, hry, hly⟩ := ih c s (by omega) hk2 l hl3 hlc
                refine ⟨y, List.mem_cons_of_mem _ (hsub y ?_), ry, hry, hly⟩
                simp only [List.flatten_cons, List.mem_append]; exact Or.inl hy
            · exact ih2 (by omega) (fun c' h => hcs c' (List.mem_cons_of_mem _ h))
                (fun x hx => hsub x (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hx)) hl3
        exact key r.cs subs hF (by simp only [List.length_cons] at hl; omega) (fun c h => h)
          (fun x h => h) hl2

theorem spillPages_none (W : WView) (T : WTx) (p : w64) (h1 : W.pages !! uint.nat p = none)
    (h2 : T.bufs !! p = none) : spillPages W T !! uint.nat p = none := by
  unfold spillPages
  rw [GMap.lookup_union, show bufsN T.bufs !! uint.nat p = (if uint.nat p < 2 ^ 64 then
    T.bufs !! W64 ((uint.nat p : Nat) : Int) else none) from rfl, h1]
  have hlt : uint.nat p < 2 ^ 64 := by word
  rw [if_pos hlt]
  have e : W64 ((uint.nat p : Nat) : Int) = p := by word
  rw [e, h2]; rfl

theorem spillPages_buf (W : WView) (T : WTx) (p : w64) (h : (T.bufs !! p).isSome) :
    (spillPages W T !! uint.nat p).isSome := by
  unfold spillPages
  rw [GMap.lookup_union, show bufsN T.bufs !! uint.nat p = (if uint.nat p < 2 ^ 64 then
    T.bufs !! W64 ((uint.nat p : Nat) : Int) else none) from rfl]
  have hlt : uint.nat p < 2 ^ 64 := by word
  rw [if_pos hlt]
  have e : W64 ((uint.nat p : Nat) : Int) = p := by word
  rw [e]
  cases hw : W.pages !! uint.nat p <;> simp_all


/-- A child kept or dereferenced: its struct but its key, its key (non-nil), its children. -/
theorem child_keep (rc rc' : NRec) (hd : rc' = rc ∨ derefNodeK rc rc') (hkn : rc.nv.key' ≠ slice.nil)
    (hpos : 0 < rc.key.length) :
    rc'.nv.parent' = rc.nv.parent' ∧ rc'.nv.pgid' = rc.nv.pgid' ∧ rc'.key = rc.key ∧
      rc'.nv.key' ≠ slice.nil ∧ rc'.nv.isLeaf' = rc.nv.isLeaf' ∧ rc'.nv.spilled' = rc.nv.spilled' ∧
      rc'.cs = rc.cs := by
  rcases hd with rfl | ⟨⟨⟨-, -, hcs, hkey, -, -, -⟩, hkx⟩, hnv⟩
  · exact ⟨rfl, rfl, rfl, hkn, rfl, rfl, rfl⟩
  · refine ⟨by rw [hnv], by rw [hnv], hkey, hkx hkn hpos, by rw [hnv], by rw [hnv], hcs⟩

theorem ownFresh_key (w : WEntry) : (ownFresh w).key = w.key := rfl
theorem ownFresh_pgid (w : WEntry) : (ownFresh w).pgid = w.pgid := rfl

theorem entryBnd_fresh (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat) :
    entryBnd b (ws.map ownFresh) i = entryBnd b ws i := by
  unfold entryBnd; rw [wKey_fresh, List.length_map]

/-- An unspilled node kept or dereferenced, its children kept or dereferenced: still unspilled
(`nodeU`) in the new state. -/
theorem nodeU_keep (W W' : WView) (bl : Loc) (B B' : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (x : Loc) (r r' : NRec)
    (hpg : W'.pages = W.pages) (hnm : B'.nm = B.nm) (hd : r' = r ∨ derefNodeK r r')
    (hkid : ∀ c rc, c ∈ r.cs → B.ns !! c = some rc →
      ∃ rc', B'.ns !! c = some rc' ∧ (rc' = rc ∨ derefNodeK rc rc'))
    (h : nodeU W bl B bnd kd x r) : nodeU W' bl B' bnd kd x r' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hd0 := hd
  -- the children clause, for an entry list `ws'` with the old one's keys and page ids
  have hch : ∀ (ws' : List WEntry), (∀ i : Nat, (ws'[i]?).map (fun w : WEntry => (w.key, w.pgid)) =
        (r.ws[i]?).map (fun w : WEntry => (w.key, w.pgid))) → ws'.length = r.ws.length →
      (∀ i : Nat, entryBnd (bnd x) ws' i = entryBnd (bnd x) r.ws i) → r.nv.isLeaf' = false → r'.cs = r.cs →
      r'.nv.isLeaf' = r.nv.isLeaf' →
      (∀ (i : Nat) (w : WEntry) (c : Loc), ws'[i]? = some w → B'.nm !! w.pgid = some c → ∃ rc, B'.ns !! c = some rc ∧
        rc.nv.parent' = x ∧ rc.nv.pgid' = w.pgid ∧ rc.key = w.key ∧ rc.nv.key' ≠ slice.nil ∧
        c ∈ r'.cs ∧ kd x = (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) ∧
        bndIn (bnd c) (entryBnd (bnd x) ws' i)) ∧
      (∀ c ∈ r'.cs, ∃ (i : Nat) (w : WEntry), ws'[i]? = some w ∧ B'.nm !! w.pgid = some c) := by
    intro ws' hkp hlen hbe hlf hcs' hlf'
    obtain ⟨-, -, -, hnmc, hcsc⟩ := h10 hlf
    refine ⟨fun i w c hw hc => ?_, fun c hc => ?_⟩
    · have hm := hkp i
      rw [hw] at hm
      obtain ⟨w0, hw0, he⟩ := Option.map_eq_some_iff.1 hm.symm
      simp only [Prod.mk.injEq] at he
      rw [hnm, ← he.2] at hc
      obtain ⟨rc, hrc, hp, hpgc, hk, hkn, hcm, hkd, hb⟩ := hnmc i w0 c hw0 hc
      obtain ⟨rc', hrc', hdc⟩ := hkid c rc hcm hrc
      have hpos : 0 < rc.key.length := by rw [hk]; exact (h5 w0 (List.mem_of_getElem? hw0)).1
      obtain ⟨e1, e2, e3, e4, e5, -, -⟩ := child_keep rc rc' hdc hkn hpos
      refine ⟨rc', hrc', by rw [e1, hp], by rw [e2, hpgc, he.2], by rw [e3, hk, he.1], e4,
        by rw [hcs']; exact hcm, by rw [e5]; exact hkd, by rw [hbe]; exact hb⟩
    · rw [hcs'] at hc
      obtain ⟨i, w0, hw0, hc0⟩ := hcsc c hc
      have hm := hkp i
      rw [hw0] at hm
      obtain ⟨w, hw, he⟩ := Option.map_eq_some_iff.1 hm
      simp only [Prod.mk.injEq] at he
      exact ⟨i, w, hw, by rw [hnm, he.2]; exact hc0⟩
  rcases hd with rfl | ⟨⟨⟨hnv0, hws, hcs, hkey, hknil, hks, hil⟩, hkx⟩, hnv⟩
  · refine ⟨h1, h2, h3, h4, h5, h6, h7, by rw [hpg]; exact h8, h9, fun hlf => ?_⟩
    obtain ⟨a1, a2, a3, -, -⟩ := h10 hlf
    obtain ⟨b1, b2⟩ := hch r'.ws (fun _ => rfl) rfl (fun _ => rfl) hlf rfl rfl
    exact ⟨a1, a2, a3, b1, b2⟩
  · have e1 : r'.nv.bucket' = r.nv.bucket' := by rw [hnv]
    have e2 : r'.nv.spilled' = r.nv.spilled' := by rw [hnv]
    have e3 : r'.nv.pgid' = r.nv.pgid' := by rw [hnv]
    have e4 : r'.nv.isLeaf' = r.nv.isLeaf' := by rw [hnv]
    refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, hil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hws]; unfold wsSorted; rw [wKey_fresh, List.length_map]; exact h4
    · intro w hw; rw [hws] at hw
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      exact h5 w0 hw0
    · intro w hw; rw [hws] at hw
      obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
      exact ⟨by simp [ownFresh], by simp [ownFresh]⟩
    · by_cases hk' : r'.nv.key' = slice.nil
      · exact Or.inl hk'
      · right
        have hrk : r.nv.key' ≠ slice.nil := fun e => hk' (hknil e)
        rcases h7 with h7 | ⟨hpos, -⟩
        · exact absurd h7 hrk
        · exact ⟨by rw [hkey]; exact hpos, by rw [hks]; nofun⟩
    · rw [e3, hpg]; exact h8
    · intro hlf; rw [hcs]; exact h9 (by rw [← e4]; exact hlf)
    · intro hlf
      have hlf0 : r.nv.isLeaf' = false := by rw [← e4]; exact hlf
      obtain ⟨a1, a2, a3, -, -⟩ := h10 hlf0
      obtain ⟨b1, b2⟩ := hch r'.ws
        (fun i => by rw [hws, List.getElem?_map]; cases r.ws[i]? <;> rfl)
        (by rw [hws, List.length_map]) (fun i => by rw [hws, entryBnd_fresh]) hlf0 hcs e4
      refine ⟨by rw [hws, List.map_map]; exact a1, by rw [hws, List.length_map]; exact a2,
        by rw [hcs]; exact a3, b1, b2⟩


theorem lt_of_lt_notLt {a b c : List w8} (h1 : go.GoStringLt a b) (h2 : ¬ go.GoStringLt c b) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot b c with h | h | h
  · exact goStringLt_trans h1 h
  · subst h; exact h1
  · exact absurd h h2

theorem lt_of_notLt_lt' {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  rcases goStringLt_trichot a b with h | h | h
  · exact goStringLt_trans h h2
  · subst h; exact h2
  · exact absurd h h1

/-- The parts' entries in place of `w0`: still sorted. -/
theorem ws_sorted_mid (A C es : List WEntry) (w0 : WEntry)
    (h : (A ++ w0 :: C).Pairwise (fun a b => go.GoStringLt a.key b.key))
    (hes : es.Pairwise (fun a b => go.GoStringLt a.key b.key))
    (hlo : ∀ a ∈ A, ∀ e ∈ es, go.GoStringLt a.key e.key)
    (hhi : ∀ e ∈ es, ∀ c ∈ C, go.GoStringLt e.key c.key) :
    (A ++ es ++ C).Pairwise (fun a b => go.GoStringLt a.key b.key) := by
  rw [List.pairwise_append] at h
  obtain ⟨hA, hwC, hAw⟩ := h
  rw [List.pairwise_cons] at hwC
  obtain ⟨-, hC⟩ := hwC
  rw [List.append_assoc, List.pairwise_append, List.pairwise_append]
  refine ⟨hA, ⟨hes, hC, hhi⟩, fun a ha b hb => ?_⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact hlo a ha b hb
  · exact hAw a ha b (List.mem_cons_of_mem _ hb)

theorem nodup_mid {α : Type} (A C es : List α) (h : (A ++ C).Nodup) (hy : es.Nodup)
    (hd : ∀ y ∈ es, y ∉ A ++ C) : (A ++ es ++ C).Nodup := by
  have hp : (A ++ es ++ C).Perm (es ++ (A ++ C)) := by
    have := (List.perm_append_comm (l₁ := A) (l₂ := es)).append_right C
    simpa [List.append_assoc] using this
  rw [hp.nodup_iff, List.nodup_append]
  exact ⟨hy, h, fun a ha b hb e => hd a ha (e ▸ hb)⟩

theorem bndIn_widen (a : Option (List w8) × Option (List w8)) (lo : Option (List w8))
    (k k' : List w8) (h : bndIn a (lo, some k)) (hk : ¬ go.GoStringLt k' k) : bndIn a (lo, some k') := by
  refine ⟨h.1, fun y hy => ?_⟩
  cases hy
  obtain ⟨x, hx, hle⟩ := h.2 k rfl
  refine ⟨x, hx, fun hlt => ?_⟩
  rcases goStringLt_trichot k x with h1 | h1 | h1
  · exact hle h1
  · subst h1; exact hk hlt
  · exact hk (goStringLt_trans hlt h1)

/-- The keys of `A ++ es ++ C` around the replaced entry `i0` (`A = W.take i0`, `C = W.drop (i0 + 1)`). -/
theorem mid_len (W es : List WEntry) (i0 : Nat) (hi : i0 < W.length) :
    (W.take i0 ++ es ++ W.drop (i0 + 1)).length = W.length - 1 + es.length := by
  rw [List.length_append, List.length_append, List.length_take, List.length_drop]; omega

theorem mid_get_left (W es : List WEntry) (i0 j : Nat) (hi : i0 < W.length) (hj : j < i0) :
    (W.take i0 ++ es ++ W.drop (i0 + 1))[j]? = W[j]? := by
  have hl : j < (W.take i0).length := by rw [List.length_take]; omega
  rw [List.append_assoc, List.getElem?_append_left hl, List.getElem?_take, if_pos hj]

theorem mid_get_mid (W es : List WEntry) (i0 k : Nat) (hi : i0 < W.length) :
    (W.take i0 ++ es ++ W.drop (i0 + 1))[i0 + k]? = if k < es.length then es[k]? else W[i0 + 1 + (k - es.length)]? := by
  have hA : (W.take i0).length = i0 := by rw [List.length_take]; omega
  rw [List.append_assoc, List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left]
  by_cases hk : k < es.length
  · rw [if_pos hk, List.getElem?_append_left hk]
  · rw [if_neg hk, List.getElem?_append_right (by omega), List.getElem?_drop]

theorem wKey_mid_left' (W es : List WEntry) (i0 j : Nat) (hi : i0 < W.length) (hj : j < i0) :
    wKey (W.take i0 ++ es ++ W.drop (i0 + 1)) j = wKey W j := by
  unfold wKey; rw [mid_get_left W es i0 j hi hj]

/-- `treeOK` does not care for the order of a node's children. -/
theorem treeOK_perm_cs (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (ys : List Loc)
    (hT : treeOK bl B) (hn : B.ns !! n = some r) (hp : ys.Perm r.cs) :
    treeOK bl (setN B n { r with cs := ys }) := by
  obtain ⟨⟨rk, N, h1, h2, h3, h4⟩, ⟨r0, hr0, hp0⟩, hroot, hok⟩ := hT
  have hlk : ∀ l rl, (setN B n { r with cs := ys }).ns !! l = some rl →
      (l = n ∧ rl = { r with cs := ys }) ∨ (l ≠ n ∧ B.ns !! l = some rl) := by
    intro l rl h
    change (<[n := { r with cs := ys }]> B.ns) !! l = some rl at h
    by_cases e : l = n
    · subst e; rw [GMap.lookup_insert] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact Or.inr ⟨e, h⟩
  have hfw : ∀ l rl, B.ns !! l = some rl → ∃ rl', (setN B n { r with cs := ys }).ns !! l = some rl' ∧
      rl'.nv = rl.nv ∧ (∀ c, c ∈ rl'.cs ↔ c ∈ rl.cs) ∧ (rl'.cs.Nodup ↔ rl.cs.Nodup) := by
    intro l rl h
    by_cases e : l = n
    · subst e; rw [hn] at h; cases h
      exact ⟨_, GMap.lookup_insert _ _ _, rfl, fun c => hp.mem_iff, hp.nodup_iff⟩
    · refine ⟨rl, ?_, rfl, fun _ => Iff.rfl, Iff.rfl⟩
      change (<[n := { r with cs := ys }]> B.ns) !! l = some rl
      rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h
  have hbw : ∀ l rl', (setN B n { r with cs := ys }).ns !! l = some rl' → ∃ rl, B.ns !! l = some rl ∧
      rl'.nv = rl.nv ∧ (∀ c, c ∈ rl'.cs ↔ c ∈ rl.cs) ∧ (rl'.cs.Nodup ↔ rl.cs.Nodup) := by
    intro l rl' h
    rcases hlk l rl' h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
    · exact ⟨r, hn, rfl, fun c => hp.mem_iff, hp.nodup_iff⟩
    · exact ⟨rl', h', rfl, fun _ => Iff.rfl, Iff.rfl⟩
  refine ⟨⟨rk, N, fun l rl' hl => ?_, fun l rl' hl => ?_, fun l rl' hl hpar => ?_, fun l rl' hl => ?_⟩,
    ?_, fun l rl' hl hpar => ?_, fun l rl' hl => ?_⟩
  · obtain ⟨rl, hrl, hnv, -, -⟩ := hbw l rl' hl; rw [hnv]; exact h1 l rl hrl
  · obtain ⟨rl, hrl, -, hmem, hnd⟩ := hbw l rl' hl
    obtain ⟨hnd0, hc0⟩ := h2 l rl hrl
    refine ⟨hnd.2 hnd0, fun c hc => ?_⟩
    obtain ⟨rc, hrc, hpc⟩ := hc0 c ((hmem c).1 hc)
    obtain ⟨rc', hrc', hnv', -, -⟩ := hfw c rc hrc
    exact ⟨rc', hrc', by rw [hnv']; exact hpc⟩
  · obtain ⟨rl, hrl, hnv, -, -⟩ := hbw l rl' hl
    rw [hnv] at hpar ⊢
    obtain ⟨rp, hrp, hlp⟩ := h3 l rl hrl hpar
    obtain ⟨rp', hrp', -, hmem', -⟩ := hfw _ rp hrp
    exact ⟨rp', hrp', (hmem' l).2 hlp⟩
  · obtain ⟨rl, hrl, -, -, -⟩ := hbw l rl' hl; exact h4 l rl hrl
  · obtain ⟨r0', hr0', hnv0, -, -⟩ := hfw _ r0 hr0
    exact ⟨r0', hr0', by rw [hnv0]; exact hp0⟩
  · obtain ⟨rl, hrl, hnv, -, -⟩ := hbw l rl' hl
    rw [hnv] at hpar; exact hroot l rl hrl hpar
  · rcases hlk l rl' hl with ⟨-, rfl⟩ | ⟨-, h'⟩
    · obtain ⟨o1, o2, o3, o4⟩ := hok n r hn
      exact ⟨o1, o2, o3, o4⟩
    · exact hok l rl' h'

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The children loop's invariant (see the module doc): the state at its start `W0`, `T0`, `B0`,
`r0`, `K0`, `n`'s tree `S0`; now `W`, `T`, `B`, `rn`, `K`, at the child `i`. -/
def loopP (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n : Loc) (txl : Loc) (txid : w64)
    (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec) (K0 : Loc → Bool) (S0 : List Loc)
    (W : WView) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec)
    (rn : NRec) (i : Nat) (sp : Loc → Bool) (sub : Loc → List Loc) : Prop :=
  spillG (hG := hG) W txl txid T ρ F ∧ T.bs !! bl = some B ∧ B.ns !! n = some rn ∧ K n = false ∧
  spillFrame T0 T (· = bl) ∧ W.pages = W0.pages ∧ W.ps = W0.ps ∧ spillPages W0 T0 ⊆ spillPages W T ∧
  B.bv = B0.bv ∧ B.ib = B0.ib ∧ B.nm = B0.nm ∧ B.bm = B0.bm ∧
  rn.nv = ({ r0.nv with inodes' := rn.nv.inodes', children' := rn.nv.children', key' := rn.nv.key' } : node) ∧
  rn.key = r0.key ∧
  (r0.nv.key' = slice.nil → rn.nv.key' = slice.nil) ∧
  (rn.ksrc = r0.ksrc ∨ rn.ksrc = Src.own (DFrac.own 1)) ∧
  nodeL W bl B bnd kd n rn ∧ nodesOK W T B ∧
  (∀ l r, B.ns !! l = some r → l ≠ n → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) ∧
  i ≤ rn.cs.length ∧ rn.cs.Nodup ∧ n ∉ rn.cs ∧
  (∀ j c, j < i → rn.cs[j]? = some c → spilledN bl B c) ∧
  (∀ c ∈ rn.cs.drop i, kidsTree B.ns c (sub c) ∧ (sp c = true → spilledN bl B c) ∧
    (sp c = false → (sub c).length < N ∧ subU W bl B bnd kd K c (sub c))) ∧
  (n :: ((rn.cs.drop i).map sub).flatten).Nodup ∧
  (∀ x ∈ ((rn.cs.drop i).map sub).flatten, x ∈ S0 ∨ x ∈ rn.cs) ∧
  (∀ c ∈ rn.cs.drop i, sp c = false → ∀ x ∈ sub c, x ∈ S0) ∧
  (∀ x rx, x ∉ S0 → B0.ns !! x = some rx → ∃ rx', B.ns !! x = some rx' ∧ dnK rx rx') ∧
  (∀ x, (B.ns !! x).isSome → (B0.ns !! x).isSome ∨ x ∈ rn.cs) ∧
  (∀ x ∈ S0, (B.ns !! x).isSome → x = n ∨ x ∈ rn.cs ∨ x ∈ ((rn.cs.drop i).map sub).flatten) ∧
  kKeep T bl B0 S0 K0 K ∧ (treeOK bl B0 → treeOK bl B) ∧ (nodeHts B0 ht → nodeHts B ht) ∧
  (∀ x ∈ rn.cs, x ∈ S0 ∨ B0.ns !! x = none) ∧
  (r0.nv.key' ≠ slice.nil → 0 < r0.key.length → rn.nv.key' ≠ slice.nil)

/-- The tokens of the trees of the unspilled children `cs`. -/
def subToks (γ : GName) (P : GMap Nat (List w8)) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (cs : List Loc) : IProp GF :=
  [∗list] c ∈ cs, (if sp c then emp else
    [∗list] l ∈ sub c, iprop(∃ rl, ⌜B.ns !! l = some rl⌝ ∗ rtoks γ P B (bnd l) (kd l) (ht l - 1) rl))

theorem kidsTree_leaf (ns : GMap Loc NRec) (c : Loc) (rc : NRec) (h : ns !! c = some rc)
    (hc : rc.cs = []) : kidsTree ns c [c] := by
  have := kidsTree.mk c rc [] h (by rw [hc]; exact List.Forall₂.nil) (by simp)
  simpa using this


theorem mem_drop_of_get {α : Type} (cs : List α) (i : Nat) (c : α) (hc : cs[i]? = some c) :
    c ∈ cs.drop i := by
  have hl : i < cs.length := (List.getElem?_eq_some_iff.1 hc).1
  rw [List.mem_iff_getElem?]
  exact ⟨0, by rw [List.getElem?_drop]; simpa using hc⟩

theorem mem_drop_succ {α : Type} (cs : List α) (i : Nat) (x : α) (h : x ∈ cs.drop (i + 1)) :
    x ∈ cs.drop i :=
  ((List.drop_sublist_drop_left cs) (Nat.le_succ i)).subset h

/-- The child `i`: spilled or with its tree. -/
theorem loop_child (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (c : Loc)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hc : rn.cs[i]? = some c) (hsp : sp c = true) : spilledN bl B c :=
  (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c (mem_drop_of_get _ _ _ hc)).2.1 hsp

/-- The loop's end: every child spilled, no tree left to hold. -/
theorem loop_exit (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hi : rn.cs.length ≤ i) : (∀ c ∈ rn.cs, spilledN bl B c) ∧ rn.cs.drop i = [] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hi', -, -, hlt, -⟩ := h
  refine ⟨fun c hc => ?_, List.drop_eq_nil_of_le hi⟩
  obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hc
  exact hlt j c (by omega) (by rw [List.getElem?_eq_getElem hj, hjc])

/-- A spilled child: the next iteration, nothing changed. -/
theorem loop_done (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (c : Loc)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hc : rn.cs[i]? = some c) (hsp : sp c = true) :
    loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn (i + 1) sp sub := by
  obtain ⟨hg, hB, hn, hK, hfr, hpgs, hps, hsp', hbv, hib, hnm, hbm, hnv, hkey, hknil, hks, hL, hok,
    hP1, hi, hnd, hnc, hlt, hdr, hfnd, hfsub, hsS, hout, hdom, hrem, hkk⟩ := h
  have hil : i < rn.cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hd := drop_cons_of_get rn.cs i c hc
  obtain ⟨hkt, hspc, -⟩ := hdr c (by rw [hd]; exact List.mem_cons_self)
  have hsc : spilledN bl B c := hspc hsp
  have hsubc : sub c = [c] := by
    obtain ⟨rc, hrc, -, hcs, -⟩ := hsc
    exact kidsTree_det B.ns _ c (sub c) [c] (Nat.le_refl _) hkt (kidsTree_leaf B.ns c rc hrc hcs)
  refine ⟨hg, hB, hn, hK, hfr, hpgs, hps, hsp', hbv, hib, hnm, hbm, hnv, hkey, hknil, hks, hL, hok,
    hP1, by omega, hnd, hnc, ?_, ?_, ?_, ?_, ?_, hout, hdom, ?_, hkk⟩
  · intro j x hj hx
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hlt j x hj hx
    · rw [hc] at hx; cases hx; exact hsc
  · intro x hx; exact hdr x (by rw [hd]; exact List.mem_cons_of_mem _ hx)
  · rw [hd] at hfnd
    simp only [List.map_cons, List.flatten_cons] at hfnd
    exact hfnd.sublist (List.cons_sublist_cons.2 (List.sublist_append_right _ _))
  · intro x hx
    apply hfsub
    rw [hd]; simp only [List.map_cons, List.flatten_cons]; exact List.mem_append_right _ hx
  · intro x hx; exact hsS x (by rw [hd]; exact List.mem_cons_of_mem _ hx)
  · intro x hx hxs
    rcases hrem x hx hxs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [hd] at h
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at h
      rcases h with h | h
      · rw [hsubc, List.mem_singleton] at h
        subst h; exact Or.inr (Or.inl (List.mem_of_getElem? hc))
      · exact Or.inr (Or.inr h)

theorem subToks_done (γ : GName) (P : GMap Nat (List w8)) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (cs : List Loc) (i : Nat) (c : Loc) (hc : cs[i]? = some c)
    (hsp : sp c = true) :
    subToks (GF := GF) γ P B bnd kd ht sp sub (cs.drop i) ⊢ subToks γ P B bnd kd ht sp sub (cs.drop (i + 1)) := by
  unfold subToks
  rw [drop_cons_of_get cs i c hc]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨-, H⟩
  iexact H

/-- An unspilled child: the premises of its spill. -/
theorem loop_sub_pre (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (c : Loc)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hc : rn.cs[i]? = some c) (hsp : sp c = false) (hnn : n ≠ null)
    (hpg : r0.nv.isLeaf' = false → r0.nv.pgid' ≠ W64 0) :
    ∃ rc, B.ns !! c = some rc ∧ (sub c).length < N ∧ subU W bl B bnd kd K c (sub c) ∧
      rc.nv.parent' = n ∧ n ∉ sub c ∧ rn.nv.isLeaf' = false ∧ rn.nv.pgid' ≠ W64 0 ∧
      (∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) := by
  obtain ⟨hg, hB, hn, hK, hfr, hpgs, hps, hsp', hbv, hib, hnm, hbm, hnv, hkey, hknil, hks, hL, hok,
    hP1, hi, hnd, hnc, hlt, hdr, hfnd, hfsub, hsS, hout, hdom, hrem, hkk⟩ := h
  have hd := drop_cons_of_get rn.cs i c hc
  obtain ⟨hkt, -, hus⟩ := hdr c (by rw [hd]; exact List.mem_cons_self)
  obtain ⟨hlen, hsu⟩ := hus hsp
  obtain ⟨rc, hrc, hU⟩ := (hsu.2 c (kidsTree_head B.ns c (sub c) hkt)).2
  have hcm : c ∈ rn.cs := List.mem_of_getElem? hc
  have hleaf : rn.nv.isLeaf' = false := by
    cases hlf : rn.nv.isLeaf'
    · rfl
    · have := hL.2.2.2.2.2.2.2.2.1 hlf; rw [this] at hcm; cases hcm
  obtain ⟨-, -, -, hnmc, hcs⟩ := hL.2.2.2.2.2.2.2.2.2 hleaf
  have hpar : rc.nv.parent' = n := by
    rcases hcs c hcm with ⟨j, w, hw, hwc⟩ | hsp2
    · obtain ⟨rc', hrc', hp', -⟩ := hnmc j w c hw hwc
      rw [hrc] at hrc'; cases hrc'; exact hp'
    · obtain ⟨rc', hrc', hs', -⟩ := hsp2
      rw [hrc] at hrc'; cases hrc'; rw [hU.2.1] at hs'; cases hs'
  have hnS : n ∉ sub c := by
    intro hm
    rw [hd] at hfnd
    simp only [List.map_cons, List.flatten_cons] at hfnd
    exact (List.nodup_cons.1 hfnd).1 (List.mem_append_left _ hm)
  have hpgn : rn.nv.pgid' ≠ W64 0 := by
    have e1 : rn.nv.pgid' = r0.nv.pgid' := by rw [hnv]
    have e2 : rn.nv.isLeaf' = r0.nv.isLeaf' := by rw [hnv]
    rw [e1]; exact hpg (by rw [← e2]; exact hleaf)
  refine ⟨rc, hrc, hlen, hsu, hpar, hnS, hleaf, hpgn, fun l r hl hlf => ?_⟩
  by_cases e : l = n
  · subst e; rw [hn] at hl; cases hl; exact hpgn
  · exact hP1 l r hl e hlf

/-- What the loop keeps of the node `n` and the bucket. -/
theorem loopP_facts (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub) :
    spillG (hG := hG) W txl txid T ρ F ∧ T.bs !! bl = some B ∧ B.ns !! n = some rn ∧
      K n = false ∧ B.bv = B0.bv ∧ W.ps = W0.ps ∧ nodeL W bl B bnd kd n rn ∧ nodesOK W T B ∧
      rn.nv.parent' = r0.nv.parent' ∧ rn.nv.isLeaf' = r0.nv.isLeaf' ∧
      rn.nv.pgid' = r0.nv.pgid' := by
  obtain ⟨hg, hB, hn, hK, hfr, hpgs, hps, hsp', hbv, hib, hnm, hbm, hnv, hkey, hknil, hks, hL, hok,
    hP1, hi, hnd, hnc, hlt, hdr, hfnd, hfsub, hsS, hout, hdom, hrem, hkk⟩ := h
  refine ⟨hg, hB, hn, hK, hbv, hps, hL, hok, ?_, ?_, ?_⟩ <;> rw [hnv]

/-- The loop keeps the bucket's tree. -/
theorem loopP_tree (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hT0 : treeOK bl B0) (hH0 : nodeHts B0 ht) : treeOK bl B ∧ nodeHts B ht := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h1, h2, -⟩ := h
  exact ⟨h1 hT0, h2 hH0⟩

theorem subToks_sub (γ : GName) (P : GMap Nat (List w8)) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (cs : List Loc) (i : Nat) (c : Loc) (hc : cs[i]? = some c)
    (hsp : sp c = false) :
    subToks (GF := GF) γ P B bnd kd ht sp sub (cs.drop i) ⊢
      ([∗list] l ∈ sub c, ∃ rl, ⌜B.ns !! l = some rl⌝ ∗ rtoks γ P B (bnd l) (kd l) (ht l - 1) rl) ∗
      subToks γ P B bnd kd ht sp sub (cs.drop (i + 1)) := by
  unfold subToks
  rw [drop_cons_of_get cs i c hc]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hc, H⟩
  rw [hsp]
  simp only [Bool.false_eq_true, ite_false]
  iframe

theorem subPostP_tree {W : WView} {txl : Loc} {txid : w64} {T : WTx} {bl : Loc} {B : BRec}
    {bnd : Loc → Option (List w8) × Option (List w8)} {S : List Loc} {n : Loc} {r : NRec}
    {pl : Loc} {rp : NRec} {K : Loc → Bool} {W' : WView} {T' : WTx} {ρ' : DBState}
    {F' : GMap Nat (List w8)} {K' : Loc → Bool} {B' : BRec} {ps : List (w64 × List w8)}
    {xs : List Loc} {rp' : NRec}
    (h : node.spill.subPostP (hG := hG) W txl txid T bl B bnd S n r pl rp K W' T' ρ' F' K' B' ps xs rp') :
    treeOK bl B' := by
  unfold node.spill.subPostP at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wbktQP_mono (γ : GName) (P P' : GMap Nat (List w8)) (hP : P ⊆ P') (v : List w8) :
    wbktQP (GF := GF) γ P v ⊢ wbktQP γ P' v := by
  unfold wbktQP
  iintro ⟨%h, H⟩
  isplitr
  · ipureintro; exact h
  by_cases hr : inBucketRoot v = 0
  · rw [if_pos hr, if_pos hr]; iexact H
  · rw [if_neg hr, if_neg hr]
    icases H with ⟨%Q, %hQ, H⟩
    iexists Q
    isplitr
    · ipureintro; exact GMap.map_subseteq_trans hQ hP
    iexact H

/-- An entry's resources, moved to more pages, another list (the same entry's fields, a wider
bound). -/
theorem entRes_move (γ : GName) (P P' : GMap Nat (List w8)) (B B' : BRec) (hP : P ⊆ P')
    (hnm : B'.nm = B.nm) (hi hi' : Option (List w8)) (leaf : Bool) (kind ch : Nat)
    (ws ws' : List WEntry) (j j' : Nat) (w w' : WEntry)
    (hf : w'.flags = w.flags) (hv : w'.value = w.value) (hpg : w'.pgid = w.pgid) (hk : w'.key = w.key)
    (hH : ∀ H, hiLe H (childHi hi (wKey ws) ws.length j) → hiLe H (childHi hi' (wKey ws') ws'.length j')) :
    entRes (GF := GF) γ P B hi leaf kind ch ws j w ⊢ entRes γ P' B' hi' leaf kind ch ws' j' w' := by
  unfold entRes
  rw [hf, hv, hpg, hk, hnm]
  cases leaf
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hn : B.nm !! w.pgid = none
    · rw [if_pos hn, if_pos hn]
      iintro ⟨%Q, %cpg, %H, %hc, Ht⟩
      iexists Q, cpg, H
      isplitr
      · ipureintro
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
        exact ⟨GMap.map_subseteq_trans h1 hP, h2, h3, h4, h5, hH H h6, h7⟩
      iexact Ht
    · rw [if_neg hn, if_neg hn]
  · simp only [ite_true]
    by_cases hb : w.flags &&& W32 1 = W32 0
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]; exact wbktQP_mono γ P P' hP w.value

theorem hiLe_refl_imp (hi : Option (List w8)) : ∀ H, hiLe H hi → hiLe H hi := fun _ h => h

/-- A node's tokens, kept by a dereference, over more pages. -/
theorem rtoks_move (γ : GName) (P P' : GMap Nat (List w8)) (B B' : BRec) (hP : P ⊆ P')
    (hnm : B'.nm = B.nm) (b : Option (List w8) × Option (List w8)) (kind ch : Nat) (r r' : NRec)
    (hd : r' = r ∨ derefNodeK r r') :
    rtoks (GF := GF) γ P B b kind ch r ⊢ rtoks γ P' B' b kind ch r' := by
  have hnv : r'.nv.pgid' = r.nv.pgid' ∧ r'.nv.isLeaf' = r.nv.isLeaf' := by
    rcases hd with rfl | ⟨-, h⟩
    · exact ⟨rfl, rfl⟩
    · rw [h]; exact ⟨rfl, rfl⟩
  have hws : r'.ws = r.ws ∨ r'.ws = r.ws.map ownFresh := by
    rcases hd with rfl | ⟨⟨⟨-, h, -⟩, -⟩, -⟩
    · exact Or.inl rfl
    · exact Or.inr h
  unfold rtoks
  rw [hnv.1, hnv.2]
  refine sep_mono .rfl ?_
  rcases hws with h | h
  · rw [h]
    exact BigSepL.bigSepL_mono_of_forall (fun {k w} =>
      entRes_move γ P P' B B' hP hnm b.2 b.2 _ kind ch r.ws r.ws k k w w rfl rfl rfl rfl (fun _ h => h))
  · rw [h, BigSepL.bigSepL_map]
    refine BigSepL.bigSepL_mono_of_forall (fun {k w} => entRes_move γ P P' B B' hP hnm b.2 b.2 _ kind ch r.ws
      (r.ws.map ownFresh) k k w (ownFresh w) rfl rfl rfl rfl ?_)
    intro H hH
    rw [wKey_fresh, List.length_map]; exact hH


theorem kidsTree_some (ns : GMap Loc NRec) (t : Loc) (S : List Loc) (h : kidsTree ns t S) :
    (ns !! t).isSome := by
  cases h with
  | mk _ r _ hr _ _ => rw [hr]; rfl

theorem notLt_trans' {a b c : List w8} (h1 : ¬ go.GoStringLt a b) (h2 : ¬ go.GoStringLt b c) :
    ¬ go.GoStringLt a c := by
  intro hac
  rcases goStringLt_trichot a b with h | h | h
  · exact h1 h
  · subst h; exact h2 hac
  · exact h2 (goStringLt_trans h hac)

/-- The keys of the entries `A ++ es ++ C`. -/
theorem wKey_mid_left (A es C : List WEntry) (k : Nat) (hk : k < A.length) :
    wKey (A ++ es ++ C) k = wKey A k := by
  unfold wKey; rw [List.append_assoc, List.getElem?_append_left hk]

theorem wKey_mid_es (A es C : List WEntry) (k : Nat) (hk : k < es.length) :
    wKey (A ++ es ++ C) (A.length + k) = wKey es k := by
  unfold wKey
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

theorem wKey_mid_right (A es C : List WEntry) (k : Nat) :
    wKey (A ++ es ++ C) (A.length + es.length + k) = wKey C k := by
  unfold wKey
  rw [List.getElem?_append_right (by rw [List.length_append]; omega), List.length_append,
    Nat.add_sub_cancel_left]

theorem bigSepL_forall2 {α β : Type} (R : α → β → Prop) (Φ : Nat → α → IProp GF) (Ψ : Nat → β → IProp GF) :
    ∀ (ps : List α) (es : List β), List.Forall₂ R ps es →
      (∀ k p e, ps[k]? = some p → es[k]? = some e → R p e → Φ k p ⊢ Ψ k e) →
      ([∗list] k ↦ p ∈ ps, Φ k p) ⊢ [∗list] k ↦ e ∈ es, Ψ k e
  | [], [], _, _ => .rfl
  | p :: ps, e :: es, .cons hr hrs, h => by
    refine BigSepL.bigSepL_cons.1.trans (BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2)
    exact sep_mono (h 0 p e rfl rfl hr)
      (bigSepL_forall2 R (fun k => Φ (k + 1)) (fun k => Ψ (k + 1)) ps es hrs
        (fun k p' e' h1 h2 h3 => h (k + 1) p' e' h1 h2 h3))

theorem forall2_get' {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), List.Forall₂ R l1 l2 → ∀ (k : Nat) (a : α), l1[k]? = some a →
      ∃ b, l2[k]? = some b ∧ R a b
  | [], [], _, _, _, h => by simp at h
  | a :: l1, b :: l2, .cons hr hrs, 0, a', h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨b, rfl, hr⟩
  | a :: l1, b :: l2, .cons _ hrs, k + 1, a', h => by
    simp only [List.getElem?_cons_succ] at h ⊢; exact forall2_get' R l1 l2 hrs k a' h

theorem forall2_get_r {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), List.Forall₂ R l1 l2 → ∀ (k : Nat) (b : β), l2[k]? = some b →
      ∃ a, l1[k]? = some a ∧ R a b
  | [], [], _, _, _, h => by simp at h
  | a :: l1, b :: l2, .cons hr hrs, 0, b', h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨a, rfl, hr⟩
  | a :: l1, b :: l2, .cons _ hrs, k + 1, b', h => by
    simp only [List.getElem?_cons_succ] at h ⊢; exact forall2_get_r R l1 l2 hrs k b' h

theorem wKey_take (W : List WEntry) (i0 k : Nat) (hk : k < i0) : wKey (W.take i0) k = wKey W k := by
  unfold wKey; rw [List.getElem?_take, if_pos hk]

theorem wKey_drop (W : List WEntry) (n k : Nat) : wKey (W.drop n) k = wKey W (n + k) := by
  unfold wKey; rw [List.getElem?_drop]

/-- The entries' resources after the part's pieces replace its entry `i0`. -/
theorem ents_post (γ : GName) (P P' : GMap Nat (List w8)) (B B' : BRec) (hP : P ⊆ P')
    (hnm : B'.nm = B.nm) (hi : Option (List w8)) (kind ch : Nat) (W : List WEntry) (i0 : Nat)
    (w0 : WEntry) (es : List WEntry) (ps : List (w64 × List w8)) (c : Loc) (hic : Option (List w8))
    (hw0 : W[i0]? = some w0) (hw0c : B.nm !! w0.pgid = some c) (hes : pieceEntries ps es)
    (hne : ps ≠ []) (hfr : ∀ p ∈ ps, B.nm !! p.1 = none)
    (hA1 : ∀ p, ps[0]? = some p → 0 < i0 → ¬ go.GoStringLt p.2 (wKey W i0))
    (hA2 : hiLe hic (childHi hi (wKey W) W.length i0)) :
    ([∗list] k ↦ x ∈ W, entRes (GF := GF) γ P B hi false kind ch W k x) ∗ pieceRes γ P' kind ch ps hic ⊢
      [∗list] k ↦ x ∈ W.take i0 ++ es ++ W.drop (i0 + 1),
        entRes γ P' B' hi false kind ch (W.take i0 ++ es ++ W.drop (i0 + 1)) k x := by
  have hi0 : i0 < W.length := (List.getElem?_eq_some_iff.1 hw0).1
  have hm : es.length = ps.length := hes.length_eq.symm
  have hmpos : 0 < ps.length := List.length_pos_iff.2 hne
  have hA : (W.take i0).length = i0 := by rw [List.length_take]; omega
  have hLl : (W.take i0 ++ es ++ W.drop (i0 + 1)).length = i0 + ps.length + (W.length - (i0 + 1)) := by
    rw [List.length_append, List.length_append, hA, hm, List.length_drop]
  have hWs : W = W.take i0 ++ w0 :: W.drop (i0 + 1) := by
    rw [← drop_cons_of_get W i0 w0 hw0, List.take_append_drop]
  have hwes : ∀ (k : Nat) (p : w64 × List w8), ps[k]? = some p → wKey es k = p.2 := by
    intro k p hp
    obtain ⟨e, he, -, -, h3, -⟩ := forall2_get' _ ps es hes k p hp
    unfold wKey; rw [he]; exact h3
  iintro ⟨Hs, Hps⟩
  ihave Hs := (BiEntails.of_eq (congrArg (fun l => [∗list] k ↦ x ∈ l, entRes (GF := GF) γ P B hi false kind ch W k x)
    hWs)).1 $$ Hs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨HA, HwC⟩
  icases BigSepL.bigSepL_cons.1 $$ HwC with ⟨-, HC⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [HA Hps]
  · iapply BigSepL.bigSepL_append.2
    isplitl [HA]
    · iapply (BigSepL.bigSepL_mono ?_) $$ HA
      intro k x hx
      have hk : k < i0 := by have := (List.getElem?_eq_some_iff.1 hx).1; rw [hA] at this; exact this
      apply entRes_move γ P P' B B' hP hnm hi hi false kind ch _ _ k k x x rfl rfl rfl rfl
      intro H hH
      unfold childHi at hH ⊢
      rw [hLl]
      by_cases hk1 : k + 1 < i0
      · rw [if_pos (by omega)] at hH
        rw [if_pos (by omega), wKey_mid_left _ _ _ _ (by rw [hA]; exact hk1), wKey_take W i0 _ hk1]
        exact hH
      · have hk1' : k + 1 = i0 := by omega
        rw [if_pos (by omega)] at hH
        rw [if_pos (by omega)]
        obtain ⟨p0, hp0⟩ : ∃ p0, ps[0]? = some p0 := ⟨_, List.getElem?_eq_getElem hmpos⟩
        have e1 : wKey (W.take i0 ++ es ++ W.drop (i0 + 1)) (k + 1) = p0.2 := by
          have h0 := wKey_mid_es (W.take i0) es (W.drop (i0 + 1)) 0 (by omega)
          rw [hA] at h0; simp only [Nat.add_zero] at h0
          rw [hk1', h0]
          exact hwes 0 p0 hp0
        rw [e1]
        intro h' hh'
        cases hh'
        obtain ⟨h'', hH'', hle⟩ := hH (wKey W (k + 1)) rfl
        refine ⟨h'', hH'', notLt_trans' ?_ hle⟩
        rw [hk1']; exact hA1 p0 hp0 (by omega)
    · rw [hA]
      unfold pieceRes
      iapply (bigSepL_forall2 _ _ _ ps es hes ?_) $$ Hps
      intro k p e hp he hr
      obtain ⟨-, hpg, hky, -, -, -⟩ := hr
      unfold entRes
      simp only [Bool.false_eq_true, ite_false]
      rw [hnm, hpg, if_pos (hfr p (List.mem_of_getElem? hp))]
      iintro ⟨%Q, %pg, %hq, Ht⟩
      iexists Q, pg, (pieceHi ps hic k)
      isplitr
      · ipureintro
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
        refine ⟨q1, q2, q3, q4, by rw [hky]; exact q5, ?_, q6⟩
        have hkm : k < ps.length := (List.getElem?_eq_some_iff.1 hp).1
        unfold pieceHi childHi
        rw [hLl]
        cases hp2 : ps[k + 1]? with
        | some p2 =>
          have hk2 : k + 1 < ps.length := (List.getElem?_eq_some_iff.1 hp2).1
          rw [if_pos (by omega)]
          have e2 : wKey (W.take i0 ++ es ++ W.drop (i0 + 1)) (k + i0 + 1) = p2.2 := by
            rw [show k + i0 + 1 = (W.take i0).length + (k + 1) by rw [hA]; omega,
              wKey_mid_es _ _ _ _ (by omega)]
            exact hwes (k + 1) p2 hp2
          rw [e2]
          intro h' hh'; cases hh'
          exact ⟨p2.2, rfl, goStringLt_irrefl_w _⟩
        | none =>
          have hk2 : k + 1 = ps.length := by
            have := List.getElem?_eq_none_iff.1 hp2; omega
          unfold childHi at hA2
          by_cases hc1 : i0 + 1 < W.length
          · rw [if_pos hc1] at hA2
            rw [if_pos (by omega)]
            have e3 : wKey (W.take i0 ++ es ++ W.drop (i0 + 1)) (k + i0 + 1) = wKey W (i0 + 1) := by
              rw [show k + i0 + 1 = (W.take i0).length + es.length + 0 by rw [hA, hm]; omega,
                wKey_mid_right, wKey_drop]
            rw [e3]; exact hA2
          · rw [if_neg hc1] at hA2
            rw [if_neg (by omega)]
            exact hA2
      rw [hky]
      iexact Ht
  · rw [List.length_append, hA, hm]
    iapply (BigSepL.bigSepL_mono ?_) $$ HC
    intro k x hx
    have hkx : i0 + 1 + k < W.length := by
      have := (List.getElem?_eq_some_iff.1 hx).1; rw [List.length_drop] at this; omega
    apply entRes_move γ P P' B B' hP hnm hi hi false kind ch _ _ _ _ x x rfl rfl rfl rfl
    intro H hH
    unfold childHi at hH ⊢
    rw [hLl]
    by_cases hc2 : k + 1 + i0 + 1 < W.length
    · rw [if_pos hc2] at hH
      rw [if_pos (by omega)]
      have e4 : wKey (W.take i0 ++ es ++ W.drop (i0 + 1)) (k + (i0 + ps.length) + 1) =
          wKey W (k + 1 + i0 + 1) := by
        rw [show k + (i0 + ps.length) + 1 = (W.take i0).length + es.length + (k + 1) by rw [hA, hm]; omega,
          wKey_mid_right, wKey_drop]
        congr 1; omega
      rw [e4]; exact hH
    · rw [if_neg hc2] at hH
      rw [if_neg (by omega)]
      exact hH


theorem ents_fresh (γ : GName) (P : GMap Nat (List w8)) (B : BRec) (hi : Option (List w8)) (leaf : Bool)
    (kind ch : Nat) (ws : List WEntry) :
    ([∗list] k ↦ w ∈ ws, entRes (GF := GF) γ P B hi leaf kind ch ws k w) ⊣⊢
      [∗list] k ↦ w ∈ ws.map ownFresh, entRes γ P B hi leaf kind ch (ws.map ownFresh) k w := by
  rw [BigSepL.bigSepL_map]
  constructor
  · exact BigSepL.bigSepL_mono_of_forall (fun {k w} => entRes_move γ P P B B (GMap.map_subseteq_refl _) rfl
      hi hi leaf kind ch ws _ k k w (ownFresh w) rfl rfl rfl rfl
      (fun H h => by rw [wKey_fresh, List.length_map]; exact h))
  · exact BigSepL.bigSepL_mono_of_forall (fun {k w} => entRes_move γ P P B B (GMap.map_subseteq_refl _) rfl
      hi hi leaf kind ch _ ws k k (ownFresh w) w rfl rfl rfl rfl
      (fun H h => by rw [wKey_fresh, List.length_map] at h; exact h))

/-- A tree's members are nodes, and hold their children. -/
theorem kidsTree_mem (ns : GMap Loc NRec) :
    ∀ (N : Nat) (t : Loc) (S : List Loc), S.length ≤ N → kidsTree ns t S →
      ∀ x ∈ S, ∃ rx, ns !! x = some rx ∧ ∀ c ∈ rx.cs, c ∈ S := by
  intro N
  induction N with
  | zero =>
    intro t S hl hk
    cases hk with
    | mk _ _ _ _ _ _ => simp at hl
  | succ N ih =>
    intro t S hl hk x hx
    cases hk with
    | mk _ r subs hr hF hnd =>
      have key : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
          ss.flatten.length ≤ N → (∀ c ∈ cs, c ∈ t :: subs.flatten) →
          (∀ y ∈ ss.flatten, y ∈ subs.flatten) →
          ∀ y ∈ ss.flatten, ∃ ry, ns !! y = some ry ∧ ∀ c ∈ ry.cs, c ∈ t :: subs.flatten := by
        intro cs ss hF2
        induction hF2 with
        | nil => intro _ _ _ y h; simp at h
        | @cons c s cs' ss' hk2 _ ih2 =>
          intro hlen hcs hsub y hy
          simp only [List.flatten_cons, List.length_append, List.mem_append] at hlen hy
          rcases hy with hy | hy
          · obtain ⟨ry, hry, hc⟩ := ih c s (by omega) hk2 y hy
            refine ⟨ry, hry, fun c' hc' => List.mem_cons_of_mem _ (hsub c' ?_)⟩
            simp only [List.flatten_cons, List.mem_append]; exact Or.inl (hc c' hc')
          · exact ih2 (by omega) (fun c' h => hcs c' (List.mem_cons_of_mem _ h))
              (fun z hz => hsub z (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hz)) y hy
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨r, hr, fun c hc => ?_⟩
        obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem hc
        obtain ⟨s, hs, hcs⟩ := forall2_get' _ r.cs subs hF k c (by rw [← hkc]; exact List.getElem?_eq_getElem hk)
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, List.mem_of_getElem? hs, kidsTree_head ns c s hcs⟩)
      · exact key r.cs subs hF (by simp only [List.length_cons] at hl; omega) (fun c h => by
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
          obtain ⟨s, hs, hcs⟩ := forall2_get' _ r.cs subs hF k _ (List.getElem?_eq_getElem hk)
          exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, List.mem_of_getElem? hs, kidsTree_head ns _ s hcs⟩))
          (fun y h => h) x hx

theorem nodup_map_idx {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup) (a b : Nat)
    (x y : α) (hx : l[a]? = some x) (hy : l[b]? = some y) (he : f x = f y) : a = b := by
  have ha : a < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have hb : b < l.length := (List.getElem?_eq_some_iff.1 hy).1
  have h1 : (l.map f)[a]? = some (f x) := by rw [List.getElem?_map, hx]; rfl
  have h2 : (l.map f)[b]? = some (f y) := by rw [List.getElem?_map, hy]; rfl
  have hp := List.pairwise_iff_getElem.1 h
  have hla : a < (l.map f).length := by simpa using ha
  have hlb : b < (l.map f).length := by simpa using hb
  rw [List.getElem?_eq_getElem hla] at h1
  rw [List.getElem?_eq_getElem hlb] at h2
  simp only [Option.some.injEq] at h1 h2
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd (by rw [h1, h2, he]) (hp a b hla hlb hab)
  · exact hab
  · exact absurd (by rw [h1, h2, he]) (hp b a hlb hla hab)

theorem forall2_map_eq {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ (l1 : List α) (l2 : List β), List.Forall₂ (fun a b => f a = g b) l1 l2 → l1.map f = l2.map g
  | [], [], .nil => rfl
  | _ :: l1, _ :: l2, .cons h hs => by simp only [List.map_cons, h, forall2_map_eq f g l1 l2 hs]

theorem es_pairwise (ps : List (w64 × List w8)) (es : List WEntry) (hes : pieceEntries ps es)
    (hsort : ∀ (j k : Nat) (a b : w64 × List w8), j < k → ps[j]? = some a → ps[k]? = some b →
      go.GoStringLt a.2 b.2) :
    es.Pairwise (fun a b => go.GoStringLt a.key b.key) := by
  rw [List.pairwise_iff_getElem]
  intro j k hj hk hjk
  obtain ⟨a, ha, -, -, hka, -⟩ := forall2_get_r _ ps es hes j es[j] (List.getElem?_eq_getElem hj)
  obtain ⟨b, hb, -, -, hkb, -⟩ := forall2_get_r _ ps es hes k es[k] (List.getElem?_eq_getElem hk)
  rw [hka, hkb]; exact hsort j k a b hjk ha hb










/-- An unspilled child spilled: the next iteration. -/
theorem loop_sub_post (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec) (r0 : NRec)
    (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (c : Loc) (rc : NRec)
    (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)) (K' : Loc → Bool) (B' : BRec)
    (ps : List (w64 × List w8)) (xs : List Loc) (rn' : NRec)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hc : rn.cs[i]? = some c) (hsp : sp c = false) (hrc : B.ns !! c = some rc)
    (hp : node.spill.subPostP (hG := hG) W txl txid T bl B bnd (sub c) c rc n rn K W' T' ρ' F' K' B'
      ps xs rn') (hnS : n ∈ S0) (hT0 : treeOK bl B0) (hH0 : nodeHts B0 ht) :
    loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W' T' ρ' F' K' B' rn' (i + 1)
      (fun x => if x ∈ xs then true else sp x) (fun x => if x ∈ xs then [x] else sub x) := by
  obtain ⟨hg, hB, hn, hK, hfr, hpgs, hps, hsp', hbv, hib, hnm, hbm, hnv, hkey, hknil, hks, hL, hok,
    hP1, hi, hnd, hnc, hlt, hdr, hfnd, hfsub, hsS, hout, hdom, hrem, hkk, hTi, hHi, hcs0, hkn0⟩ := h
  have hT := hTi hT0
  have hHt := hHi hH0
  unfold node.spill.subPostP at hp
  obtain ⟨hg', hfr', hpg', hps', hB', hbv', hib', hnm', hbm', hn', hKn', hnv', hkey', hknil', hks',
    hput, hlive', hlen', hcs', hpsne, hpsl, hpsnd, hsub, hfresh, hxpg, hc0pg, hpkey, hpsort, hxsp,
    hcsp, hxnd, hcx, hxout, hkeep, hdom', hgone, hpsk, hnewk, hkK, htree', hkx'⟩ := hp
  -- the child `c`, its tree, its entry
  have hcm : c ∈ rn.cs := List.mem_of_getElem? hc
  have hil : i < rn.cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hd := drop_cons_of_get rn.cs i c hc
  obtain ⟨hkt, -, hus⟩ := hdr c (by rw [hd]; exact List.mem_cons_self)
  obtain ⟨-, hsu⟩ := hus hsp
  obtain ⟨-, rc0, hrc0, hU⟩ := hsu.2 c (kidsTree_head B.ns c (sub c) hkt)
  rw [hrc] at hrc0; cases hrc0
  have hleaf : rn.nv.isLeaf' = false := by
    cases hlf : rn.nv.isLeaf'
    · rfl
    · have := hL.2.2.2.2.2.2.2.2.1 hlf; rw [this] at hcm; cases hcm
  obtain ⟨hpgnd, h2, -, hnmc, hcsc⟩ := hL.2.2.2.2.2.2.2.2.2 hleaf
  obtain ⟨j, w, hw, hwc⟩ : ∃ (j : Nat) (w : WEntry), rn.ws[j]? = some w ∧ B.nm !! w.pgid = some c := by
    rcases hcsc c hcm with hh | ⟨rc', hrc', hs', -⟩
    · exact hh
    · rw [hrc] at hrc'; cases hrc'; rw [hU.2.1] at hs'; cases hs'
  obtain ⟨rc', hrc', -, hcpg, hkeyc, -, -, -, hbnd⟩ := hnmc j w c hw hwc
  rw [hrc] at hrc'; cases hrc'
  obtain ⟨i0, w0, es, hw0, hw0k, hes, hws'⟩ := hput
  have hjl : j < rn.ws.length := (List.getElem?_eq_some_iff.1 hw).1
  have hi0l : i0 < rn.ws.length := by
    have := (List.getElem?_eq_some_iff.1 hw0).1; simpa using this
  have hk0 : wKey rn.ws i0 = rc.key := by
    rw [← wKey_fresh]; unfold wKey; rw [hw0]; exact hw0k
  have hkj : wKey rn.ws j = rc.key := by unfold wKey; rw [hw]; exact hkeyc.symm
  have hij : i0 = j := wsSorted_inj rn.ws hL.2.2.2.1 i0 j hi0l hjl (by rw [hk0, hkj])
  subst hij
  -- the tree: `n`'s other children are outside `c`'s tree
  obtain ⟨⟨rk, Nt, hTH⟩, -, -, -⟩ := hT
  have hfl0 := hfnd
  rw [hd] at hfl0
  simp only [List.map_cons, List.flatten_cons] at hfl0
  have hnsub : n ∉ sub c := fun hm => (List.nodup_cons.1 hfl0).1 (List.mem_append_left _ hm)
  have hcsN : ∀ x ∈ rn.cs, x ≠ c → x ∉ sub c := by
    intro x hx hxc hxs
    obtain ⟨y, hy, ry, hry, hxy⟩ := kidsTree_child B.ns (sub c).length c (sub c) (Nat.le_refl _) hkt x hxs hxc
    obtain ⟨rx, hrx, hpx⟩ := (hTH.2.1 y ry hry).2 x hxy
    obtain ⟨rx2, hrx2, hpx2⟩ := (hTH.2.1 n rn hn).2 x hx
    rw [hrx] at hrx2; cases hrx2
    rw [hpx] at hpx2; subst hpx2; exact hnsub hy
  have hcsdom : ∀ x ∈ rn.cs, ∃ rx, B.ns !! x = some rx := fun x hx => by
    obtain ⟨rx, hrx, -⟩ := (hTH.2.1 n rn hn).2 x hx; exact ⟨rx, hrx⟩
  have hxcs : ∀ x ∈ xs, x ∉ rn.cs := fun x hx hm => by
    by_cases hxc : x = c
    · subst hxc; exact hcx hx
    · obtain ⟨rx, hrx⟩ := hcsdom x hm
      exact hxout x hx x (hcsN x hm hxc) (by rw [hrx]; rfl) rfl
  have hnx : n ∉ xs := fun hm => hxout n hm n hnsub (by rw [hn]; rfl) rfl
  have hnrn : n ∉ rn.cs := hnc
  -- the later children's trees: outside `c`'s tree, not `n`
  have hlater : ∀ c' ∈ rn.cs.drop (i + 1), ∀ x ∈ sub c', x ∉ sub c ∧ x ≠ n := by
    intro c' hc' x hx
    have hxf : x ∈ ((rn.cs.drop (i + 1)).map sub).flatten :=
      List.mem_flatten.2 ⟨sub c', List.mem_map.2 ⟨c', hc', rfl⟩, hx⟩
    refine ⟨fun hh => (List.nodup_append.1 (List.nodup_cons.1 hfl0).2).2.2 x hh x hxf rfl, fun e => ?_⟩
    exact (List.nodup_cons.1 hfl0).1 (List.mem_append_right _ (e ▸ hxf))
  -- the nodes of `B'`
  have hcls : ∀ l r', B'.ns !! l = some r' → (l = n ∧ r' = rn') ∨ l = c ∨ l ∈ xs ∨
      (∃ rl, B.ns !! l = some rl ∧ l ∉ sub c ∧ l ≠ n ∧ l ≠ c ∧ (r' = rl ∨ derefNodeK rl r')) := by
    intro l r' hl
    by_cases e1 : l = n
    · subst e1; rw [hn'] at hl; cases hl; exact Or.inl ⟨rfl, rfl⟩
    by_cases e2 : l = c
    · exact Or.inr (Or.inl e2)
    by_cases e3 : l ∈ xs
    · exact Or.inr (Or.inr (Or.inl e3))
    right; right; right
    have hb : (B.ns !! l).isSome := by
      rcases hdom' l (by rw [hl]; rfl) with h | h
      · exact h
      · exact absurd h e3
    obtain ⟨rl, hrl⟩ := Option.isSome_iff_exists.1 hb
    have hls : l ∉ sub c := fun hm => by have := hgone l hm e2 e3; rw [hl] at this; cases this
    obtain ⟨rl', hrl', hdk⟩ := hkeep l rl hls e1 hrl
    rw [hl] at hrl'; cases hrl'
    exact ⟨rl, hrl, hls, e1, e2, hdk⟩
  -- `n`'s entries: the old ones but `c`'s, and the parts'
  have hm : es.length = ps.length := hes.length_eq.symm
  have hmpos : 0 < ps.length := List.length_pos_iff.2 hpsne
  have hWl : (rn.ws.map ownFresh).length = rn.ws.length := List.length_map _
  have hL'l : rn'.ws.length = rn.ws.length - 1 + es.length := by
    have e : (rn'.ws.map ownFresh).length = rn'.ws.length := List.length_map _
    rw [← e, hws', mid_len _ _ _ (by rw [hWl]; exact hi0l), hWl]
  have hwkey' : wKey rn'.ws = wKey ((rn.ws.map ownFresh).take i0 ++ es ++ (rn.ws.map ownFresh).drop (i0 + 1)) := by
    rw [← hws', wKey_fresh]
  have hesk : ∀ e ∈ es, ∃ p ∈ ps, e.key = p.2 ∧ e.pgid = p.1 ∧ e.value = [] := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨p, hp, -, h2, h3, h4, -⟩ := forall2_get_r _ ps es hes k es[k] (List.getElem?_eq_getElem hk)
    exact ⟨p, List.mem_of_getElem? hp, h3, h2, h4⟩
  have hent : ∀ w' ∈ rn'.ws, (∃ w1 ∈ rn.ws, w'.key = w1.key ∧ w'.pgid = w1.pgid ∧ w'.value = w1.value) ∨
      (∃ p ∈ ps, w'.key = p.2 ∧ w'.pgid = p.1 ∧ w'.value = []) := by
    intro w' hw'
    have hm' : ownFresh w' ∈ (rn.ws.map ownFresh).take i0 ++ es ++ (rn.ws.map ownFresh).drop (i0 + 1) := by
      rw [← hws']; exact List.mem_map.2 ⟨w', hw', rfl⟩
    rcases List.mem_append.1 hm' with hm' | hm'
    · rcases List.mem_append.1 hm' with hm' | hm'
      · obtain ⟨w1, hw1, he⟩ := List.mem_map.1 (List.mem_of_mem_take hm')
        exact Or.inl ⟨w1, hw1, by rw [← ownFresh_key w', ← he]; rfl, by rw [← ownFresh_pgid w', ← he]; rfl,
          by have := congrArg WEntry.value he; simpa [ownFresh] using this.symm⟩
      · obtain ⟨p, hp, h1, h2, h3⟩ := hesk _ hm'
        exact Or.inr ⟨p, hp, h1, h2, h3⟩
    · obtain ⟨w1, hw1, he⟩ := List.mem_map.1 (List.mem_of_mem_drop hm')
      exact Or.inl ⟨w1, hw1, by rw [← ownFresh_key w', ← he]; rfl, by rw [← ownFresh_pgid w', ← he]; rfl,
        by have := congrArg WEntry.value he; simpa [ownFresh] using this.symm⟩
  -- the parts' keys: between the neighbours of `c`'s entry, within `n`'s bounds
  have hWk : ∀ k, wKey (rn.ws.map ownFresh) k = wKey rn.ws k := fun k => by rw [wKey_fresh]
  have hplo : ∀ p ∈ ps, 0 < i0 → ¬ go.GoStringLt p.2 rc.key := by
    intro p hp hpos
    obtain ⟨x, hx, hle⟩ := hbnd.1 (wKey rn.ws i0) (by unfold entryBnd childLo; rw [if_neg (by omega)])
    rw [hk0] at hle
    exact notLt_trans' ((hpkey p hp).1.1 x hx) hle
  have hphi : ∀ p ∈ ps, i0 + 1 < rn.ws.length → go.GoStringLt p.2 (wKey rn.ws (i0 + 1)) := by
    intro p hp hlt
    obtain ⟨x, hx, hle⟩ := hbnd.2 (wKey rn.ws (i0 + 1)) (by unfold entryBnd childHi; rw [if_pos hlt])
    exact lt_of_lt_notLt ((hpkey p hp).1.2 x hx) hle
  have hpn : ∀ p ∈ ps, keyIn (bnd n).1 (bnd n).2 p.2 := by
    intro p hp
    have hw5 := hL.2.2.2.2.1 w (List.mem_of_getElem? hw)
    refine ⟨fun l hl => ?_, fun hh hh' => ?_⟩
    · by_cases hz : i0 = 0
      · obtain ⟨x, hx, hle⟩ := hbnd.1 l (by unfold entryBnd childLo; rw [if_pos hz]; exact hl)
        exact notLt_trans' ((hpkey p hp).1.1 x hx) hle
      · have h1 : ¬ go.GoStringLt rc.key l := by rw [hkeyc]; exact hw5.2.1 l hl
        exact notLt_trans' (hplo p hp (by omega)) h1
    · by_cases hz : i0 + 1 < rn.ws.length
      · obtain ⟨w2, hw2⟩ : ∃ w2, rn.ws[i0 + 1]? = some w2 := ⟨_, List.getElem?_eq_getElem hz⟩
        have hk2 : wKey rn.ws (i0 + 1) = w2.key := by unfold wKey; rw [hw2]; rfl
        have := (hL.2.2.2.2.1 w2 (List.mem_of_getElem? hw2)).2.2 hh hh'
        rw [← hk2] at this
        exact goStringLt_trans (hphi p hp hz) this
      · obtain ⟨x, hx, hle⟩ := hbnd.2 hh (by unfold entryBnd childHi; rw [if_neg hz]; exact hh')
        exact lt_of_lt_notLt ((hpkey p hp).1.2 x hx) hle
  -- `n`'s entries, by index
  have hWs : rn.ws.map ownFresh = (rn.ws.map ownFresh).take i0 ++ w0 :: (rn.ws.map ownFresh).drop (i0 + 1) := by
    rw [← drop_cons_of_get _ i0 w0 hw0, List.take_append_drop]
  have hi0W : i0 < (rn.ws.map ownFresh).length := by rw [hWl]; exact hi0l
  have hget : ∀ (j' : Nat) (w' : WEntry), rn'.ws[j']? = some w' →
      ((rn.ws.map ownFresh).take i0 ++ es ++ (rn.ws.map ownFresh).drop (i0 + 1))[j']? = some (ownFresh w') := by
    intro j' w' hw'; rw [← hws', List.getElem?_map, hw']; rfl
  have hidx : ∀ (j' : Nat) (w' : WEntry), rn'.ws[j']? = some w' →
      (j' < i0 ∧ ∃ w1, rn.ws[j']? = some w1 ∧ w'.key = w1.key ∧ w'.pgid = w1.pgid) ∨
      (i0 ≤ j' ∧ j' < i0 + es.length ∧ ∃ p ∈ ps, w'.pgid = p.1) ∨
      (i0 + es.length ≤ j' ∧ ∃ w1, rn.ws[j' + 1 - es.length]? = some w1 ∧ w'.key = w1.key ∧
        w'.pgid = w1.pgid) := by
    intro j' w' hw'
    have hg := hget j' w' hw'
    by_cases h1 : j' < i0
    · rw [mid_get_left _ _ _ _ hi0W h1, List.getElem?_map] at hg
      obtain ⟨w1, hw1, he⟩ := Option.map_eq_some_iff.1 hg
      exact Or.inl ⟨h1, w1, hw1, by rw [← ownFresh_key w', ← he]; rfl, by rw [← ownFresh_pgid w', ← he]; rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j' = i0 + k := ⟨j' - i0, by omega⟩
      rw [mid_get_mid _ _ _ _ hi0W] at hg
      by_cases h2 : k < es.length
      · rw [if_pos h2] at hg
        obtain ⟨p, hp, -, h3, -, -, -⟩ := forall2_get_r _ ps es hes k _ hg
        exact Or.inr (Or.inl ⟨by omega, by omega, p, List.mem_of_getElem? hp, by rw [← ownFresh_pgid w']; exact h3⟩)
      · rw [if_neg h2, List.getElem?_map] at hg
        obtain ⟨w1, hw1, he⟩ := Option.map_eq_some_iff.1 hg
        refine Or.inr (Or.inr ⟨by omega, w1, ?_, by rw [← ownFresh_key w', ← he]; rfl,
          by rw [← ownFresh_pgid w', ← he]; rfl⟩)
        rw [show i0 + k + 1 - es.length = i0 + 1 + (k - es.length) by omega]; exact hw1
  -- the inverse: an old entry but `c`'s, in `n`'s new entries
  have hinv : ∀ (j1 : Nat) (w1 : WEntry), rn.ws[j1]? = some w1 → j1 ≠ i0 →
      ∃ j' w', rn'.ws[j']? = some w' ∧ w'.pgid = w1.pgid ∧ w'.key = w1.key ∧
        (j1 < i0 → j' = j1) ∧ (i0 < j1 → j' = j1 + es.length - 1) := by
    intro j1 w1 hw1 hne
    have hL' : ((rn.ws.map ownFresh).take i0 ++ es ++ (rn.ws.map ownFresh).drop (i0 + 1))[
        if j1 < i0 then j1 else j1 + es.length - 1]? = some (ownFresh w1) := by
      by_cases h1 : j1 < i0
      · rw [if_pos h1, mid_get_left _ _ _ _ hi0W h1, List.getElem?_map, hw1]; rfl
      · rw [if_neg h1, show j1 + es.length - 1 = i0 + (es.length + (j1 - i0 - 1)) by omega,
          mid_get_mid _ _ _ _ hi0W, if_neg (by omega), List.getElem?_map,
          show i0 + 1 + (es.length + (j1 - i0 - 1) - es.length) = j1 by omega, hw1]; rfl
    rw [← hws', List.getElem?_map] at hL'
    obtain ⟨w', hw', he⟩ := Option.map_eq_some_iff.1 hL'
    refine ⟨_, w', hw', by rw [← ownFresh_pgid w', he]; rfl, by rw [← ownFresh_key w', he]; rfl,
      fun h => by rw [if_pos h], fun h => by rw [if_neg (by omega)]⟩
  have enl : rn'.nv.isLeaf' = rn.nv.isLeaf' := by rw [hnv']
  have enb : rn'.nv.bucket' = rn.nv.bucket' := by rw [hnv']
  have ens : rn'.nv.spilled' = rn.nv.spilled' := by rw [hnv']
  have enp : rn'.nv.pgid' = rn.nv.pgid' := by rw [hnv']
  have enpar : rn'.nv.parent' = rn.nv.parent' := by rw [hnv']
  have hlen'' : wKey rn'.ws = wKey ((rn.ws.map ownFresh).take i0 ++ es ++ (rn.ws.map ownFresh).drop (i0 + 1)) :=
    hwkey'
  -- keys of the new entries
  have hkL : ∀ j', j' < i0 → wKey rn'.ws j' = wKey rn.ws j' := by
    intro j' hj'; rw [hlen'', wKey_mid_left' _ _ _ _ hi0W hj', hWk]
  have hkM : ∀ k (p : w64 × List w8), ps[k]? = some p → wKey rn'.ws (i0 + k) = p.2 := by
    intro k p hp
    have hk : k < es.length := by rw [hm]; exact (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨e, he, -, -, h3, -⟩ := forall2_get' _ ps es hes k p hp
    rw [hlen'']; unfold wKey; rw [mid_get_mid _ _ _ _ hi0W, if_pos hk, he]; exact h3
  have hkR : ∀ k, es.length ≤ k → wKey rn'.ws (i0 + k) = wKey rn.ws (i0 + 1 + (k - es.length)) := by
    intro k hk
    rw [hlen'', ← hWk]; unfold wKey; rw [mid_get_mid _ _ _ _ hi0W, if_neg (by omega)]
  have hcsI : rn'.cs = rn.cs ++ xs := hcs'
  -- `n` after the child's spill: in its loop
  have hnL : nodeL W' bl B' bnd kd n rn' := by
    refine ⟨by rw [enb]; exact hL.1, by rw [ens]; exact hL.2.1, hlen', ?_, ?_, hlive', ?_, ?_, ?_, ?_⟩
    · -- sorted
      have e1 : wsSorted rn'.ws ↔ wsSorted (rn'.ws.map ownFresh) := by
        unfold wsSorted; rw [wKey_fresh, List.length_map]
      rw [e1, hws', wsSorted_iff]
      have hWp : (rn.ws.map ownFresh).Pairwise (fun a b => go.GoStringLt a.key b.key) := by
        rw [← wsSorted_iff]; unfold wsSorted; rw [wKey_fresh, List.length_map]; exact hL.2.2.2.1
      rw [hWs] at hWp
      apply ws_sorted_mid _ _ es w0 hWp (es_pairwise ps es hes hpsort)
      · intro a ha e he
        have hpos : 0 < i0 := by
          rcases Nat.eq_zero_or_pos i0 with hz | hz
          · subst hz; simp at ha
          · exact hz
        have hwa : go.GoStringLt a.key w0.key := (List.pairwise_append.1 hWp).2.2 a ha w0 List.mem_cons_self
        obtain ⟨p, hp, hke, -, -⟩ := hesk e he
        rw [hke]; rw [hw0k] at hwa
        exact lt_of_lt_notLt hwa (hplo p hp hpos)
      · intro e he c2 hc2
        obtain ⟨p, hp, hke, -, -⟩ := hesk e he
        obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem hc2
        have hlt1 : i0 + 1 < rn.ws.length := by rw [List.length_drop, hWl] at hk; omega
        have hc2k : c2.key = wKey rn.ws (i0 + 1 + k) := by
          rw [← hWk]; unfold wKey; rw [← List.getElem?_drop, List.getElem?_eq_getElem hk, hkc]; rfl
        have hle : ¬ go.GoStringLt c2.key (wKey rn.ws (i0 + 1)) := by
          rw [hc2k]
          rcases Nat.eq_zero_or_pos k with hz | hz
          · subst hz; exact goStringLt_irrefl_w _
          · intro hh
            exact goStringLt_irrefl_w _ (goStringLt_trans hh
              (hL.2.2.2.1 (i0 + 1) (i0 + 1 + k) (by omega) (by rw [List.length_drop, hWl] at hk; omega)))
        rw [hke]; exact lt_of_lt_notLt (hphi p hp hlt1) hle
    · intro w' hw'
      rcases hent w' hw' with ⟨w1, hw1, hk1, -, -⟩ | ⟨p, hp, hk1, -, -⟩
      · rw [hk1]; exact hL.2.2.2.2.1 w1 hw1
      · rw [hk1]; exact ⟨(hpkey p hp).2, hpn p hp⟩
    · by_cases hk' : rn'.nv.key' = slice.nil
      · exact Or.inl hk'
      · right
        have hrk : rn.nv.key' ≠ slice.nil := fun e => hk' (hknil' e)
        rcases hL.2.2.2.2.2.2.1 with h7 | ⟨hpos, hst⟩
        · exact absurd h7 hrk
        · refine ⟨by rw [hkey']; exact hpos, ?_⟩
          rcases hks' with e | e
          · rw [e]; exact hst
          · rw [e]; nofun
    · rw [enp, hpg']; exact hL.2.2.2.2.2.2.2.1
    · intro hlf; rw [enl, hleaf] at hlf; cases hlf
    · intro _
      refine ⟨?_, by rw [hL'l]; omega, ?_, ?_, ?_⟩
      · -- page ids distinct
        have e1 : rn'.ws.map WEntry.pgid = (rn'.ws.map ownFresh).map WEntry.pgid := by
          rw [List.map_map]; rfl
        rw [e1, hws', List.map_append, List.map_append]
        have hWp : ((rn.ws.map ownFresh).map WEntry.pgid).Nodup := by
          rw [List.map_map]; exact hpgnd
        rw [hWs, List.map_append, List.map_cons] at hWp
        apply nodup_mid
        · exact hWp.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)
        · rw [← forall2_map_eq Prod.fst WEntry.pgid ps es (List.Forall₂.imp (fun h => h.2.1.symm) hes)]
          exact hpsnd
        · intro y hy hyAC
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
          obtain ⟨p, hp, -, hpe, -⟩ := hesk e he
          have hnone := spillPages_none W T p.1 (hfresh p hp).2.1 (hfresh p hp).1
          have hin : e.pgid ∈ (rn.ws.map ownFresh).map WEntry.pgid := by
            rw [hWs, List.map_append, List.map_cons]
            rcases List.mem_append.1 hyAC with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
          rw [List.map_map] at hin
          obtain ⟨w1, hw1, he1⟩ := List.mem_map.1 hin
          have hsome := hok.2.2.2 n rn w1 hn hleaf hw1
          have : w1.pgid = p.1 := by rw [← hpe]; exact he1
          rw [this, hnone] at hsome; cases hsome
      · rw [hcsI]
        refine List.nodup_append.2 ⟨hnd, hxnd, fun a ha b hb e => hxcs b hb (e ▸ ha)⟩
      · -- the materialized children
        intro j' w' c' hw' hc'
        rw [hnm'] at hc'
        rcases hidx j' w' hw' with ⟨hj', w1, hw1, hk1, hp1⟩ | ⟨-, -, p, hp, hpp⟩ | ⟨hj', w1, hw1, hk1, hp1⟩
        · rw [hp1] at hc'
          obtain ⟨rc1, hrc1, hpar1, hpg1, hkey1, hkn1, hcm1, hkd1, hb1⟩ := hnmc j' w1 c' hw1 hc'
          have hc'c : c' ≠ c := by
            intro e; subst e; rw [hrc] at hrc1; cases hrc1
            exact absurd (nodup_map_idx WEntry.pgid rn.ws hpgnd j' i0 w1 w hw1 hw (by rw [← hpg1, hcpg]))
              (by omega)
          obtain ⟨rc1', hrc1', hdk⟩ := hkeep c' rc1 (hcsN c' hcm1 hc'c) (fun e => hnrn (e ▸ hcm1)) hrc1
          have hpos : 0 < rc1.key.length := by rw [hkey1]; exact (hL.2.2.2.2.1 w1 (List.mem_of_getElem? hw1)).1
          obtain ⟨f1, f2, f3, f4, f5, -, -⟩ := child_keep rc1 rc1' hdk hkn1 hpos
          refine ⟨rc1', hrc1', by rw [f1, hpar1], by rw [f2, hpg1, hp1], by rw [f3, hkey1, hk1], f4,
            by rw [hcsI]; exact List.mem_append_left _ hcm1, by rw [f5]; exact hkd1, ?_⟩
          unfold entryBnd at hb1 ⊢
          have hlo : childLo (bnd n).1 (wKey rn'.ws) j' = childLo (bnd n).1 (wKey rn.ws) j' := by
            unfold childLo; by_cases hz : j' = 0
            · rw [if_pos hz, if_pos hz]
            · rw [if_neg hz, if_neg hz, hkL j' hj']
          rw [hlo]
          by_cases hj2 : j' + 1 < i0
          · have hhi : childHi (bnd n).2 (wKey rn'.ws) rn'.ws.length j' =
                childHi (bnd n).2 (wKey rn.ws) rn.ws.length j' := by
              unfold childHi; rw [if_pos (by rw [hL'l]; omega), if_pos (by omega), hkL _ hj2]
            rw [hhi]; exact hb1
          · obtain ⟨p0, hp0⟩ : ∃ p0, ps[0]? = some p0 := ⟨_, List.getElem?_eq_getElem hmpos⟩
            have hh1 : childHi (bnd n).2 (wKey rn.ws) rn.ws.length j' = some rc.key := by
              unfold childHi; rw [if_pos (by omega), show j' + 1 = i0 by omega, hk0]
            have hh2 : childHi (bnd n).2 (wKey rn'.ws) rn'.ws.length j' = some p0.2 := by
              unfold childHi; rw [if_pos (by rw [hL'l]; omega), show j' + 1 = i0 + 0 by omega, hkM 0 p0 hp0]
            rw [hh1] at hb1; rw [hh2]
            exact bndIn_widen _ _ _ _ hb1 (hplo p0 (List.mem_of_getElem? hp0) (by omega))
        · rw [hpp, (hfresh p hp).2.2.2.1] at hc'; cases hc'
        · rw [hp1] at hc'
          obtain ⟨rc1, hrc1, hpar1, hpg1, hkey1, hkn1, hcm1, hkd1, hb1⟩ := hnmc _ w1 c' hw1 hc'
          have hc'c : c' ≠ c := by
            intro e; subst e; rw [hrc] at hrc1; cases hrc1
            exact absurd (nodup_map_idx WEntry.pgid rn.ws hpgnd _ i0 w1 w hw1 hw (by rw [← hpg1, hcpg]))
              (by omega)
          obtain ⟨rc1', hrc1', hdk⟩ := hkeep c' rc1 (hcsN c' hcm1 hc'c) (fun e => hnrn (e ▸ hcm1)) hrc1
          have hpos : 0 < rc1.key.length := by rw [hkey1]; exact (hL.2.2.2.2.1 w1 (List.mem_of_getElem? hw1)).1
          obtain ⟨f1, f2, f3, f4, f5, -, -⟩ := child_keep rc1 rc1' hdk hkn1 hpos
          refine ⟨rc1', hrc1', by rw [f1, hpar1], by rw [f2, hpg1, hp1], by rw [f3, hkey1, hk1], f4,
            by rw [hcsI]; exact List.mem_append_left _ hcm1, by rw [f5]; exact hkd1, ?_⟩
          obtain ⟨k, rfl⟩ : ∃ k, j' = i0 + k := ⟨j' - i0, by omega⟩
          have hw1l : i0 + k + 1 - es.length < rn.ws.length := (List.getElem?_eq_some_iff.1 hw1).1
          have hlo : childLo (bnd n).1 (wKey rn'.ws) (i0 + k) =
              childLo (bnd n).1 (wKey rn.ws) (i0 + k + 1 - es.length) := by
            unfold childLo
            rw [if_neg (show ¬ (i0 + k = 0) by omega), if_neg (show ¬ (i0 + k + 1 - es.length = 0) by omega),
              hkR k (by omega)]
            congr 2; omega
          have hhi : childHi (bnd n).2 (wKey rn'.ws) rn'.ws.length (i0 + k) =
              childHi (bnd n).2 (wKey rn.ws) rn.ws.length (i0 + k + 1 - es.length) := by
            unfold childHi
            by_cases hz : i0 + k + 1 - es.length + 1 < rn.ws.length
            · rw [if_pos (show i0 + k + 1 < rn'.ws.length by rw [hL'l]; omega), if_pos hz,
                show i0 + k + 1 = i0 + (k + 1) by omega, hkR (k + 1) (by omega)]
              congr 2; omega
            · rw [if_neg (show ¬ (i0 + k + 1 < rn'.ws.length) by rw [hL'l]; omega), if_neg hz]
          unfold entryBnd at hb1 ⊢; rw [hlo, hhi]; exact hb1
      · -- the children: materialized, or spilled parts
        intro c' hc'
        rw [hcsI] at hc'
        rcases List.mem_append.1 hc' with hc' | hc'
        · by_cases hcc : c' = c
          · subst hcc; exact Or.inr hcsp
          rcases hcsc c' hc' with ⟨j1, w1, hw1, hc1⟩ | hs
          · have hj1 : j1 ≠ i0 := by
              intro e; subst e; rw [hw] at hw1; cases hw1; rw [hwc] at hc1; cases hc1; exact hcc rfl
            obtain ⟨j', w', hw', hpe, -, -, -⟩ := hinv j1 w1 hw1 hj1
            exact Or.inl ⟨j', w', hw', by rw [hnm', hpe]; exact hc1⟩
          · obtain ⟨rc1, hrc1⟩ := hcsdom c' hc'
            obtain ⟨rc1', hrc1', hdk⟩ := hkeep c' rc1 (hcsN c' hc' hcc) (fun e => hnrn (e ▸ hc')) hrc1
            exact Or.inr (spilledN_keep bl B B' c' rc1 rc1' hs hrc1 hrc1' hdk hnm')
        · exact Or.inr (hxsp c' hc')
  -- the nodes kept: their entries, struct, children
  have hkw : ∀ (rl r' : NRec), (r' = rl ∨ derefNodeK rl r') → ∀ w' ∈ r'.ws, ∃ w1 ∈ rl.ws,
      w'.key = w1.key ∧ w'.value = w1.value ∧ w'.pgid = w1.pgid := by
    intro rl r' hdk w' hw'
    rcases hdk with rfl | ⟨⟨⟨-, hws, -⟩, -⟩, -⟩
    · exact ⟨w', hw', rfl, rfl, rfl⟩
    · rw [hws] at hw'; obtain ⟨w1, hw1, rfl⟩ := List.mem_map.1 hw'; exact ⟨w1, hw1, rfl, rfl, rfl⟩
  have hkn : ∀ (rl r' : NRec), (r' = rl ∨ derefNodeK rl r') →
      r'.nv = { rl.nv with key' := r'.nv.key' } ∧ r'.ws.length = rl.ws.length ∧ r'.cs = rl.cs := by
    intro rl r' hdk
    rcases hdk with rfl | ⟨⟨⟨-, hws, hcs, -⟩, -⟩, hnv⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hnv, by rw [hws, List.length_map], hcs⟩
  have hsubS : ∀ k, (spillPages W T !! k).isSome → (spillPages W' T' !! k).isSome := by
    intro k hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hk
    rw [hsub k v hv]; rfl
  have hspl : ∀ x r', (x = c ∨ x ∈ xs) → B'.ns !! x = some r' →
      r'.nv.spilled' = true ∧ r'.cs = [] ∧ 0 < r'.ws.length := by
    intro x r' hx hr'
    have hs : spilledN bl B' x := by
      rcases hx with rfl | hx
      · exact hcsp
      · exact hxsp x hx
    obtain ⟨rx, hrx, hsp1, hcs1, -, hpos, hil1, -⟩ := hs
    rw [hr'] at hrx; cases hrx
    exact ⟨hsp1, hcs1, by rw [← hil1]; exact hpos⟩
  have hnok : nodesOK W' T' B' := by
    obtain ⟨o1, o2, o3, o4⟩ := hok
    refine ⟨fun l r' hl w' hw' => ?_, fun l r' hl hpar => ?_, ?_, fun l r' w' hl hlf hw' => ?_⟩
    · rcases hcls l r' hl with ⟨rfl, rfl⟩ | hlc | hx | ⟨rl, hrl, -, -, -, hdk⟩
      · rcases hent w' hw' with ⟨w1, hw1, hk1, -, hv1⟩ | ⟨p, hp, hk1, -, hv1⟩
        · rw [hk1, hv1]; exact o1 l rn hn w1 hw1
        · rw [hk1, hv1]; have := hpsk p hp; simp only [List.length_nil, Nat.add_zero]; exact this
      · exact (hnewk l r' (Or.inl hlc) hl).1 w' hw'
      · exact (hnewk l r' (Or.inr hx) hl).1 w' hw'
      · obtain ⟨w1, hw1, hk1, hv1, -⟩ := hkw rl r' hdk w' hw'
        rw [hk1, hv1]; exact o1 l rl hrl w1 hw1
    · rcases hcls l r' hl with ⟨rfl, rfl⟩ | hlc | hx | ⟨rl, hrl, -, -, -, hdk⟩
      · rw [hL'l]; omega
      · exact (hspl l r' (Or.inl hlc) hl).2.2
      · exact (hspl l r' (Or.inr hx) hl).2.2
      · obtain ⟨hnv1, hl1, -⟩ := hkn rl r' hdk
        rw [hl1]; exact o2 l rl hrl (by rw [show rl.nv.parent' = r'.nv.parent' by rw [hnv1]]; exact hpar)
    · rw [hnm', hpg']; exact o3
    · rcases hcls l r' hl with ⟨rfl, rfl⟩ | hlc | hx | ⟨rl, hrl, -, -, -, hdk⟩
      · rcases hent w' hw' with ⟨w1, hw1, -, hp1, -⟩ | ⟨p, hp, -, hp1, -⟩
        · rw [hp1]; exact hsubS _ (o4 l rn w1 hn hleaf hw1)
        · rw [hp1]; exact spillPages_buf W' T' p.1 (hfresh p hp).2.2.1
      · exact (hnewk l r' (Or.inl hlc) hl).2 hlf w' hw'
      · exact (hnewk l r' (Or.inr hx) hl).2 hlf w' hw'
      · obtain ⟨hnv1, -, -⟩ := hkn rl r' hdk
        obtain ⟨w1, hw1, -, -, hp1⟩ := hkw rl r' hdk w' hw'
        rw [hp1]; exact hsubS _ (o4 l rl w1 hrl (by rw [show rl.nv.isLeaf' = r'.nv.isLeaf' by rw [hnv1]]; exact hlf) hw1)
  have hP1' : ∀ l r', B'.ns !! l = some r' → l ≠ n → r'.nv.isLeaf' = false → r'.nv.pgid' ≠ W64 0 := by
    intro l r' hl hln hlf
    have hp2 : ∀ (p : w64 × List w8), p ∈ ps → p.1 ≠ W64 0 := by
      intro p hp e
      have := (hfresh p hp).2.2.2.2; rw [e] at this; simp at this
    rcases hcls l r' hl with ⟨rfl, -⟩ | hlc | hx | ⟨rl, hrl, -, -, -, hdk⟩
    · exact absurd rfl hln
    · obtain ⟨p0, hp0⟩ : ∃ p0, ps[0]? = some p0 := ⟨_, List.getElem?_eq_getElem hmpos⟩
      obtain ⟨rn0, hrn0, hpg0⟩ := hc0pg p0 hp0
      rw [hlc] at hl; rw [hl] at hrn0; cases hrn0
      rw [hpg0]; exact hp2 p0 (List.mem_of_getElem? hp0)
    · obtain ⟨jx, hjx, hxj⟩ := List.getElem_of_mem hx
      obtain ⟨p, hp⟩ : ∃ p, ps[jx + 1]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨rx, hrx, hpgx⟩ := hxpg jx p l hp (by rw [← hxj]; exact List.getElem?_eq_getElem hjx)
      rw [hl] at hrx; cases hrx
      rw [hpgx]; exact hp2 p (List.mem_of_getElem? hp)
    · obtain ⟨hnv1, -, -⟩ := hkn rl r' hdk
      rw [show r'.nv.pgid' = rl.nv.pgid' by rw [hnv1]]
      exact hP1 l rl hrl hln (by rw [show rl.nv.isLeaf' = r'.nv.isLeaf' by rw [hnv1]]; exact hlf)
  have hdrop : rn'.cs.drop (i + 1) = rn.cs.drop (i + 1) ++ xs := by
    rw [hcsI, List.drop_append_of_le_length (by omega)]
  have hnotxs : ∀ c' ∈ rn.cs.drop (i + 1), c' ∉ xs := fun c' hc' hx =>
    hxcs c' hx (List.mem_of_mem_drop hc')
  have hmap : (rn'.cs.drop (i + 1)).map (fun x => if x ∈ xs then [x] else sub x) =
      (rn.cs.drop (i + 1)).map sub ++ xs.map (fun x => [x]) := by
    rw [hdrop, List.map_append]
    congr 1
    · apply List.map_congr_left; intro c' hc'; rw [if_neg (hnotxs c' hc')]
    · apply List.map_congr_left; intro x hx; rw [if_pos hx]
  have hflat1 : ∀ (l : List Loc), (l.map (fun y => [y])).flatten = l := by
    intro l; induction l with
    | nil => rfl
    | cons y l ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl
  have hflat : ((rn'.cs.drop (i + 1)).map (fun x => if x ∈ xs then [x] else sub x)).flatten =
      ((rn.cs.drop (i + 1)).map sub).flatten ++ xs := by
    rw [hmap, List.flatten_append, hflat1]
  -- the later children's trees: their nodes are `B`'s
  have hFdom : ∀ x ∈ ((rn.cs.drop (i + 1)).map sub).flatten, (B.ns !! x).isSome := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := List.mem_flatten.1 hx
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hs
    obtain ⟨hkt', -, -⟩ := hdr c' (mem_drop_succ _ _ _ hc')
    obtain ⟨rx, hrx, -⟩ := kidsTree_mem B.ns (sub c').length c' (sub c') (Nat.le_refl _) hkt' x hxs
    rw [hrx]; rfl
  have hnag : ∀ c' ∈ rn.cs.drop (i + 1), ∀ l ∈ sub c', nAgree B.ns B'.ns l := by
    intro c' hc' l hl r hr
    obtain ⟨h1, h2⟩ := hlater c' hc' l hl
    obtain ⟨r', hr', hdk⟩ := hkeep l r h1 h2 hr
    obtain ⟨hnv1, -, hcs1⟩ := hkn r r' hdk
    exact ⟨r', hr', hcs1, by rw [hnv1]⟩
  have hHt' : nodeHts B' ht := by
    intro l r' hl hspf
    rcases hcls l r' hl with ⟨rfl, rfl⟩ | hlc | hx | ⟨rl, hrl, -, -, -, hdk⟩
    · obtain ⟨-, hbr⟩ := hHt l rn hn hL.2.1
      obtain ⟨hh1, hh2⟩ := hbr hleaf
      refine ⟨(fun hlf => by rw [enl, hleaf] at hlf; cases hlf), fun _ => ⟨hh1, fun w' hw' c' hc' => ?_⟩⟩
      rcases hent w' hw' with ⟨w1, hw1, -, hp1, -⟩ | ⟨p, hp, -, hp1, -⟩
      · rw [hnm', hp1] at hc'; exact hh2 w1 hw1 c' hc'
      · rw [hnm', hp1, (hfresh p hp).2.2.2.1] at hc'; cases hc'
    · rw [(hspl l r' (Or.inl hlc) hl).1] at hspf; cases hspf
    · rw [(hspl l r' (Or.inr hx) hl).1] at hspf; cases hspf
    · obtain ⟨hnv1, -, -⟩ := hkn rl r' hdk
      have e1 : r'.nv.spilled' = rl.nv.spilled' := by rw [hnv1]
      have e2 : r'.nv.isLeaf' = rl.nv.isLeaf' := by rw [hnv1]
      obtain ⟨hh1, hh2⟩ := hHt l rl hrl (by rw [← e1]; exact hspf)
      refine ⟨fun hlf => hh1 (by rw [← e2]; exact hlf), fun hlf => ?_⟩
      obtain ⟨hb1, hb2⟩ := hh2 (by rw [← e2]; exact hlf)
      refine ⟨hb1, fun w' hw' c' hc' => ?_⟩
      obtain ⟨w1, hw1, -, -, hp1⟩ := hkw rl r' hdk w' hw'
      rw [hnm', hp1] at hc'; exact hb2 w1 hw1 c' hc'
  have hsubS0 : ∀ x ∈ sub c, x ∈ S0 := hsS c (by rw [hd]; exact List.mem_cons_self) hsp
  refine ⟨hg', hB', hn', hKn', spillFrame_transN T0 T T' _ _ hfr hfr' (fun _ h => h), hpg'.trans hpgs,
    hps'.trans hps, GMap.map_subseteq_trans hsp' hsub, hbv'.trans hbv, hib'.trans hib, hnm'.trans hnm,
    hbm'.trans hbm, node_upd3_trans _ _ _ hnv' hnv, hkey'.trans hkey, fun h => hknil' (hknil h), ?_, hnL,
    hnok, hP1', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => htree', fun _ => hHt', ?_, ?_⟩
  · rcases hks' with e | e
    · rw [e]; exact hks
    · exact Or.inr e
  · rw [hcsI, List.length_append]; omega
  · rw [hcsI]; exact List.nodup_append.2 ⟨hnd, hxnd, fun a ha b hb e => hxcs b hb (e ▸ ha)⟩
  · rw [hcsI]; intro hm'
    rcases List.mem_append.1 hm' with h | h
    · exact hnrn h
    · exact hnx h
  · intro j' c' hj' hc'
    have hj'l : j' < rn.cs.length := by omega
    rw [hcsI, List.getElem?_append_left hj'l] at hc'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
    · have hs := hlt j' c' hj' hc'
      have hcc : c' ≠ c := by
        intro e; subst e
        exact absurd (nodup_map_idx id rn.cs (by simpa using hnd) j' i c' c' hc' hc rfl) (by omega)
      have hcm' : c' ∈ rn.cs := List.mem_of_getElem? hc'
      obtain ⟨rc1, hrc1⟩ := hcsdom c' hcm'
      obtain ⟨rc1', hrc1', hdk⟩ := hkeep c' rc1 (hcsN c' hcm' hcc) (fun e => hnrn (e ▸ hcm')) hrc1
      exact spilledN_keep bl B B' c' rc1 rc1' hs hrc1 hrc1' hdk hnm'
    · rw [hc] at hc'; cases hc'; exact hcsp
  · intro c' hc'
    rw [hdrop] at hc'
    rcases List.mem_append.1 hc' with hc' | hx
    · simp only [hnotxs c' hc', ite_false]
      obtain ⟨hkt', hspT, hspF⟩ := hdr c' (mem_drop_succ _ _ _ hc')
      have hkt2 : kidsTree B'.ns c' (sub c') :=
        kidsTree_mono B.ns B'.ns (sub c').length c' (sub c') (Nat.le_refl _) (hnag c' hc') hkt'
      refine ⟨hkt2, fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨rc1, hrc1⟩ := hcsdom c' (List.mem_of_mem_drop hc')
        obtain ⟨h1, h2⟩ := hlater c' hc' c' (kidsTree_head B.ns c' (sub c') hkt')
        obtain ⟨rc1', hrc1', hdk⟩ := hkeep c' rc1 h1 h2 hrc1
        exact spilledN_keep bl B B' c' rc1 rc1' (hspT hs) hrc1 hrc1' hdk hnm'
      · obtain ⟨hlenc, hsuc⟩ := hspF hs
        refine ⟨hlenc, hkt2, fun x hx => ?_⟩
        obtain ⟨hKx, rx, hrx, hUx⟩ := hsuc.2 x hx
        obtain ⟨h1, h2⟩ := hlater c' hc' x hx
        obtain ⟨rx', hrx', hdk⟩ := hkeep x rx h1 h2 hrx
        refine ⟨by rw [hkK.1 x h1 (by rw [hrx]; rfl)]; exact hKx, rx', hrx', ?_⟩
        apply nodeU_keep W W' bl B B' bnd kd x rx rx' hpg' hnm' hdk _ hUx
        intro c3 rc3 hc3 hrc3
        obtain ⟨rx2, hrx2, hkids⟩ := kidsTree_mem B.ns (sub c').length c' (sub c') (Nat.le_refl _) hkt' x hx
        rw [hrx] at hrx2; cases hrx2
        obtain ⟨g1, g2⟩ := hlater c' hc' c3 (hkids c3 hc3)
        exact hkeep c3 rc3 g1 g2 hrc3
    · simp only [hx, ite_true]
      obtain ⟨rx, hrx, -, hcs1, -⟩ := hxsp c' hx
      exact ⟨kidsTree_leaf B'.ns c' rx hrx hcs1, fun _ => hxsp c' hx, fun h => by cases h⟩
  · rw [hflat]
    have hF := (List.nodup_cons.1 hfl0).2
    have hFn : (((rn.cs.drop (i + 1)).map sub).flatten).Nodup := (List.nodup_append.1 hF).2.1
    refine List.nodup_cons.2 ⟨fun hm' => ?_, List.nodup_append.2 ⟨hFn, hxnd, fun a ha b hb e => ?_⟩⟩
    · rcases List.mem_append.1 hm' with h | h
      · exact (List.nodup_cons.1 hfl0).1 (List.mem_append_right _ h)
      · exact hnx h
    · have haS : a ∉ sub c := fun hm' =>
        (List.nodup_append.1 (List.nodup_cons.1 hfl0).2).2.2 a hm' a ha rfl
      exact hxout b hb a haS (hFdom a ha) e
  · intro x hx
    rw [hflat] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases hfsub x (by rw [hd]; simp only [List.map_cons, List.flatten_cons]; exact List.mem_append_right _ hx) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hcsI]; exact List.mem_append_left _ h)
    · exact Or.inr (by rw [hcsI]; exact List.mem_append_right _ hx)
  · intro c' hc' hsf x hx
    rw [hdrop] at hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · simp only [hnotxs c' hc', ite_false] at hsf hx
      exact hsS c' (mem_drop_succ _ _ _ hc') hsf x hx
    · simp only [hc', ite_true] at hsf; cases hsf
  · intro x rx hx hrx
    obtain ⟨rx1, hrx1, hd1⟩ := hout x rx hx hrx
    have h1 : x ∉ sub c := fun hm' => hx (hsubS0 x hm')
    have h2 : x ≠ n := fun e => hx (e ▸ hnS)
    obtain ⟨rx', hrx', hdk⟩ := hkeep x rx1 h1 h2 hrx1
    exact ⟨rx', hrx', dnK_step rx rx1 rx' hd1 hdk⟩
  · intro x hx
    rcases hdom' x hx with h | h
    · rcases hdom x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [hcsI]; exact List.mem_append_left _ h')
    · exact Or.inr (by rw [hcsI]; exact List.mem_append_right _ h)
  · intro x hxS hx
    rw [hflat]
    rcases hdom' x hx with h | h
    · rcases hrem x hxS h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl (by rw [hcsI]; exact List.mem_append_left _ h'))
      · rw [hd] at h'
        simp only [List.map_cons, List.flatten_cons, List.mem_append] at h'
        rcases h' with h' | h'
        · by_cases hxc : x = c
          · subst hxc; exact Or.inr (Or.inl (by rw [hcsI]; exact List.mem_append_left _ hcm))
          · by_cases hxx : x ∈ xs
            · exact Or.inr (Or.inl (by rw [hcsI]; exact List.mem_append_right _ hxx))
            · have := hgone x h' hxc hxx; rw [this] at hx; cases hx
        · exact Or.inr (Or.inr (List.mem_append_left _ h'))
    · exact Or.inr (Or.inl (by rw [hcsI]; exact List.mem_append_right _ h))
  · refine ⟨fun x hx hb => ?_, fun c2 C l hc2 hC hl => ?_⟩
    · obtain ⟨rx, hrx⟩ := Option.isSome_iff_exists.1 hb
      obtain ⟨rx1, hrx1, -⟩ := hout x rx hx hrx
      rw [hkK.1 x (fun hm' => hx (hsubS0 x hm')) (by rw [hrx1]; rfl)]
      exact hkk.1 x hx hb
    · obtain ⟨d1, -, -, -, -, d6⟩ := hfr'
      obtain ⟨C0, hC0⟩ := Option.isSome_iff_exists.1 ((d1 c2).2 (by rw [hC]; rfl))
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hl
      obtain ⟨r0, hr0⟩ := derefStarX_ns C0 C (d6 c2 C0 C hc2 hC0 hC).1 l r' hr'
      rw [hkK.2 c2 C l hc2 hC hl]
      exact hkk.2 c2 C0 l hc2 hC0 (by rw [hr0]; rfl)
  · intro x hx
    rw [hcsI] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hcs0 x hx
    · by_cases hS : x ∈ S0
      · exact Or.inl hS
      · right
        cases hb : B0.ns !! x with
        | none => rfl
        | some rx =>
          obtain ⟨rx1, hrx1, -⟩ := hout x rx hS hb
          exact absurd rfl (hxout x hx x (fun hm' => hS (hsubS0 x hm')) (by rw [hrx1]; rfl))
  · intro h1 h2
    exact hkx' (hkn0 h1 h2) (by rw [hkey]; exact h2)


theorem bigSepL_emp_of {α : Type} (Φ : Nat → α → IProp GF) :
    ∀ (l : List α), (∀ k x, l[k]? = some x → emp ⊢ Φ k x) → emp ⊢ [∗list] k ↦ x ∈ l, Φ k x
  | [], _ => BigSepL.bigSepL_nil.2
  | x :: l, h => by
    refine BIBase.Entails.trans emp_sep.2 (BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2)
    exact sep_mono (h 0 x rfl) (bigSepL_emp_of (fun k => Φ (k + 1)) l (fun k y hy => h (k + 1) y hy))
theorem toks_sub_post (γ : GName) (bl : Loc) (bnd : Loc → Option (List w8) × Option (List w8))
    (kd ht : Loc → Nat) (N : Nat) (n txl : Loc) (txid : w64) (W0 : WView) (T0 : WTx) (B0 : BRec)
    (r0 : NRec) (K0 : Loc → Bool) (S0 : List Loc) (W : WView) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec) (rn : NRec) (i : Nat) (sp : Loc → Bool)
    (sub : Loc → List Loc) (c : Loc) (rc : NRec)
    (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)) (K' : Loc → Bool) (B' : BRec)
    (ps : List (w64 × List w8)) (xs : List Loc) (rn' : NRec)
    (h : loopP (hG := hG) bl bnd kd ht N n txl txid W0 T0 B0 r0 K0 S0 W T ρ F K B rn i sp sub)
    (hc : rn.cs[i]? = some c) (hsp : sp c = false) (hrc : B.ns !! c = some rc)
    (hp : node.spill.subPostP (hG := hG) W txl txid T bl B bnd (sub c) c rc n rn K W' T' ρ' F' K' B'
      ps xs rn') (hH0 : nodeHts B0 ht) :
    rtoks γ (spillPages W T) B (bnd n) (kd n) (ht n - 1) rn ∗
      subToks γ (spillPages W T) B bnd kd ht sp sub (rn.cs.drop (i + 1)) ∗
      pieceRes (GF := GF) γ (spillPages W' T') (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag)
        (ht c) ps (bnd c).2 ⊢
    rtoks γ (spillPages W' T') B' (bnd n) (kd n) (ht n - 1) rn' ∗
      subToks γ (spillPages W' T') B' bnd kd ht (fun x => if x ∈ xs then true else sp x)
        (fun x => if x ∈ xs then [x] else sub x) (rn'.cs.drop (i + 1)) := by
  obtain ⟨-, hB, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, -, -, -, -, hdr, hfnd, -, -, -,
    -, -, -, -, hHi, -⟩ := h
  have hHt := hHi hH0
  unfold node.spill.subPostP at hp
  obtain ⟨-, -, -, -, -, -, -, hnm', -, -, -, hnv', -, -, -, hput, -, -, hcs', hpsne, -, -, hsub, hfresh,
    -, -, hpkey, -, -, -, -, -, hxout, hkeep, -, -, -, -, -, -⟩ := hp
  have hcm : c ∈ rn.cs := List.mem_of_getElem? hc
  have hil : i < rn.cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hd := drop_cons_of_get rn.cs i c hc
  obtain ⟨hkt, -, hus⟩ := hdr c (by rw [hd]; exact List.mem_cons_self)
  obtain ⟨-, hsu⟩ := hus hsp
  obtain ⟨-, rc0, hrc0, hU⟩ := hsu.2 c (kidsTree_head B.ns c (sub c) hkt)
  rw [hrc] at hrc0; cases hrc0
  have hleaf : rn.nv.isLeaf' = false := by
    cases hlf : rn.nv.isLeaf'
    · rfl
    · have := hL.2.2.2.2.2.2.2.2.1 hlf; rw [this] at hcm; cases hcm
  obtain ⟨-, -, -, hnmc, hcs⟩ := hL.2.2.2.2.2.2.2.2.2 hleaf
  obtain ⟨j, w, hw, hwc⟩ : ∃ (j : Nat) (w : WEntry), rn.ws[j]? = some w ∧ B.nm !! w.pgid = some c := by
    rcases hcs c hcm with hh | ⟨rc', hrc', hs', -⟩
    · exact hh
    · rw [hrc] at hrc'; cases hrc'; rw [hU.2.1] at hs'; cases hs'
  obtain ⟨rc', hrc', -, -, hkeyc, -, -, hkd, hbnd⟩ := hnmc j w c hw hwc
  rw [hrc] at hrc'; cases hrc'
  obtain ⟨i0, w0, es, hw0, hw0k, hes, hws'⟩ := hput
  have hjl : j < rn.ws.length := (List.getElem?_eq_some_iff.1 hw).1
  have hi0l : i0 < rn.ws.length := by
    have := (List.getElem?_eq_some_iff.1 hw0).1; simpa using this
  have hk0 : wKey rn.ws i0 = rc.key := by
    rw [← wKey_fresh]; unfold wKey; rw [hw0]; exact hw0k
  have hkj : wKey rn.ws j = rc.key := by unfold wKey; rw [hw]; exact hkeyc.symm
  have hij : i0 = j := wsSorted_inj rn.ws hL.2.2.2.1 i0 j hi0l hjl (by rw [hk0, hkj])
  subst hij
  have hw0e : w0 = ownFresh w := by
    rw [List.getElem?_map, hw] at hw0; simp only [Option.map_some, Option.some.injEq] at hw0
    exact hw0.symm
  have hw0c : B.nm !! w0.pgid = some c := by rw [hw0e]; exact hwc
  have hfr : ∀ p ∈ ps, B.nm !! p.1 = none := fun p hp => (hfresh p hp).2.2.2.1
  have hkW : wKey (rn.ws.map ownFresh) i0 = rc.key := by rw [wKey_fresh]; exact hk0
  have hA1 : ∀ p, ps[0]? = some p → 0 < i0 → ¬ go.GoStringLt p.2 (wKey (rn.ws.map ownFresh) i0) := by
    intro p hp0 hpos
    rw [hkW, ← hk0]
    obtain ⟨x, hx, hle⟩ := hbnd.1 (wKey rn.ws i0) (by
      unfold entryBnd childLo; rw [if_neg (by omega)])
    have hge := (hpkey p (List.mem_of_getElem? hp0)).1.1 x hx
    exact notLt_trans' hge hle
  have hA2 : hiLe (bnd c).2 (childHi (bnd n).2 (wKey (rn.ws.map ownFresh)) (rn.ws.map ownFresh).length i0) := by
    rw [wKey_fresh, List.length_map]
    exact hbnd.2
  have hpg' : rn'.nv.pgid' = rn.nv.pgid' := by rw [hnv']
  have hlf' : rn'.nv.isLeaf' = rn.nv.isLeaf' := by rw [hnv']
  have hhc : ht c = ht n - 1 := by
    have := ((hHt n rn hn hL.2.1).2 hleaf).2 w (List.mem_of_getElem? hw) c hwc
    omega
  rw [← hkd, hhc]
  iintro ⟨Hrt, Hsub, Hpc⟩
  isplitl [Hrt Hpc]
  · unfold rtoks
    rw [hpg', hlf', hleaf]
    icases Hrt with ⟨Hpg, Hents⟩
    iframe Hpg
    iapply (ents_fresh γ _ B' (bnd n).2 false (kd n) (ht n - 1) rn'.ws).2
    rw [hws']
    ihave Hents := (ents_fresh γ _ B (bnd n).2 false (kd n) (ht n - 1) rn.ws).1 $$ Hents
    iapply ents_post γ _ _ B B' hsub hnm' (bnd n).2 (kd n) (ht n - 1) (rn.ws.map ownFresh) i0 w0 es ps c (bnd c).2
      hw0 hw0c hes hpsne hfr hA1 hA2
    iframe
  · rw [hcs', List.drop_append_of_le_length (by omega)]
    unfold subToks
    iapply BigSepL.bigSepL_append.2
    isplitl [Hsub]
    · iapply (BigSepL.bigSepL_mono ?_) $$ Hsub
      intro k c' hk
      have hc'm : c' ∈ rn.cs.drop (i + 1) := List.mem_of_getElem? hk
      have hc'd : c' ∈ rn.cs.drop i := mem_drop_succ _ _ _ hc'm
      obtain ⟨hkt', -, -⟩ := hdr c' hc'd
      have hnx : c' ∉ xs := by
        intro hx
        have hfl := hfnd
        rw [hd] at hfl
        simp only [List.map_cons, List.flatten_cons] at hfl
        have hcF : c' ∈ ((rn.cs.drop (i + 1)).map sub).flatten :=
          List.mem_flatten.2 ⟨sub c', List.mem_map.2 ⟨c', hc'm, rfl⟩, kidsTree_head B.ns c' _ hkt'⟩
        have hcS : c' ∉ sub c := fun hm' =>
          (List.nodup_append.1 (List.nodup_cons.1 hfl).2).2.2 c' hm' c' hcF rfl
        exact hxout c' hx c' hcS (kidsTree_some B.ns c' _ hkt') rfl
      simp only [hnx, ite_false]
      cases hspc : sp c'
      · simp only [Bool.false_eq_true, ite_false]
        apply BigSepL.bigSepL_mono
        intro k2 l hl
        have hlm : l ∈ sub c' := List.mem_of_getElem? hl
        have hfl := hfnd
        rw [hd] at hfl
        simp only [List.map_cons, List.flatten_cons] at hfl
        have hlf : l ∈ ((rn.cs.drop (i + 1)).map sub).flatten :=
          List.mem_flatten.2 ⟨sub c', List.mem_map.2 ⟨c', hc'm, rfl⟩, hlm⟩
        have hln : l ≠ n := fun e => (List.nodup_cons.1 hfl).1 (List.mem_append_right _ (e ▸ hlf))
        have hls : l ∉ sub c := fun hh =>
          (List.nodup_append.1 (List.nodup_cons.1 hfl).2).2.2 l hh l hlf rfl
        iintro ⟨%rl, %hrl, Ht⟩
        obtain ⟨rl', hrl', hdk⟩ := hkeep l rl hls hln hrl
        iexists rl'
        isplitr
        · ipureintro; exact hrl'
        iapply rtoks_move γ _ _ B B' hsub hnm' _ _ _ rl rl' hdk
        iexact Ht
      · simp only [ite_true]; exact .rfl
    · iapply bigSepL_emp_of
      · intro k x hx
        simp only [List.mem_of_getElem? hx, ite_true]
        exact .rfl
      iempintro



end own

end bbolt
end EtcdGrove
end Perennial
