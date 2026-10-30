/-
`node.spill`'s parts loop (`for _, node := range nodes`, after `n.split`): its invariant.

The parts `xs` of the node `n` (record `rc` at the split, its entries in chunks `chunks`, one
per part), under the parent `par` (null for a root that did not split). At iteration `j`: the
parts before `j` are written (`spilledN`, their pages `ps`, put into the parent), the others are
as at the split, possibly dereferenced (`dnK`); the parent's entries are its entries at the split
`ws0`, the one at `i0` (the node's) replaced by the written parts' (`parentWs`). Resources: the
written parts' trees (`pieceRes`, the last below the next part's first key, `hiAt`), the unwritten
parts' entries' trees (`chunkToks`), and the node's old page's token until it is freed.
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeSplit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The entries of the parts `xs` of the node `rc`. -/
def chunksOf (rc : NRec) (xs : List (Loc × node × List Inode)) : List (List WEntry) :=
  wsChunks rc.ws (xs.map (fun x => x.2.2.length))

/-- The upper bound of part `j`'s keys: the next part's first key, or the node's bound `hi`. -/
def hiAt (chs : List (List WEntry)) (hi : Option (List w8)) (j : Nat) : Option (List w8) :=
  match chs[j + 1]? with
  | some ch => some (wHead ch).key
  | none => hi

/-- The parent's entries after the parts `ps` were put into it (see the module doc). -/
def parentWs (ws0 : List WEntry) (i0 : Nat) (ps : List (w64 × List w8)) (ws : List WEntry) :
    Prop :=
  (ps = [] ∧ ws.map ownFresh = ws0.map ownFresh) ∨
  (ps ≠ [] ∧ ∃ es, pieceEntries ps es ∧
    ws.map ownFresh = (ws0.take i0 ++ es ++ ws0.drop (i0 + 1)).map ownFresh)


/-- A chunk: its length, its entries the node's. -/
theorem wsChunks_get (ws : List WEntry) :
    ∀ (ks : List Nat) (j k : Nat), ks[j]? = some k → ks.sum ≤ ws.length →
      ((wsChunks ws ks).getD j []).length = k ∧ ∀ w ∈ (wsChunks ws ks).getD j [], w ∈ ws
  | [], j, k, h, _ => by simp at h
  | k0 :: ks, 0, k, h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp only [List.sum_cons] at hs
    simp only [wsChunks, List.getD_cons_zero]
    refine ⟨by rw [List.length_take]; omega, fun w hw => List.mem_of_mem_take hw⟩
  | k0 :: ks, j + 1, k, h, hs => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.sum_cons] at hs
    simp only [wsChunks, List.getD_cons_succ]
    obtain ⟨h1, h2⟩ := wsChunks_get (ws.drop k0) ks j k h (by rw [List.length_drop]; omega)
    exact ⟨h1, fun w hw => List.mem_of_mem_drop (h2 w hw)⟩

theorem partRecs_get (r : NRec) (xs : List (Loc × node × List Inode)) (j : Nat)
    (x : Loc × node × List Inode) (hx : xs[j]? = some x) :
    (partRecs r xs)[j]? = some (partRec r j x ((chunksOf r xs).getD j [])) := by
  have hl : (chunksOf r xs).length = xs.length := by
    unfold chunksOf; rw [wsChunks_length, List.length_map]
  have hj : j < (chunksOf r xs).length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 hx).1
  have hc : (chunksOf r xs)[j]? = some ((chunksOf r xs).getD j []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  unfold partRecs
  rw [List.getElem?_map, List.getElem?_zipIdx]
  have hz : (xs.zip (wsChunks r.ws (xs.map (fun x => x.2.2.length))))[j]? =
      some (x, (chunksOf r xs).getD j []) := List.getElem?_zip_eq_some.2 ⟨hx, hc⟩
  rw [hz]; simp

theorem insertAll_get (ns : GMap Loc NRec) :
    ∀ (ls : List Loc) (rs : List NRec), ls.Nodup → ∀ (j : Nat) (l : Loc) (r : NRec),
      ls[j]? = some l → rs[j]? = some r → insertAll ns ls rs !! l = some r
  | [], _, _, j, l, r, h, _ => by simp at h
  | _ :: _, [], _, j, l, r, _, h => by simp at h
  | a :: ls, b :: rs, hnd, 0, l, r, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1; subst h2
    simp only [insertAll]; exact GMap.lookup_insert _ _ _
  | a :: ls, b :: rs, hnd, j + 1, l, r, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    simp only [insertAll]
    have hne : a ≠ l := by
      intro e; subst e; exact (List.nodup_cons.1 hnd).1 (List.mem_of_getElem? h1)
    rw [GMap.lookup_insert_ne _ _ hne]
    exact insertAll_get ns ls rs (List.nodup_cons.1 hnd).2 j l r h1 h2

/-- A parent chain kept by a map whose nodes keep their parents. -/
theorem upPath_par (ns ns' : GMap Loc NRec) {l : Loc} {p : List Loc} {t : Loc}
    (h : upPath ns l p t)
    (ha : ∀ x ∈ p, ∀ r, ns !! x = some r → ∃ r', ns' !! x = some r' ∧ r'.nv.parent' = r.nv.parent') :
    upPath ns' l p t := by
  induction h with
  | self l r hr hp =>
    obtain ⟨r', hr', he⟩ := ha l List.mem_cons_self r hr
    exact upPath.self l r' hr' (by rw [he]; exact hp)
  | up l r p t hr hp hu ih =>
    obtain ⟨r', hr', he⟩ := ha l List.mem_cons_self r hr
    have := ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    rw [← he] at this
    exact upPath.up l r' p t hr' (by rw [he]; exact hp) this

theorem upPath_last_mem (ns : GMap Loc NRec) {l : Loc} {p : List Loc} {t : Loc}
    (h : upPath ns l p t) : t ∈ p := by
  induction h with
  | self l r _ _ => exact List.mem_cons_self
  | up l r p t _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- A parent chain to a top `t` whose parent becomes the new top `pl`. -/
theorem upPath_ext (ns ns' : GMap Loc NRec) (pl : Loc) {l : Loc} {p : List Loc} {t : Loc}
    (h : upPath ns l p t) (hnd : p.Nodup)
    (ha : ∀ x ∈ p, x ≠ t → ∀ r, ns !! x = some r → ∃ r', ns' !! x = some r' ∧ r'.nv.parent' = r.nv.parent')
    (ht : ∃ rt', ns' !! t = some rt' ∧ rt'.nv.parent' = pl) (hpl : pl ≠ null)
    (hp : ∃ rp', ns' !! pl = some rp' ∧ rp'.nv.parent' = null) :
    upPath ns' l (p ++ [pl]) pl := by
  induction h with
  | self l r hr hpn =>
    obtain ⟨rt', hrt', he⟩ := ht
    obtain ⟨rp', hrp', hpe⟩ := hp
    have h1 : upPath ns' rt'.nv.parent' [pl] pl := by rw [he]; exact upPath.self pl rp' hrp' hpe
    exact upPath.up l rt' [pl] pl hrt' (by rw [he]; exact hpl) h1
  | up l r p t hr hpn hu ih =>
    have hlt : l ≠ t := by
      intro e; subst e
      exact (List.nodup_cons.1 hnd).1 (upPath_last_mem ns hu)
    obtain ⟨r', hr', he⟩ := ha l List.mem_cons_self hlt r hr
    have := ih (List.nodup_cons.1 hnd).2 (fun x hx hxt => ha x (List.mem_cons_of_mem _ hx) hxt) ht
    rw [← he] at this
    exact upPath.up l r' (p ++ [pl]) pl hr' (by rw [he]; exact hpn) this



/-- `ys` inserted into `S` (where `pl` is), or `S` unchanged without `pl`. -/
def graftR (pl : Loc) (ys : List Loc) (s s' : List Loc) : Prop :=
  (pl ∈ s → ∃ A C, s = A ++ C ∧ s' = A ++ ys ++ C) ∧ (pl ∉ s → s' = s)

theorem graftR_flatten (pl : Loc) (ys : List Loc) :
    ∀ (ss ss' : List (List Loc)), List.Forall₂ (graftR pl ys) ss ss' → ss.flatten.Nodup →
      graftR pl ys ss.flatten ss'.flatten
  | [], [], .nil, _ => ⟨fun h => by simp at h, fun _ => rfl⟩
  | s :: ss, s' :: ss', .cons hr hrs, hnd => by
    simp only [List.flatten_cons] at hnd ⊢
    have ih := graftR_flatten pl ys ss ss' hrs (List.nodup_append.1 hnd).2.1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_cases hs : pl ∈ s
      · obtain ⟨A, C, rfl, rfl⟩ := hr.1 hs
        have hn : pl ∉ ss.flatten := fun h' => (List.nodup_append.1 hnd).2.2 pl hs pl h' rfl
        rw [ih.2 hn]
        exact ⟨A, C ++ ss.flatten, by simp, by simp⟩
      · have hs' : pl ∈ ss.flatten := by
          rcases List.mem_append.1 h with h | h
          · exact absurd h hs
          · exact h
        obtain ⟨A, C, hA, hC⟩ := ih.1 hs'
        rw [hr.2 hs, hA, hC]
        exact ⟨s ++ A, C, by simp, by simp⟩
    · have hs : pl ∉ s := fun h' => h (List.mem_append_left _ h')
      have hs' : pl ∉ ss.flatten := fun h' => h (List.mem_append_right _ h')
      rw [hr.2 hs, ih.2 hs']

theorem nodup_graft (A C ys : List Loc) (h : (A ++ C).Nodup) (hy : ys.Nodup)
    (hd : ∀ y ∈ ys, y ∉ A ++ C) : (A ++ ys ++ C).Nodup := by
  have hp : (A ++ ys ++ C).Perm (ys ++ (A ++ C)) := by
    have := (List.perm_append_comm (l₁ := A) (l₂ := ys)).append_right C
    simpa [List.append_assoc] using this
  rw [hp.nodup_iff, List.nodup_append]
  exact ⟨hy, h, fun a ha b hb e => hd a ha (e ▸ hb)⟩

theorem kidsTree_leafP (ns : GMap Loc NRec) (c : Loc) (rc : NRec) (h : ns !! c = some rc)
    (hc : rc.cs = []) : kidsTree ns c [c] := by
  have := kidsTree.mk c rc [] h (by rw [hc]; exact List.Forall₂.nil) (by simp)
  simpa using this

theorem flatten_singletons : ∀ (ys : List Loc), (ys.map (fun y => [y])).flatten = ys
  | [] => rfl
  | y :: ys => by simp only [List.map_cons, List.flatten_cons, flatten_singletons ys]; rfl

theorem forall2_app {α β : Type} (R : α → β → Prop) :
    ∀ (a1 : List α) (b1 : List β) (a2 : List α) (b2 : List β), List.Forall₂ R a1 b1 →
      List.Forall₂ R a2 b2 → List.Forall₂ R (a1 ++ a2) (b1 ++ b2)
  | [], [], _, _, .nil, h => h
  | _ :: a1, _ :: b1, a2, b2, .cons h1 h2, h => .cons h1 (forall2_app R a1 b1 a2 b2 h2 h)

/-- Leaves `ys` appended to the children of `pl` in a tree: the tree with them. -/
theorem kidsTree_graft (ns ns' : GMap Loc NRec) (pl : Loc) (ys : List Loc)
    (hys : ∀ y ∈ ys, ∃ ry, ns' !! y = some ry ∧ ry.cs = []) (hyn : ys.Nodup) :
    ∀ (N : Nat) (t : Loc) (S : List Loc), S.length ≤ N → kidsTree ns t S →
      (∀ l ∈ S, l ≠ pl → ∀ r, ns !! l = some r → ∃ r', ns' !! l = some r' ∧ r'.cs = r.cs) →
      (pl ∈ S → ∀ r, ns !! pl = some r → ∃ r', ns' !! pl = some r' ∧ r'.cs = r.cs ++ ys) →
      (∀ y ∈ ys, y ∉ S) →
      ∃ S', kidsTree ns' t S' ∧ graftR pl ys S S' := by
  intro N
  induction N with
  | zero =>
    intro t S hl hk
    cases hk with
    | mk _ _ _ _ _ _ => simp at hl
  | succ N ih =>
    intro t S hl hk hag hpl hfr
    cases hk with
    | mk _ r subs hr hF hnd =>
      have hsub : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
          ss.flatten.length ≤ N → (∀ l ∈ ss.flatten, l ∈ t :: subs.flatten) →
          ∃ ss', List.Forall₂ (kidsTree ns') cs ss' ∧ List.Forall₂ (graftR pl ys) ss ss' := by
        intro cs ss hF2
        induction hF2 with
        | nil => intro _ _; exact ⟨[], .nil, .nil⟩
        | @cons c s cs' ss' hk2 _ ih2 =>
          intro hlen hin
          simp only [List.flatten_cons, List.length_append] at hlen
          have hin1 : ∀ l ∈ s, l ∈ t :: subs.flatten := fun l h => hin l (by simp [h])
          have hin2 : ∀ l ∈ ss'.flatten, l ∈ t :: subs.flatten :=
            fun l h => hin l (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr h)
          obtain ⟨s2, hk3, hg3⟩ := ih c s (by omega) hk2 (fun l hl hne => hag l (hin1 l hl) hne)
            (fun h => hpl (hin1 pl h)) (fun y hy hys' => hfr y hy (hin1 y hys'))
          obtain ⟨ss2, hF3, hG3⟩ := ih2 (by omega) hin2
          exact ⟨s2 :: ss2, .cons hk3 hF3, .cons hg3 hG3⟩
      obtain ⟨ss', hF', hG'⟩ := hsub r.cs subs hF (by simp only [List.length_cons] at hl; omega)
        (fun l h => List.mem_cons_of_mem _ h)
      have hfl := graftR_flatten pl ys subs ss' hG' (List.nodup_cons.1 hnd).2
      have hfrS : ∀ y ∈ ys, y ∉ t :: subs.flatten := hfr
      by_cases ht : t = pl
      · subst ht
        obtain ⟨r', hr', hcs'⟩ := hpl List.mem_cons_self r hr
        have hno : t ∉ subs.flatten := (List.nodup_cons.1 hnd).1
        have hss : ss'.flatten = subs.flatten := hfl.2 hno
        have hleaf : List.Forall₂ (kidsTree ns') ys (ys.map (fun y => [y])) := by
          have : ∀ (l : List Loc), (∀ y ∈ l, ∃ ry, ns' !! y = some ry ∧ ry.cs = []) →
              List.Forall₂ (kidsTree ns') l (l.map (fun y => [y])) := by
            intro l hl
            induction l with
            | nil => exact .nil
            | cons y l ihl =>
              obtain ⟨ry, hry, hc⟩ := hl y List.mem_cons_self
              exact .cons (kidsTree_leafP ns' y ry hry hc) (ihl (fun z hz => hl z (List.mem_cons_of_mem _ hz)))
          exact this ys hys
        have hflat : (ss' ++ ys.map (fun y => [y])).flatten = subs.flatten ++ ys := by
          rw [List.flatten_append, hss, flatten_singletons]
        have hnd' : (t :: (ss' ++ ys.map (fun y => [y])).flatten).Nodup := by
          rw [hflat, ← List.cons_append]
          have := nodup_graft (t :: subs.flatten) [] ys (by simpa using hnd) hyn (by simpa using hfrS)
          simpa using this
        refine ⟨t :: (ss' ++ ys.map (fun y => [y])).flatten, kidsTree.mk t r' _ hr' ?_ hnd', ?_, ?_⟩
        · rw [hcs']; exact forall2_app _ _ _ _ _ hF' hleaf
        · intro _
          exact ⟨t :: subs.flatten, [], by simp, by rw [hflat]; simp⟩
        · intro h; exact absurd List.mem_cons_self h
      · obtain ⟨r', hr', hcs'⟩ := hag t List.mem_cons_self ht r hr
        have hS' : graftR pl ys (t :: subs.flatten) (t :: ss'.flatten) := by
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have h' : pl ∈ subs.flatten := by
              rcases List.mem_cons.1 h with h | h
              · exact absurd h.symm ht
              · exact h
            obtain ⟨A, C, hA, hC⟩ := hfl.1 h'
            exact ⟨t :: A, C, by rw [hA]; rfl, by rw [hC]; rfl⟩
          · have h' : pl ∉ subs.flatten := fun h2 => h (List.mem_cons_of_mem _ h2)
            rw [hfl.2 h']
        have hnd' : (t :: ss'.flatten).Nodup := by
          by_cases hp : pl ∈ t :: subs.flatten
          · obtain ⟨A, C, hA, hC⟩ := hS'.1 hp
            rw [hC]
            exact nodup_graft A C ys (hA ▸ hnd) hyn (fun y hy => hA ▸ hfrS y hy)
          · rw [hS'.2 hp]; exact hnd
        exact ⟨t :: ss'.flatten, kidsTree.mk t r' ss' hr' (by rw [hcs']; exact hF') hnd', hS'⟩


theorem upPath_dom (ns : GMap Loc NRec) {l : Loc} {p : List Loc} {t : Loc} (h : upPath ns l p t) :
    ∀ x ∈ p, (ns !! x).isSome := by
  induction h with
  | self l r hr _ => intro x hx; rw [List.mem_singleton] at hx; subst hx; rw [hr]; rfl
  | up l r p t hr _ _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hr]; rfl
    · exact ih x hx

/-- The parts' records after the split (see `splitNs`): lookups. -/
theorem splitNs_part (ns : GMap Loc NRec) (r rp : NRec) (xs : List (Loc × node × List Inode))
    (pl : Loc) (pv' : node) (pcs' : List Loc) (hnd : (xs.map (fun x => x.1)).Nodup) (j : Nat)
    (x : Loc × node × List Inode) (hx : xs[j]? = some x) :
    splitNs ns r rp xs pl pv' pcs' !! x.1 = some (partRec r j x ((chunksOf r xs).getD j [])) := by
  unfold splitNs
  exact insertAll_get _ _ _ hnd j x.1 _ (by rw [List.getElem?_map, hx]; rfl) (partRecs_get r xs j x hx)

theorem splitNs_par (ns : GMap Loc NRec) (r rp : NRec) (xs : List (Loc × node × List Inode))
    (pl : Loc) (pv' : node) (pcs' : List Loc) (hpl : pl ∉ xs.map (fun x => x.1)) :
    splitNs ns r rp xs pl pv' pcs' !! pl = some (parentRec r rp pv' pcs') := by
  unfold splitNs
  rw [insertAll_notin _ _ _ _ hpl, GMap.lookup_insert]

theorem splitNs_other (ns : GMap Loc NRec) (r rp : NRec) (xs : List (Loc × node × List Inode))
    (pl : Loc) (pv' : node) (pcs' : List Loc) (l : Loc) (hl : l ∉ xs.map (fun x => x.1)) (hlp : l ≠ pl) :
    splitNs ns r rp xs pl pv' pcs' !! l = ns !! l := by
  unfold splitNs
  rw [insertAll_notin _ _ _ _ hl, GMap.lookup_insert_ne _ _ (Ne.symm hlp)]

/-- The split's parts: each a node `dereference` can read. -/
theorem partRec_ok (bl n pl : Loc) (rc : NRec) (xs : List (Loc × node × List Inode))
    (hdok : derefOK bl rc) (hsp : splitPieces n rc.nv pl rc.ins xs) (j : Nat)
    (x : Loc × node × List Inode) (hx : xs[j]? = some x) :
    derefOK bl (partRec rc j x ((chunksOf rc xs).getD j [])) ∧
      (rc.cs = [] → (partRec rc j x ((chunksOf rc xs).getD j [])).cs = []) ∧
      (partRec rc j x ((chunksOf rc xs).getD j [])).nv.parent' = pl := by
  obtain ⟨hflat, ⟨x0, rest, hxs, hx0n, hx0v, hrest⟩, -⟩ := hsp
  obtain ⟨hbl, hlen, hws, hkey⟩ := hdok
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [← hlen, ← hflat, List.length_flatten, List.map_map]; exact Nat.le_refl _
  obtain ⟨hcl, hcm⟩ := wsChunks_get rc.ws (xs.map (fun x => x.2.2.length)) j x.2.2.length
    (by rw [List.getElem?_map, hx]; rfl) hsum
  unfold chunksOf
  unfold partRec
  by_cases hj : j = 0
  · subst hj
    rw [hxs] at hx; simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
    rw [if_pos rfl]
    simp only
    have hb : x0.2.1.bucket' = rc.nv.bucket' := by rw [hx0v]
    have hk : x0.2.1.key' = rc.nv.key' := by rw [hx0v]
    have hpg : x0.2.1.pgid' = rc.nv.pgid' := by rw [hx0v]
    have hpa : x0.2.1.parent' = pl := by rw [hx0v]
    refine ⟨⟨by rw [hb]; exact hbl, by rw [hcl], fun w hw => hws w (hcm w hw), ?_⟩, fun h => h, hpa⟩
    rw [hk, hpg]; exact hkey
  · rw [if_neg hj]
    have hxr : x ∈ rest := by
      rw [hxs] at hx
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getElem?_cons_succ] at hx
      exact List.mem_of_getElem? hx
    obtain ⟨-, hv⟩ := hrest x hxr
    have hb : x.2.1.bucket' = rc.nv.bucket' := by rw [hv]
    have hk : x.2.1.key' = slice.nil := by rw [hv]; rfl
    have hpa : x.2.1.parent' = pl := by rw [hv]
    exact ⟨⟨by rw [hb]; exact hbl, by rw [hcl], fun w hw => hws w (hcm w hw), Or.inl hk⟩, fun _ => rfl, hpa⟩






/-- The bucket's live nodes after the split: its tree with the parts (under the old parent, or
the new top). -/
theorem split_live (bl n pl : Loc) (B : BRec) (rc rp : NRec) (xs : List (Loc × node × List Inode))
    (pv' : node) (pcs' : List Loc)
    (hn : B.ns !! n = some rc) (hcs : rc.cs = []) (hdok : derefOK bl rc)
    (hsp : splitPieces n rc.nv pl rc.ins xs) (hpl0 : pl ≠ null)
    (hcase : (rc.nv.parent' = null ∧ pv' = newParent rc.nv pv'.children' ∧ pcs' = xs.map (fun x => x.1)) ∨
      (rc.nv.parent' ≠ null ∧ pl = rc.nv.parent' ∧ pv' = { rp.nv with children' := pv'.children' } ∧
        pcs' = rp.cs ++ (xs.drop 1).map (fun x => x.1)))
    (hfr : splitFresh B n xs pl rc.nv.parent')
    (hrp : rc.nv.parent' ≠ null → B.ns !! rc.nv.parent' = some rp)
    (hlive : ∃ S, liveNodesX B S ∧ (∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧
      (rc.nv.parent' ≠ null → n ∈ S ∧ rc.nv.parent' ∈ S) ∧
      (rc.nv.parent' = null → ∃ p, upPath B.ns B.bv.rootNode' p n) ∧
      (∀ l r, B.ns !! l = some r → l ∉ S → noViewRec r)) :
    ∃ S', liveNodesX { B with ns := splitNs B.ns rc rp xs pl pv' pcs' } S' ∧
      (∀ l ∈ S', ∃ r, (splitNs B.ns rc rp xs pl pv' pcs') !! l = some r ∧ derefOK bl r) ∧
      (∀ x ∈ xs, x.1 ∈ S') ∧ pl ∈ S' ∧
      (∀ l r, (splitNs B.ns rc rp xs pl pv' pcs') !! l = some r → l ∉ S' → noViewRec r) := by
  obtain ⟨hfx, hfpl, hplids, hnd⟩ := hfr
  obtain ⟨S, ⟨p, top, hu, hpnd, hk, hq⟩, hSok, hSin, hSroot, hSnv⟩ := hlive
  have hsp' := hsp
  obtain ⟨-, ⟨x0, rest, hxs, hx0n, -, -⟩, -⟩ := hsp'
  have hnids : n ∈ xs.map (fun x => x.1) := by rw [hxs, ← hx0n]; exact List.mem_cons_self
  -- a node of `B` that is not the split node is no part
  have hnotpart : ∀ l, (B.ns !! l).isSome → l ≠ n → l ∉ xs.map (fun x => x.1) := by
    intro l hl hln hmem
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hmem
    rw [hfx x hx hln] at hl; cases hl
  have hpart : ∀ x ∈ xs, ∃ j, xs[j]? = some x := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx; exact ⟨j, List.getElem?_eq_getElem hj⟩
  have hn0 : xs[0]? = some x0 := by rw [hxs]; rfl
  have hnrec : splitNs B.ns rc rp xs pl pv' pcs' !! n = some (partRec rc 0 x0 ((chunksOf rc xs).getD 0 [])) := by
    have := splitNs_part B.ns rc rp xs pl pv' pcs' hnd 0 x0 hn0; rwa [hx0n] at this
  obtain ⟨hok0, hcs0, hpa0⟩ := partRec_ok bl n pl rc xs hdok hsp 0 x0 hn0
  have hpartok : ∀ x ∈ xs, ∃ r, splitNs B.ns rc rp xs pl pv' pcs' !! x.1 = some r ∧ derefOK bl r ∧ r.cs = [] := by
    intro x hx
    obtain ⟨j, hj⟩ := hpart x hx
    obtain ⟨h1, h2, -⟩ := partRec_ok bl n pl rc xs hdok hsp j x hj
    exact ⟨_, splitNs_part B.ns rc rp xs pl pv' pcs' hnd j x hj, h1, h2 hcs⟩
  rcases hcase with ⟨hpn, hpv, hpcs⟩ | ⟨hpn, hpleq, hpv, hpcs⟩
  · -- a root split: the new top `pl` over the parts
    subst hpcs
    obtain ⟨p1, hu1⟩ := hSroot hpn
    obtain ⟨hp1, ht1⟩ := upPath_det B.ns hu hu1
    subst hp1
    rw [ht1] at hu hk
    have hSn : S = [n] :=
      kidsTree_det B.ns S.length n S [n] (Nat.le_refl _) hk (kidsTree_leafP B.ns n rc hn hcs)
    have hplB : B.ns !! pl = none := hfpl hpn
    have hprec : splitNs B.ns rc rp xs pl pv' (xs.map (fun x => x.1)) !! pl =
        some ⟨pv', [], [], xs.map (fun x => x.1), [], Src.own (DFrac.own 1)⟩ := by
      rw [splitNs_par _ _ _ _ _ _ _ hplids]; unfold parentRec; rw [if_pos hpn]
    have hpp : pv'.parent' = null := by rw [hpv]; rfl
    refine ⟨pl :: xs.map (fun x => x.1), ⟨p ++ [pl], pl, ?_, ?_, ?_, ?_⟩, ?_,
      fun x hx => List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩), List.mem_cons_self, ?_⟩
    · apply upPath_ext B.ns _ pl hu hpnd
      · intro x hx hxt r hr
        have hxi := hnotpart x (by rw [hr]; rfl) hxt
        have hxp : x ≠ pl := by intro e; subst e; rw [hplB] at hr; cases hr
        exact ⟨r, by rw [splitNs_other _ _ _ _ _ _ _ x hxi hxp]; exact hr, rfl⟩
      · exact ⟨_, hnrec, hpa0⟩
      · exact hpl0
      · exact ⟨_, hprec, hpp⟩
    · rw [List.nodup_append]
      refine ⟨hpnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb e => ?_⟩
      rw [List.mem_singleton] at hb; subst hb; subst e
      have := upPath_dom B.ns hu a ha; rw [hplB] at this; cases this
    · have hF : List.Forall₂ (kidsTree (splitNs B.ns rc rp xs pl pv' (xs.map (fun x => x.1)))) (xs.map (fun x => x.1))
          ((xs.map (fun x => x.1)).map (fun y => [y])) := by
        have : ∀ (l : List (Loc × node × List Inode)), (∀ x ∈ l, x ∈ xs) →
            List.Forall₂ (kidsTree (splitNs B.ns rc rp xs pl pv' (xs.map (fun x => x.1)))) (l.map (fun x => x.1))
              ((l.map (fun x => x.1)).map (fun y => [y])) := by
          intro l hl
          induction l with
          | nil => exact .nil
          | cons x l ihl =>
            obtain ⟨r, hr, -, hc⟩ := hpartok x (hl x List.mem_cons_self)
            exact .cons (kidsTree_leafP _ x.1 r hr hc) (ihl (fun z hz => hl z (List.mem_cons_of_mem _ hz)))
        exact this xs (fun x hx => hx)
      have := kidsTree.mk pl ⟨pv', [], [], xs.map (fun x => x.1), [], Src.own (DFrac.own 1)⟩ _ hprec hF
        (by rw [flatten_singletons]; exact List.nodup_cons.2 ⟨hplids, hnd⟩)
      rw [flatten_singletons] at this
      exact this
    · intro l hl hlS
      rcases List.mem_append.1 hl with hl | hl
      · have hln : l ≠ n := fun e => hlS (List.mem_cons_of_mem _ (e ▸ hnids))
        have hlS0 : l ∉ S := by rw [hSn]; simpa using hln
        obtain ⟨r, hr, hv⟩ := hq l hl hlS0
        have hxp : l ≠ pl := by intro e; subst e; rw [hplB] at hr; cases hr
        exact ⟨r, by rw [splitNs_other _ _ _ _ _ _ _ l (hnotpart l (by rw [hr]; rfl) hln) hxp]; exact hr, hv⟩
      · rw [List.mem_singleton] at hl; exact absurd (hl ▸ List.mem_cons_self) hlS
    · intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · refine ⟨_, hprec, ?_, rfl, fun w hw => by simp at hw, Or.inl ?_⟩
        · show pv'.bucket' = bl; rw [hpv]; exact hdok.1
        · show pv'.key' = slice.nil; rw [hpv]; rfl
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
        obtain ⟨r, hr, hok, -⟩ := hpartok x hx
        exact ⟨r, hr, hok⟩
    · intro l r hl hlS
      have hln : l ∉ xs.map (fun x => x.1) := fun h => hlS (List.mem_cons_of_mem _ h)
      have hlp : l ≠ pl := fun e => hlS (e ▸ List.mem_cons_self)
      rw [splitNs_other _ _ _ _ _ _ _ l hln hlp] at hl
      exact hSnv l r hl (by rw [hSn]; simp only [List.mem_singleton]; exact fun e => hln (e ▸ hnids))
  · -- the old parent: the new parts appended to its children
    subst hpleq
    subst hpcs
    obtain ⟨hnS, hplS⟩ := hSin hpn
    have hrp' := hrp hpn
    obtain ⟨r1, hr1, hrpok⟩ := hSok _ hplS
    rw [hrp'] at hr1; cases hr1
    have hrest : (xs.drop 1).map (fun x => x.1) = rest.map (fun x => x.1) := by rw [hxs]; rfl
    have hndr : (rest.map (fun x => x.1)).Nodup := by
      have := hnd; rw [hxs, List.map_cons] at this; exact (List.nodup_cons.1 this).2
    have hrn : ∀ x ∈ rest, x.1 ≠ n := by
      intro x hx e
      have := hnd; rw [hxs, List.map_cons] at this
      exact (List.nodup_cons.1 this).1 (by rw [hx0n, ← e]; exact List.mem_map.2 ⟨x, hx, rfl⟩)
    have hprec : splitNs B.ns rc rp xs rc.nv.parent' pv' (rp.cs ++ (xs.drop 1).map (fun x => x.1)) !! rc.nv.parent' =
        some { rp with nv := pv', cs := rp.cs ++ (xs.drop 1).map (fun x => x.1) } := by
      rw [splitNs_par _ _ _ _ _ _ _ hplids]; unfold parentRec; rw [if_neg hpn]
    have hys : ∀ y ∈ (xs.drop 1).map (fun x => x.1), ∃ ry,
        splitNs B.ns rc rp xs rc.nv.parent' pv' (rp.cs ++ (xs.drop 1).map (fun x => x.1)) !! y = some ry ∧ ry.cs = [] := by
      intro y hy
      rw [hrest] at hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨r, hr, -, hc⟩ := hpartok x (by rw [hxs]; exact List.mem_cons_of_mem _ hx)
      exact ⟨r, hr, hc⟩
    have hySn : ∀ y ∈ (xs.drop 1).map (fun x => x.1), y ∉ S := by
      intro y hy hyS
      rw [hrest] at hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨r, hr, -⟩ := hSok _ hyS
      rw [hfx x (by rw [hxs]; exact List.mem_cons_of_mem _ hx) (hrn x hx)] at hr; cases hr
    obtain ⟨S', hk', hg'⟩ := kidsTree_graft B.ns _ rc.nv.parent' ((xs.drop 1).map (fun x => x.1)) hys
      (by rw [hrest]; exact hndr) S.length top S (Nat.le_refl _) hk
      (by
        intro l hl hlp r hr
        by_cases hln : l = n
        · subst hln; rw [hn] at hr; cases hr
          exact ⟨_, hnrec, by rw [hcs0 hcs, hcs]⟩
        · exact ⟨r, by rw [splitNs_other _ _ _ _ _ _ _ l (hnotpart l (by rw [hr]; rfl) hln) hlp]; exact hr, rfl⟩)
      (by
        intro _ r hr
        rw [hrp'] at hr; cases hr
        exact ⟨_, hprec, rfl⟩)
      hySn
    obtain ⟨A, C, hA, hC⟩ := hg'.1 hplS
    have hSS : ∀ l ∈ S, l ∈ S' := by
      intro l hl; rw [hA] at hl; rw [hC]
      rcases List.mem_append.1 hl with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h
    have hpv1 : pv'.parent' = rp.nv.parent' := by rw [hpv]
    have hxs' : ∀ x ∈ xs, x.1 ∈ S' := by
      intro x hx
      rw [hxs] at hx
      rcases List.mem_cons.1 hx with h | hx
      · rw [h, hx0n]; exact hSS _ hnS
      · rw [hC]
        exact List.mem_append_left _ (List.mem_append_right _ (by rw [hrest]; exact List.mem_map.2 ⟨x, hx, rfl⟩))
    refine ⟨S', ⟨p, top, ?_, hpnd, hk', ?_⟩, ?_, hxs', hSS _ hplS, ?_⟩
    · apply upPath_par B.ns _ hu
      intro x hx r hr
      by_cases hxn : x = n
      · subst hxn; rw [hn] at hr; cases hr; exact ⟨_, hnrec, hpa0⟩
      · by_cases hxp : x = rc.nv.parent'
        · rw [hxp] at hr ⊢; rw [hrp'] at hr; cases hr; exact ⟨_, hprec, hpv1⟩
        · exact ⟨r, by rw [splitNs_other _ _ _ _ _ _ _ x (hnotpart x (by rw [hr]; rfl) hxn) hxp]; exact hr, rfl⟩
    · intro l hl hlS'
      have hlS : l ∉ S := fun h => hlS' (hSS l h)
      obtain ⟨r, hr, hv⟩ := hq l hl hlS
      have hln : l ≠ n := fun e => hlS (e ▸ hnS)
      have hlp : l ≠ rc.nv.parent' := fun e => hlS (e ▸ hplS)
      exact ⟨r, by rw [splitNs_other _ _ _ _ _ _ _ l (hnotpart l (by rw [hr]; rfl) hln) hlp]; exact hr, hv⟩
    · intro l hl
      have hl' : l ∈ (xs.drop 1).map (fun x => x.1) ∨ l ∈ S := by
        rw [hC] at hl; rw [hA]
        rcases List.mem_append.1 hl with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inr (List.mem_append_left _ h)
          · exact Or.inl h
        · exact Or.inr (List.mem_append_right _ h)
      rcases hl' with hy | hlS
      · rw [hrest] at hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        obtain ⟨r, hr, hok, -⟩ := hpartok x (by rw [hxs]; exact List.mem_cons_of_mem _ hx)
        exact ⟨r, hr, hok⟩
      · by_cases hln : l = n
        · subst hln; exact ⟨_, hnrec, hok0⟩
        · by_cases hlp : l = rc.nv.parent'
          · rw [hlp]
            refine ⟨_, hprec, ?_⟩
            obtain ⟨o1, o2, o3, o4⟩ := hrpok
            have hb : pv'.bucket' = rp.nv.bucket' := by rw [hpv]
            have hk2 : pv'.key' = rp.nv.key' := by rw [hpv]
            have hpg2 : pv'.pgid' = rp.nv.pgid' := by rw [hpv]
            refine ⟨by show pv'.bucket' = bl; rw [hb]; exact o1, o2, o3, ?_⟩
            show pv'.key' = slice.nil ∨ (rp.ksrc ≠ Src.stale ∧ (pv'.pgid' = W64 0 ∨ 0 < rp.key.length))
            rw [hk2, hpg2]; exact o4
          · obtain ⟨r, hr, hok⟩ := hSok l hlS
            exact ⟨r, by rw [splitNs_other _ _ _ _ _ _ _ l (hnotpart l (by rw [hr]; rfl) hln) hlp]; exact hr, hok⟩


    · intro l r hl hlS
      have hln : l ∉ xs.map (fun x => x.1) := fun h => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h; exact hlS (hxs' x hx)
      have hlp : l ≠ rc.nv.parent' := fun e => hlS (e ▸ hSS _ hplS)
      rw [splitNs_other _ _ _ _ _ _ _ l hln hlp] at hl
      exact hSnv l r hl (fun h => hlS (hSS l h))
/-- `ys` (right after `pl`) cut from `S`, or `S` unchanged without `pl`. -/
def pruneR (pl : Loc) (ys : List Loc) (s s' : List Loc) : Prop :=
  (pl ∈ s → ∃ A C, s = A ++ pl :: ys ++ C ∧ s' = A ++ pl :: C) ∧ (pl ∉ s → s' = s)

theorem pruneR_flatten (pl : Loc) (ys : List Loc) :
    ∀ (ss ss' : List (List Loc)), List.Forall₂ (pruneR pl ys) ss ss' → ss.flatten.Nodup →
      pruneR pl ys ss.flatten ss'.flatten
  | [], [], .nil, _ => ⟨fun h => by simp at h, fun _ => rfl⟩
  | s :: ss, s' :: ss', .cons hr hrs, hnd => by
    simp only [List.flatten_cons] at hnd ⊢
    have ih := pruneR_flatten pl ys ss ss' hrs (List.nodup_append.1 hnd).2.1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_cases hs : pl ∈ s
      · obtain ⟨A, C, rfl, rfl⟩ := hr.1 hs
        have hn : pl ∉ ss.flatten := fun h' => (List.nodup_append.1 hnd).2.2 pl hs pl h' rfl
        rw [ih.2 hn]
        exact ⟨A, C ++ ss.flatten, by simp, by simp⟩
      · have hs' : pl ∈ ss.flatten := by
          rcases List.mem_append.1 h with h | h
          · exact absurd h hs
          · exact h
        obtain ⟨A, C, hA, hC⟩ := ih.1 hs'
        rw [hr.2 hs, hA, hC]
        exact ⟨s ++ A, C, by simp, by simp⟩
    · have hs : pl ∉ s := fun h' => h (List.mem_append_left _ h')
      have hs' : pl ∉ ss.flatten := fun h' => h (List.mem_append_right _ h')
      rw [hr.2 hs, ih.2 hs']

/-- In a list of disjoint lists, a common element means the same list. -/
theorem flatten_same {α : Type} : ∀ (L : List (List α)), L.flatten.Nodup → ∀ (l1 l2 : List α) (a : α),
    l1 ∈ L → l2 ∈ L → a ∈ l1 → a ∈ l2 → l1 = l2
  | [], _, _, _, _, h, _, _, _ => by simp at h
  | s :: L, hnd, l1, l2, a, h1, h2, ha1, ha2 => by
    simp only [List.flatten_cons] at hnd
    obtain ⟨-, hndL, hdis⟩ := List.nodup_append.1 hnd
    by_cases e1 : l1 = s <;> by_cases e2 : l2 = s
    · rw [e1, e2]
    · have h2' : l2 ∈ L := (List.mem_cons.1 h2).resolve_left e2
      subst e1; exact absurd rfl (hdis a ha1 a (List.mem_flatten.2 ⟨l2, h2', ha2⟩))
    · have h1' : l1 ∈ L := (List.mem_cons.1 h1).resolve_left e1
      subst e2; exact absurd rfl (hdis a ha2 a (List.mem_flatten.2 ⟨l1, h1', ha1⟩))
    · exact flatten_same L hndL l1 l2 a ((List.mem_cons.1 h1).resolve_left e1)
        ((List.mem_cons.1 h2).resolve_left e2) ha1 ha2

theorem flatten_singletonsC : ∀ (ys : List Loc), (ys.map (fun y => [y])).flatten = ys
  | [] => rfl
  | y :: ys => by simp only [List.map_cons, List.flatten_cons, flatten_singletonsC ys]; rfl

theorem kidsTree_leafC (ns : GMap Loc NRec) (c : Loc) (rc : NRec) (h : ns !! c = some rc)
    (hc : rc.cs = []) : kidsTree ns c [c] := by
  have := kidsTree.mk c rc [] h (by rw [hc]; exact List.Forall₂.nil) (by simp)
  simpa using this

/-- Leaf children's trees are the leaves alone. -/
theorem leaves_subs (ns : GMap Loc NRec) :
    ∀ (ys : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) ys ss →
      (∀ y ∈ ys, ∃ ry, ns !! y = some ry ∧ ry.cs = []) → ss = ys.map (fun y => [y])
  | [], [], .nil, _ => rfl
  | y :: ys, s :: ss, .cons hk hrs, hl => by
    obtain ⟨ry, hry, hc⟩ := hl y List.mem_cons_self
    have e := kidsTree_det ns s.length y s [y] (Nat.le_refl _) hk (kidsTree_leafC ns y ry hry hc)
    simp only [List.map_cons, e, leaves_subs ns ys ss hrs (fun z hz => hl z (List.mem_cons_of_mem _ hz))]

theorem forall2_get_C {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), List.Forall₂ R l1 l2 → ∀ (k : Nat) (a : α), l1[k]? = some a →
      ∃ b, l2[k]? = some b ∧ R a b
  | [], [], _, _, _, h => by simp at h
  | a :: l1, b :: l2, .cons hr hrs, 0, a', h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨b, rfl, hr⟩
  | a :: l1, b :: l2, .cons _ hrs, k + 1, a', h => by
    simp only [List.getElem?_cons_succ] at h ⊢; exact forall2_get_C R l1 l2 hrs k a' h

theorem forall2_get_r_C {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), List.Forall₂ R l1 l2 → ∀ (k : Nat) (b : β), l2[k]? = some b →
      ∃ a, l1[k]? = some a ∧ R a b
  | [], [], _, _, _, h => by simp at h
  | a :: l1, b :: l2, .cons hr hrs, 0, b', h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨a, rfl, hr⟩
  | a :: l1, b :: l2, .cons _ hrs, k + 1, b', h => by
    simp only [List.getElem?_cons_succ] at h ⊢; exact forall2_get_r_C R l1 l2 hrs k b' h

/-- A tree's members are nodes, and hold their children. -/
theorem kidsTree_memC (ns : GMap Loc NRec) :
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
        obtain ⟨s, hs, hcs⟩ := forall2_get_C _ r.cs subs hF k c (by rw [← hkc]; exact List.getElem?_eq_getElem hk)
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, List.mem_of_getElem? hs, kidsTree_head ns c s hcs⟩)
      · exact key r.cs subs hF (by simp only [List.length_cons] at hl; omega) (fun c h => by
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
          obtain ⟨s, hs, hcs⟩ := forall2_get_C _ r.cs subs hF k _ (List.getElem?_eq_getElem hk)
          exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, List.mem_of_getElem? hs, kidsTree_head ns _ s hcs⟩))
          (fun y h => h) x hx

/-- The leaf children `ys` of `pl` cut from a tree (`pl` now childless). -/
theorem kidsTree_prune (ns ns' : GMap Loc NRec) (pl : Loc) (ys : List Loc)
    (hys : ∀ y ∈ ys, ∃ ry, ns !! y = some ry ∧ ry.cs = [])
    (hplc : ∀ r, ns !! pl = some r → r.cs = ys) :
    ∀ (N : Nat) (t : Loc) (S : List Loc), S.length ≤ N → kidsTree ns t S →
      (∀ l ∈ S, l ≠ pl → l ∉ ys → ∀ r, ns !! l = some r → ∃ r', ns' !! l = some r' ∧ r'.cs = r.cs) →
      (pl ∈ S → ∃ r', ns' !! pl = some r' ∧ r'.cs = []) →
      (pl ∉ S → ∀ y ∈ ys, y ∉ S) →
      ∃ S', kidsTree ns' t S' ∧ pruneR pl ys S S' := by
  intro N
  induction N with
  | zero =>
    intro t S hl hk
    cases hk with
    | mk _ _ _ _ _ _ => simp at hl
  | succ N ih =>
    intro t S hl hk hag hpl hout
    cases hk with
    | mk _ r subs hr hF hnd =>
      by_cases ht : t = pl
      · subst ht
        have hrc := hplc r hr
        rw [hrc] at hF
        have hss := leaves_subs ns ys subs hF hys
        obtain ⟨r', hr', hcs'⟩ := hpl List.mem_cons_self
        refine ⟨[t], kidsTree_leafC ns' t r' hr' hcs', fun _ => ⟨[], [], ?_, rfl⟩, fun h => absurd List.mem_cons_self h⟩
        rw [hss, flatten_singletonsC]; simp
      · -- `t ∈ ys` is a leaf alone, without `pl`
        have htys : t ∉ ys := by
          intro hty
          obtain ⟨ry, hry, hc⟩ := hys t hty
          rw [hr] at hry; cases hry
          rw [hc] at hF
          cases hF
          have hpS : pl ∉ t :: ([] : List (List Loc)).flatten := by simp; exact fun e => ht e.symm
          exact hout hpS t hty List.mem_cons_self
        obtain ⟨r', hr', hcs'⟩ := hag t List.mem_cons_self ht htys r hr
        -- `ys` lie in the child tree with `pl`
        have hco : ∀ y ∈ ys, ∀ s ∈ subs, y ∈ s → pl ∈ s := by
          intro y hy s hs hys1
          by_cases hpS : pl ∈ t :: subs.flatten
          · have hp2 : pl ∈ subs.flatten := by
              rcases List.mem_cons.1 hpS with h | h
              · exact absurd h.symm ht
              · exact h
            obtain ⟨s2, hs2, hp2s⟩ := List.mem_flatten.1 hp2
            obtain ⟨k, hk, hks⟩ := List.getElem_of_mem hs2
            obtain ⟨c2, hc2, hk2⟩ := forall2_get_r_C _ r.cs subs hF k s2 (by rw [← hks]; exact List.getElem?_eq_getElem hk)
            obtain ⟨rp, hrp, hkids⟩ := kidsTree_memC ns s2.length c2 s2 (Nat.le_refl _) hk2 pl hp2s
            have hy2 : y ∈ s2 := hkids y (by rw [hplc rp hrp]; exact hy)
            rw [flatten_same subs (List.nodup_cons.1 hnd).2 s s2 y hs hs2 hys1 hy2]; exact hp2s
          · exact absurd (List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, hs, hys1⟩)) (hout hpS y hy)
        have hsub : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
            ss.flatten.length ≤ N → (∀ s ∈ ss, s ∈ subs) →
            ∃ ss', List.Forall₂ (kidsTree ns') cs ss' ∧ List.Forall₂ (pruneR pl ys) ss ss' := by
          intro cs ss hF2
          induction hF2 with
          | nil => intro _ _; exact ⟨[], .nil, .nil⟩
          | @cons c s cs' ss' hk2 _ ih2 =>
            intro hlen hin
            simp only [List.flatten_cons, List.length_append] at hlen
            have hsS : s ∈ subs := hin s List.mem_cons_self
            have hin1 : ∀ l ∈ s, l ∈ t :: subs.flatten := fun l h =>
              List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨s, hsS, h⟩)
            obtain ⟨s2, hk3, hg3⟩ := ih c s (by omega) hk2 (fun l hl hne hny => hag l (hin1 l hl) hne hny)
              (fun h => hpl (hin1 pl h)) (fun hp y hy hyS => hp (hco y hy s hsS hyS))
            obtain ⟨ss2, hF3, hG3⟩ := ih2 (by omega) (fun s' h => hin s' (List.mem_cons_of_mem _ h))
            exact ⟨s2 :: ss2, .cons hk3 hF3, .cons hg3 hG3⟩
        obtain ⟨ss', hF', hG'⟩ := hsub r.cs subs hF (by simp only [List.length_cons] at hl; omega)
          (fun s h => h)
        have hfl := pruneR_flatten pl ys subs ss' hG' (List.nodup_cons.1 hnd).2
        have hS' : pruneR pl ys (t :: subs.flatten) (t :: ss'.flatten) := by
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have h' : pl ∈ subs.flatten := by
              rcases List.mem_cons.1 h with h | h
              · exact absurd h.symm ht
              · exact h
            obtain ⟨A, C, hA, hC⟩ := hfl.1 h'
            exact ⟨t :: A, C, by rw [hA]; rfl, by rw [hC]; rfl⟩
          · have h' : pl ∉ subs.flatten := fun h2 => h (List.mem_cons_of_mem _ h2)
            rw [hfl.2 h']
        have hnd' : (t :: ss'.flatten).Nodup := by
          by_cases hp : pl ∈ t :: subs.flatten
          · obtain ⟨A, C, hA, hC⟩ := hS'.1 hp
            rw [hC]; rw [hA] at hnd
            have : (A ++ pl :: C).Sublist (A ++ pl :: ys ++ C) := by
              simp only [List.append_assoc, List.cons_append]
              exact List.Sublist.append_left (List.Sublist.cons₂ _ (List.sublist_append_right _ _)) _
            exact hnd.sublist this
          · rw [hS'.2 hp]; exact hnd
        exact ⟨t :: ss'.flatten, kidsTree.mk t r' ss' hr' (by rw [hcs']; exact hF') hnd', hS'⟩



/-- The node at the cut: no children. -/
def cutRec (rn : NRec) : NRec := { rn with nv := { rn.nv with children' := slice.nil }, cs := [] }

/-- The bucket after the cut: the node childless, its spilled children gone (those on the root's
parent chain kept, without the view's bytes). -/
def cutB (B' : BRec) (n : Loc) (rn : NRec) : BRec :=
  { setN B' n (cutRec rn) with ns := cutNs (setN B' n (cutRec rn)).ns (onRootPath B') rn.cs }

theorem cutB_lookup (B' : BRec) (n : Loc) (rn : NRec) (hnd : rn.cs.Nodup) (hnc : n ∉ rn.cs) (l : Loc) :
    (cutB B' n rn).ns !! l = if l ∈ rn.cs then (if onRootPath B' l then (B'.ns !! l).map staleRec else none)
      else if l = n then some (cutRec rn) else B'.ns !! l := by
  unfold cutB
  show cutNs (<[n := cutRec rn]> B'.ns) (onRootPath B') rn.cs !! l = _
  rw [cutNs_lookup _ _ _ hnd l]
  by_cases hl : l ∈ rn.cs
  · have hln : n ≠ l := fun e => hnc (e ▸ hl)
    rw [if_pos hl, if_pos hl, GMap.lookup_insert_ne _ _ hln]
  · rw [if_neg hl, if_neg hl]
    by_cases e : l = n
    · subst e; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), if_neg e]

theorem onRootPath_of (B : BRec) (p : List Loc) (t x : Loc) (hu : upPath B.ns B.bv.rootNode' p t)
    (hx : x ∈ p) : onRootPath B x = true := by
  unfold onRootPath; exact @decide_eq_true _ (Classical.propDecidable _) ⟨p, t, hu, hx⟩

/-- A parent chain of `B'` in the cut bucket. -/
theorem upPath_cut (B' : BRec) (n : Loc) (rn : NRec) (hnd : rn.cs.Nodup) (hnc : n ∉ rn.cs)
    (hn : B'.ns !! n = some rn) (p : List Loc) (t : Loc) (hu : upPath B'.ns B'.bv.rootNode' p t) :
    upPath (cutB B' n rn).ns (cutB B' n rn).bv.rootNode' p t := by
  apply upPath_par B'.ns _ hu
  intro x hx r hr
  rw [cutB_lookup B' n rn hnd hnc x]
  by_cases hxc : x ∈ rn.cs
  · rw [if_pos hxc, if_pos (onRootPath_of B' p t x hu hx), hr]; exact ⟨_, rfl, rfl⟩
  · rw [if_neg hxc]
    by_cases e : x = n
    · subst e; rw [hn] at hr; cases hr; rw [if_pos rfl]; exact ⟨_, rfl, rfl⟩
    · rw [if_neg e]; exact ⟨r, hr, rfl⟩


/-- The live nodes of a bucket whose nodes are a tree: all of them, `n` and its parent among them
(a parentless `n` is the root). -/
theorem hlv_of_treeOK (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (hT : treeOK bl B)
    (hn : B.ns !! n = some rn) :
    ∃ S, liveNodesX B S ∧ (∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧ n ∈ S ∧
      (rn.nv.parent' ≠ null → rn.nv.parent' ∈ S ∧ rn.nv.parent' ∉ rn.cs) ∧
      (rn.nv.parent' = null → ∃ p, upPath B.ns B.bv.rootNode' p n) ∧
      (∀ l r, B.ns !! l = some r → l ∉ S → noViewRec r) := by
  obtain ⟨⟨rk, N, hTH⟩, ⟨r0, h0, hp0⟩, hroot, hok⟩ := hT
  obtain ⟨S, hS, hm⟩ := kidsTree_rootN B.ns rk N hTH B.bv.rootNode' r0 h0 hroot
  have hin : ∀ l, (B.ns !! l).isSome → l ∈ S := fun l h => (hm l).2 h
  refine ⟨S, ⟨[B.bv.rootNode'], B.bv.rootNode', upPath.self _ r0 h0 hp0,
    List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, hS, fun l hl hlS => ?_⟩, fun l hl => ?_,
    hin n (by rw [hn]; rfl), fun hp => ⟨?_, ?_⟩, fun hp => ?_,
    fun l r hr hlS => absurd (hin l (by rw [hr]; rfl)) hlS⟩
  · rw [List.mem_singleton] at hl; subst hl
    exact absurd (hin _ (by rw [h0]; rfl)) hlS
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((hm l).1 hl)
    exact ⟨r, hr, hok l r hr⟩
  · obtain ⟨rp, hrp, -⟩ := hTH.2.2.1 n rn hn hp
    exact hin _ (by rw [hrp]; rfl)
  · intro hc
    obtain ⟨rc, hrc, hpc⟩ := (hTH.2.1 n rn hn).2 _ hc
    have h1 := (hTH.1 n rn hn).2 hp
    have h2 := (hTH.1 _ rc hrc).2 (by rw [hpc]; exact fun e => (hTH.2.2.2 n rn hn) e)
    rw [hpc] at h2
    omega
  · have := hroot n rn hn hp
    subst this
    exact ⟨[B.bv.rootNode'], upPath.self _ rn hn hp⟩

/-- The live nodes of a bucket at the top's spill: the top `n` and its spilled children, the
root's parent chain `p` up to `n` among them. -/
theorem hlv_top (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (p : List Loc)
    (hn : B.ns !! n = some rn) (hpn : rn.nv.parent' = null) (hall : ∀ c ∈ rn.cs, spilledN bl B c)
    (hnd : rn.cs.Nodup) (hnc : n ∉ rn.cs) (hu : upPath B.ns B.bv.rootNode' p n) (hpnd : p.Nodup)
    (hpS : ∀ x ∈ p, x = n ∨ x ∈ rn.cs ∨ ∃ r, B.ns !! x = some r ∧ noViewRec r) (hok : derefOK bl rn)
    (hdom : ∀ l, (B.ns !! l).isSome → l ∈ p ∨ l ∈ rn.cs) :
    ∃ S, liveNodesX B S ∧ (∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧ n ∈ S ∧
      (rn.nv.parent' ≠ null → rn.nv.parent' ∈ S ∧ rn.nv.parent' ∉ rn.cs) ∧
      (rn.nv.parent' = null → ∃ p, upPath B.ns B.bv.rootNode' p n) ∧
      (∀ l r, B.ns !! l = some r → l ∉ S → noViewRec r) := by
  have hF : List.Forall₂ (kidsTree B.ns) rn.cs (rn.cs.map (fun y => [y])) := by
    have : ∀ (l : List Loc), (∀ c ∈ l, c ∈ rn.cs) →
        List.Forall₂ (kidsTree B.ns) l (l.map (fun y => [y])) := by
      intro l hl
      induction l with
      | nil => exact .nil
      | cons y l ihl =>
        obtain ⟨ry, hry, -, hc, -⟩ := hall y (hl y List.mem_cons_self)
        exact .cons (kidsTree_leafC B.ns y ry hry hc) (ihl (fun z hz => hl z (List.mem_cons_of_mem _ hz)))
    exact this rn.cs (fun c h => h)
  have hk : kidsTree B.ns n (n :: rn.cs) := by
    have := kidsTree.mk n rn _ hn hF (by rw [flatten_singletonsC]; exact List.nodup_cons.2 ⟨hnc, hnd⟩)
    rwa [flatten_singletonsC] at this
  refine ⟨n :: rn.cs, ⟨p, n, hu, hpnd, hk, fun l hl hlS => ?_⟩, fun l hl => ?_, List.mem_cons_self,
    fun h => absurd hpn h, fun _ => ⟨p, hu⟩, fun l r hr hlS => ?_⟩
  · rcases hpS l hl with rfl | h | h
    · exact absurd List.mem_cons_self hlS
    · exact absurd (List.mem_cons_of_mem _ h) hlS
    · exact h
  · rcases List.mem_cons.1 hl with rfl | h
    · exact ⟨rn, hn, hok⟩
    · obtain ⟨rc, hrc, -, -, -, -, -, hokc, -⟩ := hall l h
      exact ⟨rc, hrc, hokc⟩
  · rcases hdom l (by rw [hr]; rfl) with hp | hc
    · rcases hpS l hp with rfl | hc | ⟨r', hr', hv⟩
      · exact absurd List.mem_cons_self hlS
      · exact absurd (List.mem_cons_of_mem _ hc) hlS
      · rw [hr] at hr'; cases hr'; exact hv
    · exact absurd (List.mem_cons_of_mem _ hc) hlS




/-- A dereference keeps a bucket's live nodes (the same set), each dereferenced (or kept, without
the view's bytes). -/
theorem live_deref (bl : Loc) (B B0 : BRec) (hd : derefBktX B B0) (hrn : B.bv.rootNode' ≠ null)
    (S : List Loc) (hlv : liveNodesX B S) (hok : ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) :
    liveNodesX B0 S ∧ ∀ l ∈ S, ∃ r r0, B.ns !! l = some r ∧ B0.ns !! l = some r0 ∧ derefOK bl r0 ∧
      dnX r r0 := by
  obtain ⟨p, top, hu, hnd, hk, hq⟩ := hlv
  have h8 := hd.2.2.2.2.2.2.2.1 hrn S p top hu hnd hk hq
  obtain ⟨hu', hk', hq'⟩ := liveX_transfer B B0 hd.1 S p top (fun l hl => (h8 l hl).1)
    (fun l hl => (h8 l hl).2) hu hk hq
  refine ⟨⟨p, top, hu', hnd, hk', hq'⟩, fun l hS => ?_⟩
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (h8 l (Or.inl hS)).1
  obtain ⟨r, hr, hok1⟩ := hok l hS
  have hdn := (h8 l (Or.inl hS)).2 r r' hr hr'
  refine ⟨r, r', hr, hr', ?_, hdn⟩
  rcases hdn with hdn | ⟨rfl, -⟩
  · exact derefOK_derefNode bl _ r' hok1 hdn.1
  · exact hok1

/-- A node's record changed but its children and parent: the live nodes kept. -/
theorem liveNodesX_setN (bl : Loc) (B : BRec) (S : List Loc) (x : Loc) (r r' : NRec)
    (hlv : liveNodesX B S) (hok : ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r)
    (hx : B.ns !! x = some r) (hcs : r'.cs = r.cs) (hpar : r'.nv.parent' = r.nv.parent')
    (hokx : derefOK bl r → derefOK bl r') (hnv : noViewRec r → noViewRec r') :
    liveNodesX (setN B x r') S ∧ ∀ l ∈ S, ∃ r, (setN B x r').ns !! l = some r ∧ derefOK bl r := by
  have hlk : ∀ l, (setN B x r').ns !! l = if l = x then some r' else B.ns !! l := by
    intro l
    show (<[x := r']> B.ns) !! l = _
    by_cases e : l = x
    · subst e; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), if_neg e]
  have hag : ∀ l, nAgree B.ns (setN B x r').ns l := by
    intro l rl hl
    by_cases e : l = x
    · subst e; rw [hx] at hl; cases hl; exact ⟨r', by rw [hlk, if_pos rfl], hcs, hpar⟩
    · exact ⟨rl, by rw [hlk, if_neg e]; exact hl, rfl, rfl⟩
  obtain ⟨p, top, hu, hnd, hk, hq⟩ := hlv
  refine ⟨⟨p, top, upPath_mono B.ns _ hu (fun l _ => hag l), hnd,
    kidsTree_mono B.ns _ S.length top S (Nat.le_refl _) (fun l _ => hag l) hk, fun l hl hlS => ?_⟩,
    fun l hl => ?_⟩
  · obtain ⟨rl, hrl, hv⟩ := hq l hl hlS
    by_cases e : l = x
    · subst e; rw [hx] at hrl; cases hrl; exact ⟨r', by rw [hlk, if_pos rfl], hnv hv⟩
    · exact ⟨rl, by rw [hlk, if_neg e]; exact hrl, hv⟩
  · obtain ⟨rl, hrl, hokl⟩ := hok l hl
    by_cases e : l = x
    · subst e; rw [hx] at hrl; cases hrl; exact ⟨r', by rw [hlk, if_pos rfl], hokx hokl⟩
    · exact ⟨rl, by rw [hlk, if_neg e]; exact hrl, hokl⟩


/-- A live node's record changed but its children and parent: the live nodes kept. -/
theorem liveNodesX_setN_in (bl : Loc) (B : BRec) (S : List Loc) (x : Loc) (r r' : NRec)
    (hlv : liveNodesX B S) (hok : ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r)
    (hx : B.ns !! x = some r) (hxS : x ∈ S) (hcs : r'.cs = r.cs) (hpar : r'.nv.parent' = r.nv.parent')
    (hokx : derefOK bl r') :
    liveNodesX (setN B x r') S ∧ ∀ l ∈ S, ∃ r, (setN B x r').ns !! l = some r ∧ derefOK bl r := by
  have hlk : ∀ l, (setN B x r').ns !! l = if l = x then some r' else B.ns !! l := by
    intro l
    show (<[x := r']> B.ns) !! l = _
    by_cases e : l = x
    · subst e; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), if_neg e]
  have hag : ∀ l, nAgree B.ns (setN B x r').ns l := by
    intro l rl hl
    by_cases e : l = x
    · subst e; rw [hx] at hl; cases hl; exact ⟨r', by rw [hlk, if_pos rfl], hcs, hpar⟩
    · exact ⟨rl, by rw [hlk, if_neg e]; exact hl, rfl, rfl⟩
  obtain ⟨p, top, hu, hnd, hk, hq⟩ := hlv
  refine ⟨⟨p, top, upPath_mono B.ns _ hu (fun l _ => hag l), hnd,
    kidsTree_mono B.ns _ S.length top S (Nat.le_refl _) (fun l _ => hag l) hk, fun l hl hlS => ?_⟩,
    fun l hl => ?_⟩
  · have e : l ≠ x := fun e => hlS (e ▸ hxS)
    obtain ⟨rl, hrl, hv⟩ := hq l hl hlS
    exact ⟨rl, by rw [hlk, if_neg e]; exact hrl, hv⟩
  · by_cases e : l = x
    · exact ⟨r', by rw [hlk, if_pos e], hokx⟩
    · obtain ⟨rl, hrl, hokl⟩ := hok l hl
      exact ⟨rl, by rw [hlk, if_neg e]; exact hrl, hokl⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The parts loop's facts (see the module doc): at the split `Ws`, `Ts`, `Bs`, `Ks`; now `W`,
`T`, `B`, `K`, the parts `ps` written. -/
def partsP (bl txl : Loc) (txid : w64) (n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode))
    (par : Loc) (ws0 : List WEntry) (i0 : Nat) (lo hi : Option (List w8))
    (Ws : WView) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool)
    (W : WView) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (B : BRec)
    (ps : List (w64 × List w8)) : Prop :=
  spillG (hG := hG) W txl txid T ρ F ∧ T.bs !! bl = some B ∧
  spillFrame Ts T (· = bl) ∧ W.pages = Ws.pages ∧ W.ps = Ws.ps ∧
  spillPages Ws Ts ⊆ spillPages W T ∧
  B.bv = Bs.bv ∧ B.ib = Bs.ib ∧ B.nm = Bs.nm ∧ B.bm = Bs.bm ∧
  ps.length ≤ xs.length ∧
  (∀ j x, j < ps.length → (xs[j]?).map (fun x => x.1) = some x → (par ≠ null → spilledN bl B x) ∧
    ∃ rx p, B.ns !! x = some rx ∧ rx.nv.spilled' = true ∧ rx.cs = [] ∧ rx.nv.bucket' = bl ∧
      rx.ins.length = rx.ws.length ∧ derefOK bl rx ∧
      ps[j]? = some p ∧ rx.nv.pgid' = p.1 ∧ rx.nv.parent' = par ∧
      rx.ws.map ownFresh = ((chunksOf rc xs).getD j []).map ownFresh ∧ rx.nv.isLeaf' = rc.nv.isLeaf') ∧
  (∀ j x, ps.length ≤ j → (xs[j]?).map (fun x => x.1) = some x →
    ∃ rs rx, Bs.ns !! x = some rs ∧ B.ns !! x = some rx ∧ dnK rs rx ∧
      (0 < j → rx.nv.pgid' = W64 0)) ∧
  (∀ j p, ps[j]? = some p → p.2 = (wHead ((chunksOf rc xs).getD j [])).key) ∧
  (∀ p ∈ ps, Ts.bufs !! p.1 = none ∧ Ws.pages !! uint.nat p.1 = none ∧ (T.bufs !! p.1).isSome ∧
    Bs.nm !! p.1 = none ∧ 2 ≤ uint.nat p.1) ∧
  (ps.map (fun p => p.1)).Nodup ∧
  (par ≠ null → ∃ rp, B.ns !! par = some rp ∧ K par = false ∧ parentWs ws0 i0 ps rp.ws ∧
    wsLive rp.ws ∧ rp.ins.length = rp.ws.length ∧
    wsSorted rp.ws ∧ rp.nv.bucket' = bl ∧ par ∉ xs.map (fun x => x.1) ∧
    ∃ rp0, Bs.ns !! par = some rp0 ∧ rp.cs = rp0.cs ∧ rp.key = rp0.key ∧
      rp.nv = ({ rp0.nv with inodes' := rp.nv.inodes', key' := rp.nv.key' } : node) ∧
      (rp0.nv.key' = slice.nil → rp.nv.key' = slice.nil) ∧
      (rp0.nv.key' ≠ slice.nil → 0 < rp0.key.length → rp.nv.key' ≠ slice.nil) ∧
      (rp.ksrc = rp0.ksrc ∨ rp.ksrc = Src.own (DFrac.own 1))) ∧
  (∀ x rs, x ∉ xs.map (fun x => x.1) → x ≠ par → Bs.ns !! x = some rs →
    ∃ rx, B.ns !! x = some rx ∧ dnK rs rx) ∧
  (∀ x, (B.ns !! x).isSome → (Bs.ns !! x).isSome) ∧
  (∀ x, x ∉ (xs.take ps.length).map (fun x => x.1) → K x = Ks x) ∧
  (∃ S, liveNodesX B S ∧ (∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧
    (∀ (j : Nat) (x : Loc), (xs[j]?).map (fun x => x.1) = some x → x ∈ S) ∧ (par ≠ null → par ∈ S) ∧
    (∀ l r, B.ns !! l = some r → l ∉ S → noViewRec r))

/-- The unwritten parts' entries' trees: chunk `j` from `j0` on, its own bound. -/
def chunkToks (γ : GName) (P : GMap Nat (List w8)) (B : BRec) (leaf : Bool) (kind ch0 : Nat)
    (chs : List (List WEntry)) (hi : Option (List w8)) (j0 : Nat) : IProp GF :=
  [∗list] j ↦ ch ∈ chs.drop j0,
    [∗list] i ↦ w ∈ ch, entRes γ P B (hiAt chs hi (j0 + j)) leaf kind ch0 ch i w

/-- The parts' inodes are the node's, every part after the first non-empty. -/
def piecesFlat (rc : NRec) (xs : List (Loc × node × List Inode)) : Prop :=
  (xs.map (fun x => x.2.2)).flatten = rc.ins ∧ ∀ x ∈ xs.drop 1, 0 < x.2.2.length

/-- What the parts loop knows of the split, beyond `partsP` (see the module doc). -/
def startP (bl : Loc) (n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode)) (par : Loc)
    (Bs : BRec) (ws0 : List WEntry) (i0 : Nat) : Prop :=
  xs ≠ [] ∧ (xs.map (fun x => x.1)).Nodup ∧ (xs.head?.map (fun x => x.1) = some n) ∧
  piecesFlat rc xs ∧
  (xs.length = 1 → par = rc.nv.parent') ∧
  (2 ≤ xs.length → par ≠ null ∧ (rc.nv.parent' ≠ null → par = rc.nv.parent')) ∧
  (par ≠ null → ∃ rp0, Bs.ns !! par = some rp0 ∧ rp0.ws = ws0 ∧
    ((rc.nv.parent' ≠ null ∧ ∃ w, ws0[i0]? = some w ∧ w.key = rc.key ∧ w.pgid = rc.nv.pgid') ∨
     (rc.nv.parent' = null ∧ ws0 = [] ∧ i0 = 0))) ∧
  (∀ j x, xs[j]? = some x → Bs.ns !! x.1 = some (partRec rc j x ((chunksOf rc xs).getD j []))) ∧
  (∀ x ∈ xs, x.2.1.parent' = par) ∧
  (∀ x, xs.head? = some x → x.2.1 = { rc.nv with parent' := par, inodes' := x.2.1.inodes' }) ∧
  (∀ x ∈ xs.drop 1, x.2.1.pgid' = W64 0 ∧ x.2.1.key' = slice.nil)

/-- What the split did: nothing, or the parts `xs` under `par` (see `spillR_split`). -/
def splitRes (bl n : Loc) (rc rp : NRec) (xs : List (Loc × node × List Inode)) (T : WTx) (B : BRec)
    (K : Loc → Bool) (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc) : Prop :=
  (xs = [(n, rc.nv, rc.ins)] ∧ Ts = T ∧ Bs = B ∧ Ks = K) ∨
  (∃ (pv' : node) (pcs' : List Loc) (st : TxStats), 2 ≤ xs.length ∧ splitPieces n rc.nv par rc.ins xs ∧
    par ≠ null ∧ splitFresh B n xs par rc.nv.parent' ∧ Ts = splitT T bl B rc rp xs par pv' pcs' st ∧
    Bs = { B with ns := splitNs B.ns rc rp xs par pv' pcs' } ∧ Ks = splitK K xs par ∧
    ((rc.nv.parent' = null ∧ pv' = newParent rc.nv pv'.children' ∧ pcs' = xs.map (fun x => x.1)) ∨
     (rc.nv.parent' ≠ null ∧ par = rc.nv.parent' ∧ pv' = { rp.nv with children' := pv'.children' } ∧
      pcs' = rp.cs ++ (xs.drop 1).map (fun x => x.1))))

theorem spillG_stat (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (st : TxStats) (hg : spillG (hG := hG) W txl txid T ρ F) :
    spillG (hG := hG) W txl txid { T with t := { T.t with stats' := st } } ρ F := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd⟩ := hg
  obtain ⟨d1, d2, d3, d4⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, d1,
    fun bl h => bktReach_bmN T { T with t := { T.t with stats' := st } } _ (fun c C' h => ⟨C', h, rfl⟩) (fun c h => h) bl (d2 bl h), d3, d4⟩

theorem spillFrame_split (T : WTx) (bl : Loc) (B' : BRec) (st : TxStats) (hbl : (T.bs !! bl).isSome) :
    spillFrame T { setB T bl B' with t := { T.t with stats' := st } } (· = bl) := by
  obtain ⟨a, b, c, d, -, f⟩ := spillFrame_setB T bl B' hbl
  exact ⟨a, b, c, d, rfl, f⟩

/-- `partsP` with no part written. -/
theorem partsP_nil (bl txl : Loc) (txid : w64) (n : Loc) (rc : NRec) (xs : List (Loc × node × List Inode))
    (par : Loc) (ws0 : List WEntry) (i0 : Nat) (lo hi : Option (List w8)) (W : WView) (Ts : WTx)
    (Bs : BRec) (Ks : Loc → Bool) (ρ : DBState) (F : GMap Nat (List w8))
    (hg : spillG (hG := hG) W txl txid Ts ρ F) (hB : Ts.bs !! bl = some Bs)
    (hlv : ∃ S, liveNodesX Bs S ∧ (∀ l ∈ S, ∃ r, Bs.ns !! l = some r ∧ derefOK bl r) ∧
      (∀ x ∈ xs, x.1 ∈ S) ∧ (par ≠ null → par ∈ S) ∧ (∀ l r, Bs.ns !! l = some r → l ∉ S → noViewRec r))
    (hrec : ∀ j x, xs[j]? = some x → ∃ rs, Bs.ns !! x.1 = some rs ∧ (0 < j → rs.nv.pgid' = W64 0))
    (hpar : par ≠ null → ∃ rp, Bs.ns !! par = some rp ∧ Ks par = false ∧ rp.ws = ws0 ∧ wsLive rp.ws ∧
      rp.ins.length = rp.ws.length ∧ wsSorted rp.ws ∧ rp.nv.bucket' = bl ∧ par ∉ xs.map (fun x => x.1)) :
    partsP (hG := hG) bl txl txid n rc xs par ws0 i0 lo hi W Ts Bs Ks W Ts ρ F Ks Bs [] := by
  refine ⟨hg, hB, spillFrame_reflN Ts _, rfl, rfl, GMap.map_subseteq_refl _, rfl, rfl, rfl, rfl,
    Nat.zero_le _, fun j x hj => absurd hj (Nat.not_lt_zero _), ?_, fun j p hp => by simp at hp,
    fun p hp => by simp at hp, List.nodup_nil, ?_, ?_, fun x h => h, fun x _ => rfl, ?_⟩
  · intro j x _ hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨rs, hrs, hpg⟩ := hrec j y hy
    exact ⟨rs, rs, hrs, hrs, Or.inl rfl, hpg⟩
  · intro hp
    obtain ⟨rp, hrp, hK, hws, hwl, hil, hso, hbk, hni⟩ := hpar hp
    refine ⟨rp, hrp, hK, Or.inl ⟨rfl, by rw [hws]⟩, hwl, hil, hso, hbk, hni, rp, hrp, rfl, rfl, rfl, fun h => h, fun h _ => h,
      Or.inl rfl⟩
  · intro x rs _ _ hx; exact ⟨rs, hx, Or.inl rfl⟩
  · obtain ⟨S, h1, h2, h3, h4, h5⟩ := hlv
    exact ⟨S, h1, h2, fun j x hx => by
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx; exact h3 y (List.mem_of_getElem? hy), h4, h5⟩

/-- The split's outcome: the state the parts loop starts from. -/
theorem parts_start (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (rc rp : NRec) (lo hi : Option (List w8))
    (hg : spillG (hG := hG) W txl txid T ρ F) (hB : T.bs !! bl = some B)
    (hn : B.ns !! n = some rc) (hK : K n = false) (hcs : rc.cs = [])
    (xs : List (Loc × node × List Inode)) (hdok : derefOK bl rc)
    (hpar : rc.nv.parent' ≠ null → B.ns !! rc.nv.parent' = some rp ∧ K rc.nv.parent' = false ∧
      wsLive rp.ws ∧ rp.ins.length = rp.ws.length ∧ wsSorted rp.ws ∧ rp.nv.bucket' = bl ∧
      rc.nv.parent' ≠ n ∧
      ∃ (i0 : Nat) (w : WEntry), rp.ws[i0]? = some w ∧ w.key = rc.key ∧ w.pgid = rc.nv.pgid')
    (hlive : ∃ S, liveNodesX B S ∧ (∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧
      (rc.nv.parent' ≠ null → n ∈ S ∧ rc.nv.parent' ∈ S) ∧
      (rc.nv.parent' = null → ∃ p, upPath B.ns B.bv.rootNode' p n) ∧
      (∀ l r, B.ns !! l = some r → l ∉ S → noViewRec r)) :
    ((⌜xs = [(n, rc.nv, rc.ins)]⌝ ∗ spillR I γd γ W txl txid T ρ F K) ∨
      (∃ (pl : Loc) (pv' : node) (pcs' : List Loc) (xl : Loc × node × List Inode) (st : TxStats),
        ⌜2 ≤ xs.length ∧ splitPieces n rc.nv pl rc.ins xs ∧ xs.getLast? = some xl ∧ pl ≠ null ∧
          ((rc.nv.parent' = null ∧ pv' = newParent rc.nv pv'.children' ∧
              pcs' = xs.map (fun x => x.1)) ∨
           (rc.nv.parent' ≠ null ∧ pl = rc.nv.parent' ∧ pv' = { rp.nv with children' := pv'.children' } ∧
            pcs' = rp.cs ++ (xs.drop 1).map (fun x => x.1)))⌝ ∗
        ⌜splitFresh B n xs pl rc.nv.parent'⌝ ∗
        spillR I γd γ W txl txid (splitT T bl B rc rp xs pl pv' pcs' st) ρ F (splitK K xs pl))) ⊢
    ∃ (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc) (ws0 : List WEntry) (i0 : Nat),
      spillR I γd γ W txl txid Ts ρ F Ks ∗
      ⌜partsP (hG := hG) bl txl txid n rc xs par ws0 i0 lo hi W Ts Bs Ks W Ts ρ F Ks Bs [] ∧
        startP bl n rc xs par Bs ws0 i0 ∧ spillFrame T Ts (· = bl) ∧
        (Bs.bv = B.bv ∧ Bs.ib = B.ib ∧ Bs.nm = B.nm ∧ Bs.bm = B.bm) ∧
        splitRes bl n rc rp xs T B K Ts Bs Ks par⌝ := by
  have hbl : (T.bs !! bl).isSome := by rw [hB]; rfl
  iintro (⟨%hxs, HR⟩ | ⟨%pl, %pv', %pcs', %xl, %st, %hsf, %hfr, HR⟩)
  · subst hxs
    have hrec0 : ∀ (j : Nat) (x : Loc × node × List Inode), [(n, rc.nv, rc.ins)][j]? = some x →
        j = 0 ∧ x = (n, rc.nv, rc.ins) := by
      intro j x hx
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; exact ⟨rfl, hx.symm⟩
      | succ j => simp at hx
    have hchunk : (chunksOf rc [(n, rc.nv, rc.ins)]).getD 0 [] = rc.ws := by
      simp only [chunksOf, List.map_cons, List.map_nil, wsChunks, List.getD_cons_zero]
      rw [hdok.2.1]; exact List.take_length
    have hprt : B.ns !! n = some (partRec rc 0 (n, rc.nv, rc.ins) ((chunksOf rc [(n, rc.nv, rc.ins)]).getD 0 [])) := by
      rw [hchunk, hn]; unfold partRec; rw [if_pos rfl]
    have hrecs : ∀ (j : Nat) (x : Loc × node × List Inode), [(n, rc.nv, rc.ins)][j]? = some x →
        B.ns !! x.1 = some (partRec rc j x ((chunksOf rc [(n, rc.nv, rc.ins)]).getD j [])) := by
      intro j x hx; obtain ⟨rfl, rfl⟩ := hrec0 j x hx; exact hprt
    have hflat : piecesFlat rc [(n, rc.nv, rc.ins)] := ⟨by simp, fun x hx => by simp at hx⟩
    have hlvU : ∃ S, liveNodesX B S ∧ (∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧
        (∀ x ∈ [(n, rc.nv, rc.ins)], x.1 ∈ S) ∧ (rc.nv.parent' ≠ null → rc.nv.parent' ∈ S) ∧
        (∀ l r, B.ns !! l = some r → l ∉ S → noViewRec r) := by
      obtain ⟨S, hS, hok, h1, h2, h3⟩ := hlive
      have hnS : n ∈ S := by
        by_cases hp : rc.nv.parent' = null
        · obtain ⟨p1, hu1⟩ := h2 hp
          obtain ⟨p, top, hu, -, hk, -⟩ := hS
          obtain ⟨-, ht⟩ := upPath_det B.ns hu hu1
          rw [← ht]; exact kidsTree_head B.ns top S hk
        · exact (h1 hp).1
      exact ⟨S, hS, hok, fun x hx => by simp at hx; rw [hx]; exact hnS, fun hp => (h1 hp).2, h3⟩
    by_cases hp : rc.nv.parent' = null
    · iexists T, B, K, rc.nv.parent', ([] : List WEntry), 0
      iframe HR
      ipureintro
      refine ⟨partsP_nil bl txl txid n rc _ _ _ _ lo hi W T B K ρ F hg hB hlvU
        (fun j x hx => ⟨rc, by obtain ⟨rfl, rfl⟩ := hrec0 j x hx; exact hn, fun h => absurd h (by
          obtain ⟨rfl, -⟩ := hrec0 j x hx; exact Nat.lt_irrefl 0)⟩) (fun h => absurd hp h),
        ⟨List.cons_ne_nil _ _, by simp, rfl, hflat, fun _ => rfl, fun h => by simp at h,
          fun h => absurd hp h, hrecs, fun x hx => by simp at hx; rw [hx],
          fun x hx => by simp at hx; subst hx; rfl, fun x hx => by simp at hx⟩, spillFrame_reflN T _,
          ⟨rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨hrp, hKp, hwl, hil, hso, hbk, hpn', i0, w, hw, hwk, hwp⟩ := hpar hp
      iexists T, B, K, rc.nv.parent', rp.ws, i0
      iframe HR
      ipureintro
      refine ⟨partsP_nil bl txl txid n rc _ _ _ _ lo hi W T B K ρ F hg hB hlvU
        (fun j x hx => ⟨rc, by obtain ⟨rfl, rfl⟩ := hrec0 j x hx; exact hn, fun h => absurd h (by
          obtain ⟨rfl, -⟩ := hrec0 j x hx; exact Nat.lt_irrefl 0)⟩)
          (fun _ => ⟨rp, hrp, hKp, rfl, hwl, hil, hso, hbk, by simpa using hpn'⟩),
        ⟨List.cons_ne_nil _ _, by simp, rfl, hflat, fun _ => rfl, fun h => by simp at h,
          fun _ => ⟨rp, hrp, rfl, Or.inl ⟨hp, w, hw, hwk, hwp⟩⟩, hrecs,
          fun x hx => by simp at hx; rw [hx],
          fun x hx => by simp at hx; subst hx; rfl, fun x hx => by simp at hx⟩, spillFrame_reflN T _,
          ⟨rfl, rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨h2, hsp, hlast, hpl0, hcase⟩ := hsf
    have hfr' := hfr
    obtain ⟨-, -, hplids, hnd⟩ := hfr'
    have hsp' := hsp
    obtain ⟨hflat, ⟨x0, rest, hxs, hx0n, hx0v, hrest⟩, hlen2⟩ := hsp'
    have hBs : (splitT T bl B rc rp xs pl pv' pcs' st).bs !! bl =
        some { B with ns := splitNs B.ns rc rp xs pl pv' pcs' } := by
      unfold splitT; exact GMap.lookup_insert _ _ _
    have hlv := split_live bl n pl B rc rp xs pv' pcs' hn hcs hdok hsp hpl0 hcase hfr
      (fun h => (hpar h).1) hlive
    obtain ⟨S', hlS', hokS', hxS', hplS', hnvS'⟩ := hlv
    have hgs : spillG (hG := hG) W txl txid (splitT T bl B rc rp xs pl pv' pcs' st) ρ F :=
      spillG_stat W txl txid _ ρ F st
        (spillG_setB W txl txid T ρ F bl B { B with ns := splitNs B.ns rc rp xs pl pv' pcs' } hg hB rfl rfl
          (Or.inr ⟨S', hlS', hokS'⟩))
    have hrecs : ∀ (j : Nat) (x : Loc × node × List Inode), xs[j]? = some x →
        (splitNs B.ns rc rp xs pl pv' pcs') !! x.1 = some (partRec rc j x ((chunksOf rc xs).getD j [])) :=
      fun j x hx => splitNs_part B.ns rc rp xs pl pv' pcs' hnd j x hx
    have hrec : ∀ (j : Nat) (x : Loc × node × List Inode), xs[j]? = some x →
        ∃ rs, (splitNs B.ns rc rp xs pl pv' pcs') !! x.1 = some rs ∧ (0 < j → rs.nv.pgid' = W64 0) := by
      intro j x hx
      refine ⟨_, hrecs j x hx, fun hj => ?_⟩
      have hxr : x ∈ rest := by
        rw [hxs] at hx
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp only [List.getElem?_cons_succ] at hx
        exact List.mem_of_getElem? hx
      obtain ⟨-, hv⟩ := hrest x hxr
      unfold partRec; rw [if_neg (by omega)]
      show x.2.1.pgid' = W64 0
      rw [hv]; rfl
    have hparof : ∀ x ∈ xs, x.2.1.parent' = pl := by
      intro x hx
      rw [hxs] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hx0v]
      · rw [(hrest x hx).2]
    have hpfl : piecesFlat rc xs := ⟨hflat, fun x hx => by
      have := hlen2 h2 x (List.mem_of_mem_drop hx); omega⟩
    have hhead : xs.head?.map (fun x => x.1) = some n := by rw [hxs]; simp [hx0n]
    have hne : xs ≠ [] := by rw [hxs]; exact List.cons_ne_nil _ _
    rcases hcase with ⟨hpn, hpv, hpcs⟩ | ⟨hpn, hpleq, hpv, hpcs⟩
    · have hprec : (splitNs B.ns rc rp xs pl pv' pcs') !! pl = some ⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ := by
        rw [splitNs_par _ _ _ _ _ _ _ hplids]; unfold parentRec; rw [if_pos hpn]
      iexists (splitT T bl B rc rp xs pl pv' pcs' st), { B with ns := splitNs B.ns rc rp xs pl pv' pcs' },
        (splitK K xs pl), pl, ([] : List WEntry), 0
      iframe HR
      ipureintro
      refine ⟨partsP_nil bl txl txid n rc _ _ _ _ lo hi W _ _ _ ρ F hgs hBs ⟨S', hlS', hokS', hxS', fun _ => hplS', hnvS'⟩ hrec
        (fun _ => ⟨_, hprec, splitK_pl K xs pl hplids, rfl, fun w hw => by simp at hw, rfl,
          fun i j _ hj => by simp at hj, by show pv'.bucket' = bl; rw [hpv]; exact hdok.1, hplids⟩),
        ⟨hne, hnd, hhead, hpfl, fun h => by omega, fun _ => ⟨hpl0, fun h => absurd hpn h⟩,
          fun _ => ⟨_, hprec, rfl, Or.inr ⟨hpn, rfl, rfl⟩⟩, hrecs, hparof, fun x hx => by rw [hxs] at hx; simp at hx; subst hx; exact hx0v,
          fun x hx => by
            rw [hxs] at hx; simp only [List.drop_succ_cons, List.drop_zero] at hx
            rw [(hrest x hx).2]; exact ⟨rfl, rfl⟩⟩,
        spillFrame_split T bl _ st hbl, ⟨rfl, rfl, rfl, rfl⟩, Or.inr ⟨pv', pcs', st, h2, hsp, hpl0, hfr, rfl, rfl, rfl, Or.inl ⟨hpn, hpv, hpcs⟩⟩⟩
    · obtain ⟨hrp, hKp, hwl, hil, hso, hbk, -, i0, w, hw, hwk, hwp⟩ := hpar hpn
      have hprec : (splitNs B.ns rc rp xs pl pv' pcs') !! pl = some { rp with nv := pv', cs := pcs' } := by
        rw [splitNs_par _ _ _ _ _ _ _ hplids]; unfold parentRec; rw [if_neg hpn]
      iexists (splitT T bl B rc rp xs pl pv' pcs' st), { B with ns := splitNs B.ns rc rp xs pl pv' pcs' },
        (splitK K xs pl), pl, rp.ws, i0
      iframe HR
      ipureintro
      refine ⟨partsP_nil bl txl txid n rc _ _ _ _ lo hi W _ _ _ ρ F hgs hBs ⟨S', hlS', hokS', hxS', fun _ => hplS', hnvS'⟩ hrec
        (fun _ => ⟨_, hprec, splitK_pl K xs pl hplids, rfl, hwl, hil, hso,
          by show pv'.bucket' = bl; rw [hpv]; exact hbk, hplids⟩),
        ⟨hne, hnd, hhead, hpfl, fun h => by omega, fun _ => ⟨hpl0, fun _ => hpleq⟩,
          fun _ => ⟨_, hprec, rfl, Or.inl ⟨hpn, w, hw, hwk, hwp⟩⟩, hrecs, hparof, fun x hx => by rw [hxs] at hx; simp at hx; subst hx; exact hx0v,
          fun x hx => by
            rw [hxs] at hx; simp only [List.drop_succ_cons, List.drop_zero] at hx
            rw [(hrest x hx).2]; exact ⟨rfl, rfl⟩⟩,
        spillFrame_split T bl _ st hbl, ⟨rfl, rfl, rfl, rfl⟩, Or.inr ⟨pv', pcs', st, h2, hpleq ▸ hsp, hpl0, hfr, rfl, rfl, rfl, Or.inr ⟨hpn, hpleq, hpv, hpcs⟩⟩⟩


theorem wHead_drop_take (ws : List WEntry) (k k1 : Nat) (hk : k < ws.length) (hk1 : 0 < k1) :
    (wHead ((ws.drop k).take k1)).key = wKey ws k := by
  unfold wHead wKey
  rw [List.getElem?_eq_getElem hk]
  obtain ⟨m, rfl⟩ : ∃ m, k1 = m + 1 := ⟨k1 - 1, by omega⟩
  rw [List.drop_eq_getElem_cons hk]
  rfl

theorem childHi_drop (hi : Option (List w8)) (ws : List WEntry) (k i : Nat) :
    childHi hi (wKey ws) ws.length (i + k) = childHi hi (wKey (ws.drop k)) (ws.drop k).length i := by
  unfold childHi wKey
  rw [List.length_drop, List.getElem?_drop]
  have e : k + (i + 1) = i + k + 1 := by omega
  rw [e]
  by_cases h : i + k + 1 < ws.length
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem entRes_congr (γ : GName) (P : GMap Nat (List w8)) (B B' : BRec) (hnm : B'.nm = B.nm)
    (hi hi' : Option (List w8)) (leaf : Bool) (kind ch0 : Nat) (ws ws' : List WEntry) (i i' : Nat)
    (w : WEntry) (hc : childHi hi (wKey ws) ws.length i = childHi hi' (wKey ws') ws'.length i') :
    entRes (GF := GF) γ P B hi leaf kind ch0 ws i w = entRes γ P B' hi' leaf kind ch0 ws' i' w := by
  unfold entRes; rw [hnm, hc]

theorem chunks_toks (γ : GName) (P : GMap Nat (List w8)) (B B' : BRec) (hnm : B'.nm = B.nm)
    (hi : Option (List w8)) (leaf : Bool) (kind ch0 : Nat) :
    ∀ (ks : List Nat) (ws : List WEntry), ks.sum = ws.length → (∀ k ∈ ks.drop 1, 0 < k) →
      ([∗list] i ↦ w ∈ ws, entRes (GF := GF) γ P B hi leaf kind ch0 ws i w) ⊢
        [∗list] j ↦ ch ∈ wsChunks ws ks,
          [∗list] i ↦ w ∈ ch, entRes γ P B' (hiAt (wsChunks ws ks) hi j) leaf kind ch0 ch i w
  | [], ws, hs, _ => by
    have : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hs.symm)
    subst this
    simp only [wsChunks]
    exact .rfl
  | k :: ks, ws, hs, hne => by
    simp only [List.sum_cons] at hs
    have hk : k ≤ ws.length := by omega
    have hne' : ∀ k' ∈ ks.drop 1, 0 < k' := by
      intro k' hk'
      exact hne k' (by
        cases ks with
        | nil => simp at hk'
        | cons a t => simp only [List.drop_succ_cons, List.drop_zero] at hne ⊢; exact List.mem_cons_of_mem _ (by simpa using hk'))
    have IH := chunks_toks γ P B B' hnm hi leaf kind ch0 ks (ws.drop k) (by rw [List.length_drop]; omega) hne'
    simp only [wsChunks]
    refine (BiEntails.of_eq (congrArg (fun l => [∗list] i ↦ w ∈ l, entRes (GF := GF) γ P B hi leaf kind ch0 ws i w)
      (List.take_append_drop k ws).symm)).1.trans ?_
    refine BigSepL.bigSepL_append.1.trans ?_
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2
    refine sep_mono ?_ ?_
    · refine BigSepL.bigSepL_mono (fun {i w} hiw => ?_)
      have hil : i < (ws.take k).length := (List.getElem?_eq_some_iff.1 hiw).1
      rw [List.length_take, Nat.min_eq_left hk] at hil
      rw [entRes_congr γ P B B' hnm hi _ leaf kind ch0 ws (ws.take k) i i w ?_]
      unfold childHi
      rw [List.length_take, Nat.min_eq_left hk]
      by_cases h1 : i + 1 < k
      · rw [if_pos (by omega), if_pos h1]
        congr 1
        unfold wKey; rw [List.getElem?_take, if_pos h1]
      · rw [if_neg h1]
        have hik : i + 1 = k := by omega
        unfold hiAt
        cases ks with
        | nil =>
          simp only [wsChunks, List.getElem?_cons_succ, List.getElem?_nil]
          rw [if_neg (by simp at hs; omega)]
        | cons k1 ks1 =>
          have hk1 : 0 < k1 := hne k1 (by simp)
          simp only [wsChunks, List.getElem?_cons_succ, List.getElem?_cons_zero]
          simp only [List.sum_cons] at hs
          rw [if_pos (by omega), hik, wHead_drop_take ws k k1 (by omega) hk1]
    · refine BigSepL.bigSepL_mono_of_forall (fun {i w} => ?_) |>.trans IH |>.trans ?_
      · rw [List.length_take, Nat.min_eq_left hk]
        rw [entRes_congr γ P B B rfl hi hi leaf kind ch0 ws (ws.drop k) (i + k) i w (childHi_drop hi ws k i)]
      · exact .rfl

/-- The node's tokens at the split: its page's, and its entries' trees, in the parts' chunks. -/
theorem toks_start (γ : GName) (P : GMap Nat (List w8)) (B B' : BRec)
    (b : Option (List w8) × Option (List w8)) (kind ch0 : Nat) (rn rc : NRec)
    (xs : List (Loc × node × List Inode)) (hnm : B'.nm = B.nm) (hws : rc.ws = rn.ws)
    (hpg : rc.nv.pgid' = rn.nv.pgid') (hleaf : rc.nv.isLeaf' = rn.nv.isLeaf')
    (hflat : piecesFlat rc xs) (hl : rc.ins.length = rc.ws.length) :
    rtoks (GF := GF) γ P B b kind ch0 rn ⊢
      (if rc.nv.pgid' = W64 0 then emp else (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF)) ∗
      chunkToks γ P B' rc.nv.isLeaf' kind ch0 (chunksOf rc xs) b.2 0 := by
  unfold rtoks chunkToks chunksOf
  rw [hpg, hleaf, ← hws]
  refine sep_mono .rfl ?_
  simp only [List.drop_zero, Nat.zero_add]
  apply chunks_toks γ P B B' hnm b.2 rn.nv.isLeaf' kind ch0
  · rw [← hl, ← hflat.1, List.length_flatten, List.map_map]; rfl
  · intro k hk
    rw [← List.map_drop, List.mem_map] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    exact hflat.2 x hx

theorem setB_setB (T : WTx) (bl : Loc) (X Y : BRec) : setB (setB T bl X) bl Y = setB T bl Y := by
  unfold setB
  congr 1
  apply GMap.ext; intro k
  show (<[bl := Y]> (<[bl := X]> T.bs)) !! k = (<[bl := Y]> T.bs) !! k
  by_cases e : bl = k
  · subst e; rw [GMap.lookup_insert, GMap.lookup_insert]
  · rw [GMap.lookup_insert_ne _ _ e, GMap.lookup_insert_ne _ _ e, GMap.lookup_insert_ne _ _ e]

/-- After the cut (the node `n` childless, its spilled children gone): the transaction's facts,
and the bucket's live nodes, with `n` (and its parent) among them. -/
theorem spillG_cut (W' : WView) (txl : Loc) (txid : w64) (T' : WTx) (ρ' : DBState)
    (F' : GMap Nat (List w8)) (bl : Loc) (B' : BRec) (n : Loc) (rn : NRec)
    (hg : spillG (hG := hG) W' txl txid T' ρ' F') (hB : T'.bs !! bl = some B')
    (hn : B'.ns !! n = some rn) (hall : ∀ c ∈ rn.cs, spilledN bl B' c) (hnd : rn.cs.Nodup)
    (hnc : n ∉ rn.cs)
    (hlv : ∃ S, liveNodesX B' S ∧ (∀ l ∈ S, ∃ r, B'.ns !! l = some r ∧ derefOK bl r) ∧ n ∈ S ∧
      (rn.nv.parent' ≠ null → rn.nv.parent' ∈ S ∧ rn.nv.parent' ∉ rn.cs) ∧
      (rn.nv.parent' = null → ∃ p, upPath B'.ns B'.bv.rootNode' p n) ∧
      (∀ l r, B'.ns !! l = some r → l ∉ S → noViewRec r)) :
    spillG (hG := hG) W' txl txid (setB (setB T' bl (setN B' n (cutRec rn))) bl (cutB B' n rn)) ρ' F' ∧
      ∃ S3, liveNodesX (cutB B' n rn) S3 ∧
        (∀ l ∈ S3, ∃ r, (cutB B' n rn).ns !! l = some r ∧ derefOK bl r) ∧
        ((cutRec rn).nv.parent' ≠ null → n ∈ S3 ∧ (cutRec rn).nv.parent' ∈ S3) ∧
        ((cutRec rn).nv.parent' = null → ∃ p, upPath (cutB B' n rn).ns (cutB B' n rn).bv.rootNode' p n) ∧
        (∀ l r, (cutB B' n rn).ns !! l = some r → l ∉ S3 → noViewRec r) := by
  obtain ⟨S, ⟨p, top, hu, hpnd, hk, hq⟩, hSok, hnS, hpar, hnull, hnv0⟩ := hlv
  have hlk := cutB_lookup B' n rn hnd hnc
  have hleaf : ∀ y ∈ rn.cs, ∃ ry, B'.ns !! y = some ry ∧ ry.cs = [] := by
    intro y hy; obtain ⟨ry, hry, -, hc, -⟩ := hall y hy; exact ⟨ry, hry, hc⟩
  obtain ⟨S3, hk3, hpr⟩ := kidsTree_prune B'.ns (cutB B' n rn).ns n rn.cs hleaf
    (fun r hr => by rw [hn] at hr; cases hr; rfl) S.length top S (Nat.le_refl _) hk
    (fun l hl hln hlc r hr => ⟨r, by rw [hlk l, if_neg hlc, if_neg hln]; exact hr, rfl⟩)
    (fun _ => ⟨cutRec rn, by rw [hlk n, if_neg hnc, if_pos rfl], rfl⟩)
    (fun h => absurd hnS h)
  obtain ⟨A, C, hSe, hS3e⟩ := hpr.1 hnS
  have hSnd : S.Nodup := kidsTree_nodup B'.ns top S hk
  rw [hSe] at hSnd
  simp only [List.append_assoc, List.cons_append] at hSnd
  obtain ⟨-, hnd2, hdisA⟩ := List.nodup_append.1 hSnd
  obtain ⟨hnCs, hnd3⟩ := List.nodup_cons.1 hnd2
  obtain ⟨-, -, hdisC⟩ := List.nodup_append.1 hnd3
  have hm1 : ∀ l ∈ S3, l ∈ S ∧ l ∉ rn.cs := by
    intro l hl
    rw [hS3e] at hl; rw [hSe]
    rcases List.mem_append.1 hl with hl | hl
    · refine ⟨List.mem_append_left _ (List.mem_append_left _ hl), fun hc => ?_⟩
      exact hdisA l hl l (List.mem_cons_of_mem _ (List.mem_append_left _ hc)) rfl
    · rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨by simp, hnc⟩
      · refine ⟨by simp [hl], fun hc => hdisC l hc l hl rfl⟩
  have hm2 : ∀ l ∈ S, l ∉ rn.cs → l ∈ S3 := by
    intro l hl hlc
    rw [hSe] at hl; rw [hS3e]
    simp only [List.append_assoc, List.cons_append, List.mem_append, List.mem_cons] at hl ⊢
    rcases hl with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h hlc
    · exact Or.inr (Or.inr h)
  have hnS3 : n ∈ S3 := by rw [hS3e]; simp
  refine ⟨?_, ?_⟩
  rotate_left
  · refine ⟨S3, ⟨p, top, upPath_cut B' n rn hnd hnc hn p top hu, hpnd, hk3, fun l hl hlS => ?_⟩,
      fun l hl => ?_, fun h => ⟨hnS3, hm2 _ (hpar h).1 (hpar h).2⟩, fun h => ?_, fun l r hl hlS => ?_⟩
    · by_cases hlc : l ∈ rn.cs
      · obtain ⟨ry, hry, -⟩ := hleaf l hlc
        refine ⟨staleRec ry, ?_, staleRec_noView ry⟩
        rw [hlk l, if_pos hlc, if_pos (onRootPath_of B' p top l hu hl), hry]; rfl
      · have hln : l ≠ n := fun e => hlS (e ▸ hnS3)
        have hlS0 : l ∉ S := fun h => hlS (hm2 l h hlc)
        obtain ⟨r, hr, hv⟩ := hq l hl hlS0
        exact ⟨r, by rw [hlk l, if_neg hlc, if_neg hln]; exact hr, hv⟩
    · obtain ⟨hlS, hlc⟩ := hm1 l hl
      obtain ⟨r, hr, hok⟩ := hSok l hlS
      by_cases hln : l = n
      · subst hln; rw [hn] at hr; cases hr
        refine ⟨cutRec rn, by rw [hlk l, if_neg hlc, if_pos rfl], ?_⟩
        obtain ⟨o1, o2, o3, o4⟩ := hok
        exact ⟨o1, o2, o3, o4⟩
      · exact ⟨r, by rw [hlk l, if_neg hlc, if_neg hln]; exact hr, hok⟩
    · obtain ⟨p1, hu1⟩ := hnull h
      exact ⟨p1, upPath_cut B' n rn hnd hnc hn p1 n hu1⟩
    · rw [hlk l] at hl
      by_cases hlc : l ∈ rn.cs
      · rw [if_pos hlc] at hl
        split at hl
        · obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hl; exact staleRec_noView r0
        · cases hl
      · rw [if_neg hlc] at hl
        have hln : l ≠ n := fun e => hlS (e ▸ hnS3)
        rw [if_neg hln] at hl
        exact hnv0 l r hl (fun h => hlS (hm2 l h hlc))
  · rw [setB_setB]
    apply spillG_setB W' txl txid T' ρ' F' bl B' (cutB B' n rn) hg hB rfl rfl
    right
    refine ⟨S3, ⟨p, top, upPath_cut B' n rn hnd hnc hn p top hu, hpnd, hk3, fun l hl hlS => ?_⟩, fun l hl => ?_⟩
    · by_cases hlc : l ∈ rn.cs
      · obtain ⟨ry, hry, -⟩ := hleaf l hlc
        refine ⟨staleRec ry, ?_, staleRec_noView ry⟩
        rw [hlk l, if_pos hlc, if_pos (onRootPath_of B' p top l hu hl), hry]; rfl
      · have hln : l ≠ n := fun e => hlS (e ▸ hnS3)
        have hlS0 : l ∉ S := fun h => hlS (hm2 l h hlc)
        obtain ⟨r, hr, hv⟩ := hq l hl hlS0
        exact ⟨r, by rw [hlk l, if_neg hlc, if_neg hln]; exact hr, hv⟩
    · obtain ⟨hlS, hlc⟩ := hm1 l hl
      obtain ⟨r, hr, hok⟩ := hSok l hlS
      by_cases hln : l = n
      · subst hln; rw [hn] at hr; cases hr
        refine ⟨cutRec rn, by rw [hlk l, if_neg hlc, if_pos rfl], ?_⟩
        obtain ⟨o1, o2, o3, o4⟩ := hok
        exact ⟨o1, o2, o3, o4⟩
      · exact ⟨r, by rw [hlk l, if_neg hlc, if_neg hln]; exact hr, hok⟩


end own

end bbolt
end EtcdGrove
end Perennial
