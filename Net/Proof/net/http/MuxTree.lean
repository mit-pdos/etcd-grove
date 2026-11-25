/-
net/http's Go 1.22 matcher (`routing_tree.go`, the `ServeMux`'s `tree`) on literal path patterns
(`litPat`: `/`-initial, every byte a `pathByte`, so no method, host, wildcard or escape).

* `Seg`, `pathSegs p`: a pattern's segments as `parsePattern` makes them (a literal per `/`, an
  anonymous multi wildcard for a trailing `/`), which is also how `firstSegment` splits a path;
  `patKeys p`: the keys from the root to its node (the host `""`, the method `""`, the segments).
* `wp_firstSegment`, `wp_pathUnescape`: on `/`-initial paths without `%`.
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.net.http.RequestDefs
public import Net.Proof.net.http.MuxMapping
public import Perennial.Proof.strings.Base
public import Spec.net.url.PathUnescape
public import Perennial.Spec.strings.IndexByte
public import Perennial.Proof.internal.bytealg.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

/-! ### Segments -/

/-- A segment of a literal pattern: a literal, or the anonymous multi wildcard of a trailing `/`. -/
inductive Seg where
  | lit (s : List w8)
  | multi
  deriving DecidableEq

/-- The segments of a `/`-initial path (see the file header). -/
def pathSegs : List w8 → List Seg
  | [] => []
  | _ :: rest =>
    if rest = [] then [.multi]
    else .lit (rest.takeWhile (· != W8 47)) :: pathSegs (rest.dropWhile (· != W8 47))
termination_by l => l.length
decreasing_by
  have := (List.dropWhile_suffix (p := (· != W8 47)) (l := rest)).length_le
  simp only [List.length_cons]; omega

/-- The keys from the root to a pattern's node (see the file header). -/
def patKeys (p : List w8) : List Seg := .lit [] :: .lit [] :: pathSegs p

/-- A literal path pattern (see the file header). -/
def litPat (p : List w8) : Prop := p.head? = some (W8 47) ∧ ∀ b ∈ p, pathByte b = true

theorem pathByte_ne_pct (b : w8) (h : pathByte b = true) : b ≠ W8 37 := by
  intro hb; subst hb; simp [pathByte] at h

/-- `firstSegment`'s split of a `/`-initial path. -/
def fsF (path : List w8) : List w8 × List w8 :=
  if path = [W8 47] then ([W8 47], [])
  else (path.tail.takeWhile (· != W8 47), path.tail.dropWhile (· != W8 47))

theorem slash_split_aux : ∀ s : List w8,
    ((∀ b ∈ s, b ≠ W8 47) ∧ s.takeWhile (· != W8 47) = s ∧ s.dropWhile (· != W8 47) = []) ∨
    (∃ i : Nat, i < s.length ∧ s[i]? = some (W8 47) ∧ (∀ j < i, s[j]? ≠ some (W8 47)) ∧
      s.takeWhile (· != W8 47) = s.take i ∧ s.dropWhile (· != W8 47) = s.drop i)
  | [] => .inl (by simp)
  | c :: s => by
    by_cases hc : c = W8 47
    · subst hc
      exact .inr ⟨0, by simp, by simp, by simp, by simp, by simp⟩
    · have hc' : (c != W8 47) = true := by simpa using hc
      rcases slash_split_aux s with ⟨h, htw, hdw⟩ | ⟨i, hi, hs, hmin, htw, hdw⟩
      · refine .inl ⟨?_, ?_, ?_⟩
        · simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hc, h⟩
        · simp only [List.takeWhile_cons, hc', ↓reduceIte, htw, List.take_succ_cons]
        · simp only [List.dropWhile_cons, hc', ↓reduceIte, hdw, List.drop_succ_cons]
      · refine .inr ⟨i + 1, by simp; omega, by simpa using hs, ?_, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero => simpa using hc
          | succ j => simpa using hmin j (by omega)
        · simp only [List.takeWhile_cons, hc', ↓reduceIte, htw, List.take_succ_cons]
        · simp only [List.dropWhile_cons, hc', ↓reduceIte, hdw, List.drop_succ_cons]

/-- How `firstSegment` finds the next `/` (see `fsF`). -/
theorem slash_split (s : List w8) :
    (internal.bytealg.indexByte s (W8 47) = -1 ∧
      s.takeWhile (· != W8 47) = s ∧ s.dropWhile (· != W8 47) = []) ∨
    (∃ i : Nat, i < s.length ∧ internal.bytealg.indexByte s (W8 47) = i ∧
      s.takeWhile (· != W8 47) = s.take i ∧ s.dropWhile (· != W8 47) = s.drop i) := by
  rcases slash_split_aux s with ⟨h, htw, hdw⟩ | ⟨i, hi, hs, hmin, htw, hdw⟩
  · left
    refine ⟨internal.bytealg.indexByte_eq_neg _ _ ?_, htw, hdw⟩
    intro j hj
    exact h _ (List.mem_of_getElem? hj) rfl
  · exact .inr ⟨i, hi, internal.bytealg.indexByte_eq_of _ _ i hs hmin, htw, hdw⟩

theorem unescCheck_noPct (s : List w8) (h : ∀ b ∈ s, b ≠ W8 37) :
    net.url.unescCheck net.url.mPathSegment s = none := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    have hc : c ≠ W8 37 := h c (by simp)
    have ih := ih (fun b hb => h b (by simp [hb]))
    conv => lhs; unfold net.url.unescCheck
    have : (c == W8 37) = false := by simpa using hc
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    split <;> first | exact ih | skip

theorem unescDecode_noPct (s : List w8) (h : ∀ b ∈ s, b ≠ W8 37) :
    net.url.unescDecode net.url.mPathSegment s = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    have hc : c ≠ W8 37 := h c (by simp)
    have ih := ih (fun b hb => h b (by simp [hb]))
    conv => lhs; unfold net.url.unescDecode
    have : (c == W8 37) = false := by simpa using hc
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    by_cases h43 : c = W8 43
    · subst h43; simp; exact ih
    · have : ¬ c = 43#8 := h43
      simp [this]; exact ih

/-- `unescape` of a string without `%`, in a path segment: itself. -/
theorem unescRes_noPct [GooseExts] [GoGlobalContext] (s : List w8) (h : ∀ b ∈ s, b ≠ W8 37) :
    net.url.unescRes s net.url.mPathSegment = (s, interface.nil) := by
  simp only [net.url.unescRes, net.url.unescapeF, unescCheck_noPct s h, unescDecode_noPct s h]

theorem dropWhile_shape (t : List w8) :
    t.dropWhile (· != W8 47) = [] ∨ (t.dropWhile (· != W8 47)).head? = some (W8 47) := by
  rcases slash_split_aux t with ⟨_, _, hdw⟩ | ⟨i, _, hs, _, _, hdw⟩
  · exact .inl hdw
  · exact .inr (by rw [hdw, List.head?_drop]; exact hs)

theorem pathSegs_slash : pathSegs [W8 47] = [.multi] := by rw [pathSegs]; simp

theorem pathSegs_cons (t : List w8) (ht : t ≠ []) :
    pathSegs (W8 47 :: t) =
      .lit (t.takeWhile (· != W8 47)) :: pathSegs (t.dropWhile (· != W8 47)) := by
  rw [pathSegs]; simp [ht]

/-- Induction along `pathSegs` (see the file header). -/
theorem pathSegs_ind (P : List w8 → Prop) (h0 : P []) (h1 : P [W8 47])
    (h2 : ∀ t, t ≠ [] → P (t.dropWhile (· != W8 47)) → P (W8 47 :: t)) :
    ∀ p, (p = [] ∨ p.head? = some (W8 47)) → P p := by
  intro p
  induction hn : p.length using Nat.strongRecOn generalizing p with
  | ind n ih =>
    intro hp
    rcases hp with rfl | hp
    · exact h0
    cases p with
    | nil => exact h0
    | cons c t =>
      simp at hp; subst hp
      by_cases ht : t = []
      · subst ht; exact h1
      · apply h2 t ht
        have := (List.dropWhile_suffix (p := (· != W8 47)) (l := t)).length_le
        exact ih _ (by simp at hn; omega) _ rfl (dropWhile_shape t)

/-- A literal segment holds no `/`, and only bytes of the path. -/
theorem lit_mem_pathSegs : ∀ p, (p = [] ∨ p.head? = some (W8 47)) →
    ∀ s, Seg.lit s ∈ pathSegs p → ∀ b ∈ s, b ≠ W8 47 ∧ b ∈ p := by
  apply pathSegs_ind
  · intro s hs; simp [pathSegs] at hs
  · intro s hs; rw [pathSegs_slash] at hs; simp at hs
  · intro t ht ih s hs b hb
    rw [pathSegs_cons t ht] at hs
    rcases List.mem_cons.mp hs with h | h
    · cases h
      refine ⟨by simpa using List.all_eq_true.mp List.all_takeWhile b hb, ?_⟩
      exact List.mem_cons_of_mem _ (List.takeWhile_subset _ hb)
    · obtain ⟨h1, h2⟩ := ih s h b hb
      exact ⟨h1, List.mem_cons_of_mem _ ((List.dropWhile_suffix (p := (· != W8 47))).subset h2)⟩

/-- The number of segments is the number of `/`s. -/
theorem pathSegs_length : ∀ p, (p = [] ∨ p.head? = some (W8 47)) →
    (pathSegs p).length = p.count (W8 47) := by
  apply pathSegs_ind
  · simp [pathSegs]
  · rw [pathSegs_slash]; simp
  · intro t ht ih
    rw [pathSegs_cons t ht, List.length_cons, ih, List.count_cons_self]
    have hsplit := List.takeWhile_append_dropWhile (p := (· != W8 47)) (l := t)
    have h0 : (t.takeWhile (· != W8 47)).count (W8 47) = 0 := by
      rw [List.count_eq_zero]; intro hm
      have := List.all_eq_true.mp List.all_takeWhile _ hm; simp at this
    conv => rhs; rw [← hsplit]
    rw [List.count_append, h0]; omega

/-- The last segment, when it is the multi wildcard, comes from a trailing `/`. -/
theorem pathSegs_last_multi : ∀ p, (p = [] ∨ p.head? = some (W8 47)) →
    (pathSegs p).getLast? = some .multi → p.getLast? = some (W8 47) := by
  apply pathSegs_ind
  · simp [pathSegs]
  · intro _; rfl
  · intro t ht ih h
    rw [pathSegs_cons t ht] at h
    rcases dropWhile_shape t with hd | hd
    · rw [hd] at h; simp [pathSegs] at h
    · have hne : t.dropWhile (· != W8 47) ≠ [] := by intro h'; rw [h'] at hd; simp at hd
      have hps : pathSegs (t.dropWhile (· != W8 47)) ≠ [] := by
        obtain ⟨c, u, hcu⟩ := List.exists_cons_of_ne_nil hne
        rw [hcu, List.head?_cons] at hd; rw [hcu]
        obtain rfl := Option.some.inj hd
        by_cases hu : u = []
        · subst hu; exact fun h => by have := pathSegs_slash; rw [h] at this; simp at this
        · intro h; have := pathSegs_cons u hu; rw [h] at this; simp at this
      obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil hps
      rw [hxl, List.getLast?_cons_cons, ← hxl] at h
      have := ih h
      have hsplit := List.takeWhile_append_dropWhile (p := (· != W8 47)) (l := t)
      rw [List.getLast?_cons, ← hsplit, List.getLast?_append, this]
      rfl

/-! ### The tree's state -/

section st
variable [GooseExts]

/-- A node of the tree (see the file header). -/
structure NodeSt where
  l : Loc
  pat : Loc
  h : GoInterface
  ms : MapSt
  kids : List (GoString × Loc)
  multi : Loc
  empty : Loc

/-- The tree: its nodes by their keys from the root, its patterns (string, `*pattern`, handler). -/
structure TreeSt where
  nodes : GMap (List Seg) NodeSt
  pats : List (List w8 × Loc × GoInterface)

/-- A node's address, `nil` for none. -/
def locOf (o : Option NodeSt) : Loc := (o.map NodeSt.l).getD null

/-- What the tree's state says of its nodes and patterns (see the file header). -/
def TreeSt.ok (root : Loc) (S : TreeSt) : Prop :=
  (∃ d, S.nodes !! [] = some d ∧ d.l = root) ∧
  (∀ e ∈ S.pats, litPat e.1) ∧ (S.pats.map Prod.fst).Nodup ∧
  (∀ k, (S.nodes !! k).isSome → k = [] ∨ ∃ e ∈ S.pats, k <+: patKeys e.1) ∧
  (∀ e ∈ S.pats, ∀ k, k <+: patKeys e.1 → (S.nodes !! k).isSome) ∧
  ∀ k d, S.nodes !! k = some d →
    d.l ≠ null ∧
    (∀ s, s ≠ [] → map.lookupL s d.kids = (S.nodes !! (k ++ [.lit s])).map NodeSt.l) ∧
    d.empty = locOf (S.nodes !! (k ++ [.lit []])) ∧
    d.multi = locOf (S.nodes !! (k ++ [.multi])) ∧
    (∀ e ∈ S.pats, patKeys e.1 = k → d.pat = e.2.1 ∧ d.h = e.2.2) ∧
    ((∀ e ∈ S.pats, patKeys e.1 ≠ k) → d.pat = null ∧ d.h = interface.nil)

/-- A segment's value. -/
def segVal : Seg → net.http.segment
  | .lit s => { s' := s, wild' := false, multi' := false }
  | .multi => { s' := [], wild' := true, multi' := true }

end st

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- `pathUnescape(s)` of a string without `%`: itself. -/
theorem wp_pathUnescape (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (s : List w8) (h : ∀ b ∈ s, b ≠ W8 37) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
      (App (Val (@! net.http.pathUnescape)) (Val #s))
    {{ RET #s; True }} := by
  wp_start
  wp_auto
  wp_apply wp_PathUnescape s
  rw [unescRes_noPct s h]
  wp_auto
  iapply HΦ
  ipureintro; trivial

/-- `firstSegment(path)` of a `/`-initial path without `%`. -/
theorem wp_firstSegment (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (path : List w8) (hp : path.head? = some (W8 47)) (h : ∀ b ∈ path, b ≠ W8 37) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.url }}
      (App (Val (@! net.http.firstSegment)) (Val #path))
    {{ RET (PairV #(fsF path).1 #(fsF path).2); True }} := by
  obtain ⟨t, rfl⟩ : ∃ t, path = W8 47 :: t := by
    cases path with
    | nil => simp at hp
    | cons c t => simp at hp; subst hp; exact ⟨t, rfl⟩
  by_cases ht : t = []
  · subst ht
    simp only [fsF, ↓reduceIte]
    wp_start
    wp_auto
    rw [show (47#8 : w8) = W8 47 from rfl]
    iapply HΦ
    ipureintro; trivial
  have hf : fsF (W8 47 :: t) = (t.takeWhile (· != W8 47), t.dropWhile (· != W8 47)) := by
    simp [fsF, ht]
  rw [hf]
  wp_start
  wp_auto
  rw [decide_eq_false (by simpa using ht)]
  wp_auto
  wp_apply wp_string_len as %Hl
  try wp_auto
  rw [ite_eq_left (by simp only [List.length_cons] at Hl ⊢; word)]
  have ht1 : List.take (sint.nat (W64 ↑(W8 47 :: t).length) - 1) (List.drop 1 (W8 47 :: t)) = t := by
    simp only [List.drop_succ_cons, List.drop_zero]; apply List.take_of_length_le
    simp only [List.length_cons] at Hl ⊢; word
  rw [ht1]
  wp_auto
  wp_apply wp_IndexByte
  have hpt : ∀ b ∈ t, b ≠ W8 37 := fun b hb => h b (by simp [hb])
  rcases slash_split t with ⟨hi, htw, hdw⟩ | ⟨i, hi, hidx, htw, hdw⟩
  · rw [hi]
    try wp_auto
    wp_apply wp_string_len as %_
    try wp_auto
    rw [ite_eq_left (by word)]
    have e1 : List.take (sint.nat (W64 ↑t.length) - 0) (List.drop 0 t) = t := by
      simp only [List.drop_zero]; apply List.take_of_length_le; word
    rw [e1]
    wp_apply wp_pathUnescape wp_PathUnescape t hpt $$ [$Hpkg]
    wp_apply wp_string_len as %_
    try wp_auto
    rw [ite_eq_left (by word)]
    have e2 : List.take (sint.nat (W64 ↑t.length) - sint.nat (W64 ↑t.length))
        (List.drop (sint.nat (W64 ↑t.length)) t) = [] := by simp
    rw [e2]
    try wp_auto
    rw [htw, hdw]
    iapply HΦ
    ipureintro; trivial
  · rw [hidx]
    have Hl' : t.length < 2 ^ 63 := by simp only [List.length_cons] at Hl; omega
    rw [decide_eq_false (by word)]
    try wp_auto
    rw [ite_eq_left (by word)]
    have e1 : List.take (sint.nat (W64 ↑i) - 0) (List.drop 0 t) = t.take i := by
      simp only [List.drop_zero, Nat.sub_zero]; congr 1; word
    rw [e1]
    wp_apply wp_pathUnescape wp_PathUnescape (t.take i)
      (fun b hb => hpt b (List.mem_of_mem_take hb)) $$ [$Hpkg]
    wp_apply wp_string_len as %_
    try wp_auto
    rw [ite_eq_left (by word)]
    have e2 : List.take (sint.nat (W64 ↑t.length) - sint.nat (W64 ↑i))
        (List.drop (sint.nat (W64 ↑i)) t) = t.drop i := by
      rw [show sint.nat (W64 ↑i) = i by word]
      apply List.take_of_length_le; simp only [List.length_drop]; word
    rw [e2]
    try wp_auto
    rw [htw, hdw]
    iapply HΦ
    ipureintro; trivial

/-- A node's fields at `dq` (see the file header). -/
def nodeRep (dq : DFrac) (d : NodeSt) : IProp GF :=
  iprop(structFieldRef net.http.routingNode go!"pattern" d.l ↦{dq} d.pat ∗
    structFieldRef net.http.routingNode go!"handler" d.l ↦{dq} d.h ∗
    mapRep dq (structFieldRef net.http.routingNode go!"children" d.l) d.ms d.kids ∗
    structFieldRef net.http.routingNode go!"multiChild" d.l ↦{dq} d.multi ∗
    structFieldRef net.http.routingNode go!"emptyChild" d.l ↦{dq} d.empty)

/-- A registered pattern's `*pattern` (persistent; see the file header). -/
def patRep (pp : Loc) (p : List w8) : IProp GF :=
  iprop(∃ (sl : GoSlice) (loc : GoString),
    pp ↦□ ({ str' := p, method' := [], host' := [], segments' := sl, loc' := loc } : net.http.pattern) ∗
    sl ↦*□ ((pathSegs p).map segVal))

instance patRep_persistent (pp : Loc) (p : List w8) : Persistent (patRep (GF := GF) (hG := hG) pp p) := by
  unfold patRep; infer_instance

/-- The tree at `dq` (see the file header). -/
def treeRep (dq : DFrac) (S : TreeSt) : IProp GF :=
  iprop(([∗map] _k ↦ d ∈ S.nodes, nodeRep dq d) ∗ [∗list] e ∈ S.pats, patRep e.2.1 e.1)

/-- `n.findChild(key)`. -/
theorem wp_findChild (dq : DFrac) (d : NodeSt) (key : List w8) :
    {{ nodeRep (GF := GF) (hG := hG) dq d }}
      (App (Val (d.l @!! go.GoType.PointerType net.http.routingNode.ty @!! go!"findChild")) (Val #key))
    {{ RET #(if key = [] then d.empty else (map.lookupL key d.kids).getD null); nodeRep dq d }} := by
  unfold nodeRep
  by_cases hk : key = []
  · simp only [hk, ↓reduceIte]
    wp_start as ⟨Hp, Hh, Hc, Hm, He⟩
    wp_auto
    iapply HΦ; iframe
  · simp only [hk, ↓reduceIte]
    wp_start as ⟨Hp, Hh, Hc, Hm, He⟩
    wp_auto
    rw [decide_eq_false hk]
    wp_auto
    wp_apply wp_mapping_find _ dq d.ms d.kids key $$ Hc as Hc
    iapply HΦ; iframe

/-- `nil.matchPath(path, matches)`: no match. -/
theorem wp_matchPath_nil (path : List w8) (ms : GoSlice) :
    {{ (True : IProp GF) }}
      (App (App (Val ((null : Loc) @!! go.GoType.PointerType net.http.routingNode.ty @!! go!"matchPath"))
        (Val #path)) (Val #ms))
    {{ RET (PairV #(null : Loc) #slice.nil); True }} := by
  wp_start
  wp_auto
  iapply HΦ; ipureintro; trivial

theorem TreeSt.ok.node_of_prefix {root : Loc} {S : TreeSt} (hok : S.ok root) {e : List w8 × Loc × GoInterface}
    (he : e ∈ S.pats) {k : List Seg} (hk : k <+: patKeys e.1) : ∃ d, S.nodes !! k = some d := by
  have := hok.2.2.2.2.1 e he k hk
  exact Option.isSome_iff_exists.mp this

theorem TreeSt.ok.nodes_no_slash {root : Loc} {S : TreeSt} (hok : S.ok root) (k : List Seg) (s : List w8)
    (hs : W8 47 ∈ s) : S.nodes !! (k ++ [Seg.lit s]) = none := by
  rcases h : S.nodes !! (k ++ [Seg.lit s]) with _ | d
  · rfl
  · exfalso
    rcases hok.2.2.2.1 _ (by rw [h]; rfl) with h0 | ⟨e, he, hpre⟩
    · simp at h0
    · have hm : Seg.lit s ∈ patKeys e.1 := hpre.subset (by simp)
      obtain ⟨hp1, _⟩ := hok.2.1 e he
      simp only [patKeys, List.mem_cons] at hm
      rcases hm with hm | hm | hm
      · cases hm; simp at hs
      · cases hm; simp at hs
      · have hp : e.1 = [] ∨ e.1.head? = some (W8 47) := .inr hp1
        exact (lit_mem_pathSegs e.1 hp s hm (W8 47) hs).1 rfl

theorem TreeSt.ok.node_l_ne {root : Loc} {S : TreeSt} (hok : S.ok root) {k : List Seg} {d : NodeSt}
    (hd : S.nodes !! k = some d) : locOf (S.nodes !! k) ≠ null := by
  rw [hd]; exact (hok.2.2.2.2.2 k d hd).1

/-- `p.lastSegment()` of a registered pattern. -/
theorem wp_lastSegment (pp : Loc) (p : List w8) (x : Seg) (hx : (pathSegs p).getLast? = some x) :
    {{ patRep (GF := GF) (hG := hG) pp p }}
      (App (Val (pp @!! go.GoType.PointerType net.http.pattern.ty @!! go!"lastSegment")) (Val #()))
    {{ RET #(segVal x); True }} := by
  unfold patRep
  wp_start as ⟨%sl, %loc, Hpp, #Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  iStructNamedPrefix Hpp "P"
  wp_auto
  have hne : (pathSegs p).length ≥ 1 := by
    cases h : pathSegs p with
    | nil => rw [h] at hx; simp at hx
    | cons _ _ => simp
  simp only [List.length_map] at Hlen
  rw [ite_eq_left (by word)]
  have hget : (List.map segVal (pathSegs p))[(sint.Z (sl.len - W64 1)).toNat]? = some (segVal x) := by
    rw [show (sint.Z (sl.len - W64 1)).toNat = (pathSegs p).length - 1 by word,
      List.getElem?_map, ← List.getLast?_eq_getElem?, hx]; rfl
  wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) _ _ (segVal x) (by word) $$ [Hsl] as _Hsl2
  · iframe #; ipureintro; exact hget
  iapply HΦ; ipureintro; trivial

/-- `n.matchPath(rest, ms)` on the way to a registered pattern's node, literal-first: that node. -/
theorem wp_matchPath_found (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (dq : DFrac) (root : Loc) (S : TreeSt) (hok : S.ok root) (e : List w8 × Loc × GoInterface)
    (he : e ∈ S.pats) :
    ∀ (rest : List w8) (k : List Seg) (d : NodeSt) (ms : GoSlice),
    S.nodes !! k = some d → k ++ pathSegs rest = patKeys e.1 →
    (rest = [] ∨ rest.head? = some (W8 47)) → (∀ b ∈ rest, b ≠ W8 37) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗ treeRep (GF := GF) (hG := hG) dq S }}
      (App (App (Val (d.l @!! go.GoType.PointerType net.http.routingNode.ty @!! go!"matchPath"))
        (Val #rest)) (Val #ms))
    {{ RET (PairV #(locOf (S.nodes !! patKeys e.1)) #ms); treeRep dq S }} := by
  intro rest
  induction hn : rest.length using Nat.strongRecOn generalizing rest with
  | ind n ih =>
  intro k d ms hd hk hr hpct
  obtain ⟨dP, hdP⟩ := hok.node_of_prefix he (k := patKeys e.1) (List.prefix_refl _)
  rw [show locOf (S.nodes !! patKeys e.1) = dP.l by rw [hdP]; rfl]
  obtain ⟨hl, hkids, hemp, hmul, hpat, hnopat⟩ := hok.2.2.2.2.2 k d hd
  unfold treeRep
  wp_start as ⟨HN, #HP⟩
  icases (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hd).1 $$ HN
    with ⟨Hd, HN⟩
  iunfold nodeRep at Hd
  icases Hd with ⟨Hp, Hh, Hc, Hm, He⟩
  wp_auto
  rw [decide_eq_false hl]
  wp_auto
  rcases hr with rfl | hr
  · have hk' : k = patKeys e.1 := by simpa [pathSegs] using hk
    obtain ⟨hpp, hph⟩ := hpat e he hk'.symm
    ihave Hpe := BigSepL.bigSepL_mem (Φ := fun e => patRep (GF := GF) (hG := hG) e.2.1 e.1) he $$ HP
    iunfold patRep at Hpe
    icases Hpe with ⟨%sl, %loc, #Hpp, #Hsl⟩
    ihave %hppn := typedPointsto_not_null _ _ _ $$ Hpp
    wp_auto
    rw [decide_eq_false (show d.pat ≠ null by rw [hpp]; exact hppn)]
    wp_auto
    obtain rfl : d = dP := by rw [hk'] at hd; exact Option.some.inj (hd.symm.trans hdP)
    iapply HΦ
    isplitl [HN Hp Hh Hc Hm He]
    · iapply (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hd).2
      iunfold nodeRep; iframe
    · iexact HP
  · obtain ⟨t, rfl⟩ : ∃ t, rest = W8 47 :: t := by
      cases rest with
      | nil => simp at hr
      | cons c t => rw [List.head?_cons] at hr; obtain rfl := Option.some.inj hr; exact ⟨t, rfl⟩
    rw [decide_eq_false (List.cons_ne_nil _ _)]
    wp_auto
    wp_apply wp_firstSegment wp_PathUnescape wp_IndexByte (W8 47 :: t) rfl hpct $$ [$Hpkg]
    ihave Hd : nodeRep (GF := GF) (hG := hG) dq d $$ [Hp Hh Hc Hm He]
    · iunfold nodeRep; iframe
    by_cases ht : t = []
    · subst ht
      have hf : fsF [W8 47] = ([W8 47], []) := by simp [fsF]
      rw [hf]
      have hk' : k ++ [Seg.multi] = patKeys e.1 := by rw [← hk, pathSegs_slash]
      dsimp only
      wp_apply wp_findChild dq d [W8 47] $$ Hd as Hd
      rw [hkids _ (List.cons_ne_nil _ _),
        hok.nodes_no_slash k [W8 47] (by simp), Option.map_none, Option.getD_none]
      wp_apply wp_matchPath_nil
      iunfold nodeRep at Hd
      icases Hd with ⟨Hp, Hh, Hc, Hm, He⟩
      wp_auto
      have hmP : d.multi = dP.l := by rw [hmul, hk', hdP]; rfl
      obtain ⟨hlP, -, -, -, hpatP, -⟩ := hok.2.2.2.2.2 _ dP hdP
      obtain ⟨hppP, -⟩ := hpatP e he rfl
      rw [hmP, decide_eq_false hlP]
      wp_auto
      have hne : patKeys e.1 ≠ k := by
        rw [← hk']; intro h; have := congrArg List.length h; simp at this
      have hdP' : get? (delete S.nodes k) (patKeys e.1) = some dP := by
        rw [Iris.Std.LawfulPartialMap.get?_delete, if_neg (Ne.symm hne)]; exact hdP
      icases (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hdP').1 $$ HN
        with ⟨HdP, HN2⟩
      iunfold nodeRep at HdP
      icases HdP with ⟨HpP, HhP, HcP, HmP, HeP⟩
      wp_auto
      rw [hppP]
      ihave Hpe := BigSepL.bigSepL_mem (Φ := fun e => patRep (GF := GF) (hG := hG) e.2.1 e.1) he $$ HP
      have hlast : (pathSegs e.1).getLast? = some Seg.multi := by
        have h2 : (k ++ [Seg.multi]).getLast? = some Seg.multi := by simp
        rw [hk'] at h2; simp only [patKeys] at h2
        cases hX : pathSegs e.1 with
        | nil => rw [hX] at h2; simp at h2
        | cons a l => rw [hX] at h2; simp only [List.getLast?_cons_cons] at h2; exact h2
      wp_apply wp_lastSegment e.2.1 e.1 Seg.multi hlast $$ Hpe
      iapply HΦ
      isplitl [HN2 Hp Hh Hc Hm He HpP HhP HcP HmP HeP]
      · iapply (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hd).2
        isplitl [Hp Hh Hc Hm He]
        · iunfold nodeRep; rw [hmP]; iframe
        · iapply (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hdP').2
          iunfold nodeRep; rw [hppP]; iframe
      · iexact HP
    · have hf : fsF (W8 47 :: t) = (t.takeWhile (· != W8 47), t.dropWhile (· != W8 47)) := by
        simp [fsF, ht]
      rw [hf]
      dsimp only
      have hk2 : (k ++ [Seg.lit (t.takeWhile (· != W8 47))]) ++ pathSegs (t.dropWhile (· != W8 47)) =
          patKeys e.1 := by
        rw [List.append_assoc, ← hk, pathSegs_cons t ht]; rfl
      obtain ⟨d', hd'⟩ := hok.node_of_prefix he (k := k ++ [Seg.lit (t.takeWhile (· != W8 47))]) ⟨_, hk2⟩
      have hres : (if t.takeWhile (· != W8 47) = [] then d.empty
          else (map.lookupL (t.takeWhile (· != W8 47)) d.kids).getD null) = d'.l := by
        by_cases h0 : t.takeWhile (· != W8 47) = []
        · rw [if_pos h0, hemp]; rw [h0] at hd'; rw [hd']; rfl
        · rw [if_neg h0, hkids _ h0, hd']; rfl
      wp_apply wp_findChild dq d (t.takeWhile (· != W8 47)) $$ Hd as Hd
      rw [hres]
      ihave HT : treeRep (GF := GF) (hG := hG) dq S $$ [HN Hd]
      · iunfold treeRep
        isplitl [HN Hd]
        · iapply (BigSepM.bigSepM_delete (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) dq d) hd).2
          iframe
        · iexact HP
      have hlt : (t.dropWhile (· != W8 47)).length < n := by
        have := (List.dropWhile_suffix (p := (· != W8 47)) (l := t)).length_le
        simp at hn; omega
      have hpct' : ∀ b ∈ t.dropWhile (· != W8 47), b ≠ W8 37 := fun b hb =>
        hpct b (List.mem_cons_of_mem _ ((List.dropWhile_suffix (p := (· != W8 47))).subset hb))
      wp_apply ih _ hlt _ rfl _ d' ms hd' hk2 (dropWhile_shape t) hpct' $$ [$Hpkg $HT] as HT
      rw [show locOf (S.nodes !! patKeys e.1) = dP.l by rw [hdP]; rfl]
      rw [decide_eq_false (hok.2.2.2.2.2 _ dP hdP).1]
      wp_auto
      iapply HΦ
      iunfold treeRep at HT
      iexact HT

end wp

end net.http
end Perennial
