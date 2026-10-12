/-
`Bucket.dereference` (pure): what one call does to the buckets, and how the calls compose.

A call on the bucket `x` with the buckets `bs` (`readyAt bs x`: the buckets reachable from `x`
are in `bs`, each ready for `node.dereference`; `depOK dep bs`: a cached child is lower than its
parent, so no call reaches its caller) gives back `bs'`: every bucket the same or dereferenced
(`derefM`), those reachable from `x` dereferenced (`derefFrom`). A call on a child is given the
buckets but its parent (`child_pre`, `child_post`); the parent then is dereferenced too (`final`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxDeref

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt

section pure
variable [ext : FfiSyntax]

/-! ### Node trees -/

/-- The node `l` of `ns` is in `ns'`, with the same children and parent. -/
def nAgree (ns ns' : GMap Loc NRec) (l : Loc) : Prop :=
  ∀ r, ns !! l = some r → ∃ r', ns' !! l = some r' ∧ r'.cs = r.cs ∧ r'.nv.parent' = r.nv.parent'

theorem upPath_det (ns : GMap Loc NRec) {l : Loc} {p : List Loc} {t : Loc} (h : upPath ns l p t) :
    ∀ {p' t'}, upPath ns l p' t' → p = p' ∧ t = t' := by
  induction h with
  | self l r hr hp =>
    intro p' t' h2
    cases h2 with
    | self _ r2 hr2 _ => exact ⟨rfl, rfl⟩
    | up _ r2 _ _ hr2 hp2 _ =>
      rw [hr] at hr2; cases hr2; exact absurd hp hp2
  | up l r p t hr hp hu ih =>
    intro p' t' h2
    cases h2 with
    | self _ r2 hr2 hp2 =>
      rw [hr] at hr2; cases hr2; exact absurd hp2 hp
    | up _ r2 p2 t2 hr2 _ hu2 =>
      rw [hr] at hr2; cases hr2
      obtain ⟨e1, e2⟩ := ih hu2
      exact ⟨by rw [e1], e2⟩

theorem upPath_mono (ns ns' : GMap Loc NRec) {l : Loc} {p : List Loc} {t : Loc}
    (h : upPath ns l p t) : (∀ x ∈ p, nAgree ns ns' x) → upPath ns' l p t := by
  induction h with
  | self l r hr hp =>
    intro ha
    obtain ⟨r', hr', -, hpar⟩ := ha l List.mem_cons_self r hr
    exact upPath.self l r' hr' (by rw [hpar]; exact hp)
  | up l r p t hr hp hu ih =>
    intro ha
    obtain ⟨r', hr', -, hpar⟩ := ha l List.mem_cons_self r hr
    refine upPath.up l r' p t hr' (by rw [hpar]; exact hp) ?_
    rw [hpar]; exact ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))

theorem flatten_sub_length {α : Type} (ss : List (List α)) (s : List α) (h : s ∈ ss) :
    s.length ≤ ss.flatten.length := by
  induction ss with
  | nil => simp at h
  | cons a ss ih =>
    simp only [List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with e | h
    · subst e; omega
    · have := ih h; omega

theorem kidsTree_mono (ns ns' : GMap Loc NRec) :
    ∀ (n : Nat) (t : Loc) (S : List Loc), S.length ≤ n → (∀ l ∈ S, nAgree ns ns' l) →
    kidsTree ns t S → kidsTree ns' t S := by
  intro n
  induction n with
  | zero =>
    intro t S hl _ hk
    cases hk with
    | mk _ _ _ _ _ _ => simp at hl
  | succ n ih =>
    intro t S hl ha hk
    cases hk with
    | mk _ r subs hr hF hnd =>
      obtain ⟨r', hr', hcs, -⟩ := ha t List.mem_cons_self r hr
      refine kidsTree.mk t r' subs hr' ?_ hnd
      rw [hcs]
      have hsub : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
          ss.flatten.length ≤ n → (∀ l ∈ ss.flatten, nAgree ns ns' l) →
          List.Forall₂ (kidsTree ns') cs ss := by
        intro cs ss hF2
        induction hF2 with
        | nil => intro _ _; exact List.Forall₂.nil
        | @cons c s cs' ss' hk2 _ ih2 =>
          intro hlen ha2
          simp only [List.flatten_cons, List.length_append] at hlen
          refine List.Forall₂.cons (ih c s (by omega)
            (fun l hl => ha2 l (by simp only [List.flatten_cons, List.mem_append]; exact Or.inl hl)) hk2)
            (ih2 (by omega) (fun l hl => ha2 l (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hl)))
      exact hsub r.cs subs hF (by simp only [List.length_cons] at hl; omega)
        (fun l hl => ha l (List.mem_cons_of_mem _ hl))

theorem kidsTree_det (ns : GMap Loc NRec) :
    ∀ (n : Nat) (t : Loc) (S S' : List Loc), S.length ≤ n →
    kidsTree ns t S → kidsTree ns t S' → S = S' := by
  intro n
  induction n with
  | zero =>
    intro t S S' hl hk _
    cases hk with
    | mk _ _ _ _ _ _ => simp at hl
  | succ n ih =>
    intro t S S' hl hk hk'
    cases hk with
    | mk _ r subs hr hF _ =>
      cases hk' with
      | mk _ r2 subs2 hr2 hF2 _ =>
        rw [hr] at hr2; cases hr2
        have hsub : ∀ (cs : List Loc) (ss ss' : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
            List.Forall₂ (kidsTree ns) cs ss' → ss.flatten.length ≤ n → ss = ss' := by
          intro cs ss ss' h1
          induction h1 generalizing ss' with
          | nil => intro h2 _; cases h2; rfl
          | @cons c s cs' ss1 hk1 _ ih1 =>
            intro h2 hlen
            cases h2 with
            | cons hk2 hr2 =>
              simp only [List.flatten_cons, List.length_append] at hlen
              rw [ih c _ _ (by omega) hk1 hk2, ih1 _ hr2 (by omega)]
        rw [hsub r.cs subs subs2 hF hF2 (by simp only [List.length_cons] at hl; omega)]

theorem liveNodes_det (B : BRec) (S S' : List Loc) (h : liveNodes B S) (h' : liveNodes B S') :
    S = S' := by
  obtain ⟨p, top, hu, -, hk, -⟩ := h
  obtain ⟨p', top', hu', -, hk', -⟩ := h'
  obtain ⟨-, rfl⟩ := upPath_det B.ns hu hu'
  exact kidsTree_det B.ns S.length top S S' (Nat.le_refl _) hk hk'

theorem liveNodes_mono (B B' : BRec) (S : List Loc) (hbv : B'.bv = B.bv)
    (ha : ∀ l ∈ S, nAgree B.ns B'.ns l) (h : liveNodes B S) : liveNodes B' S := by
  obtain ⟨p, top, hu, hnd, hk, hpS⟩ := h
  refine ⟨p, top, ?_, hnd, kidsTree_mono B.ns B'.ns S.length top S (Nat.le_refl _) ha hk, hpS⟩
  rw [hbv]; exact upPath_mono B.ns B'.ns hu (fun x hx => ha x (hpS x hx))

/-! ### Dereferenced nodes and buckets -/

theorem derefNode_agree (r r' : NRec) (h : derefNode r r') :
    r'.nv.parent' = r.nv.parent' ∧ r'.cs = r.cs ∧ r'.nv.bucket' = r.nv.bucket' ∧
      r'.nv.pgid' = r.nv.pgid' := by
  obtain ⟨h1, -, h3, -⟩ := h
  exact ⟨by rw [h1], h3, by rw [h1], by rw [h1]⟩

theorem ownFresh_idem (w : WEntry) : ownFresh (ownFresh w) = ownFresh w := rfl

theorem derefNode_trans (r r' r'' : NRec) (h : derefNode r r') (h' : derefNode r' r'') :
    derefNode r r'' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h'
  refine ⟨?_, ?_, b3.trans a3, b4.trans a4, fun e => b5 (a5 e), b6, b7⟩
  · calc r''.nv = { r'.nv with inodes' := r''.nv.inodes', key' := r''.nv.key' } := b1
      _ = { r.nv with inodes' := r''.nv.inodes', key' := r''.nv.key' } := by rw [a1]
  · rw [b2, a2, List.map_map]; rfl

theorem derefOK_derefNode (bl : Loc) (r r' : NRec) (h : derefOK bl r) (hd : derefNode r r') :
    derefOK bl r' := by
  obtain ⟨hb, -, hws, hk⟩ := h
  obtain ⟨hpar, -, hbk, hpg⟩ := derefNode_agree r r' hd
  obtain ⟨-, h2, -, h4, h5, h6, h7⟩ := hd
  refine ⟨hbk.trans hb, h7, ?_, ?_⟩
  · intro w hw
    rw [h2] at hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    exact ⟨by simp [ownFresh], by simp [ownFresh], (hws w0 hw0).2.2⟩
  · by_cases e : r'.nv.key' = slice.nil
    · exact Or.inl e
    · rcases hk with hk | ⟨-, hk⟩
      · exact absurd (h5 hk) e
      · refine Or.inr ⟨by rw [h6]; simp, ?_⟩
        rw [hpg, h4]; exact hk

theorem staleOf_idem (s : Src) : staleOf (staleOf s) = staleOf s := by
  cases s <;> rfl

theorem derefBkt_live (B B' : BRec) (S : List Loc) (h : derefBkt B B') (hn : B.bv.rootNode' ≠ null)
    (hl : liveNodes B S) : liveNodes B' S := by
  obtain ⟨hbv, -, -, -, -, -, hns, hlive⟩ := h
  refine liveNodes_mono B B' S hbv ?_ hl
  intro l hS r hr
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hlive hn S hl l hS)
  obtain ⟨r0, hr0, hd⟩ := hns l r' hr'
  rw [hr] at hr0; cases hr0
  obtain ⟨hpar, hcs, -, -⟩ := derefNode_agree r r' hd
  exact ⟨r', hr', hcs, hpar⟩

theorem derefBkt_trans (B B' B'' : BRec) (h : derefBkt B B') (h' : derefBkt B' B'') :
    derefBkt B B'' := by
  have hlv := derefBkt_live B B'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h'
  refine ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, ?_, ?_, ?_⟩
  · rw [b6, a6, staleOf_idem]
  · intro l r'' hr''
    obtain ⟨r', hr', hd'⟩ := b7 l r'' hr''
    obtain ⟨r, hr, hd⟩ := a7 l r' hr'
    exact ⟨r, hr, derefNode_trans r r' r'' hd hd'⟩
  · intro hn S hl
    have hn' : B'.bv.rootNode' ≠ null := by rw [a1]; exact hn
    exact b8 hn' S (hlv S ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hn hl)

/-- The bucket `y` (record `Y`) is ready for `dereference`: its live nodes hold their bytes. -/
def nodesReady (y : Loc) (Y : BRec) : Prop :=
  Y.bv.rootNode' = null ∨ ∃ S, liveNodes Y S ∧ ∀ l ∈ S, ∃ r, Y.ns !! l = some r ∧ derefOK y r

theorem derefBkt_ready (y : Loc) (Y Y' : BRec) (h : nodesReady y Y) (hd : derefBkt Y Y') :
    nodesReady y Y' := by
  have hbv := hd.1
  rcases h with h | ⟨S, hl, hok⟩
  · left; rw [hbv]; exact h
  · by_cases hn : Y.bv.rootNode' = null
    · left; rw [hbv]; exact hn
    right
    refine ⟨S, derefBkt_live Y Y' S hd hn hl, fun l hS => ?_⟩
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hd.2.2.2.2.2.2.2 hn S hl l hS)
    obtain ⟨r0, hr0, hdn⟩ := hd.2.2.2.2.2.2.1 l r' hr'
    obtain ⟨r, hr, hok1⟩ := hok l hS
    rw [hr] at hr0; cases hr0
    exact ⟨r', hr', derefOK_derefNode y _ r' hok1 hdn⟩

/-- `B'` is `B` or `B` dereferenced. -/
def derefStar (B B' : BRec) : Prop := B' = B ∨ derefBkt B B'

theorem derefStar_bm (B B' : BRec) (h : derefStar B B') : B'.bm = B.bm ∧ B'.bv = B.bv := by
  rcases h with rfl | h
  · exact ⟨rfl, rfl⟩
  · exact ⟨h.2.2.2.1, h.1⟩

theorem derefStar_trans (B B' B'' : BRec) (h : derefStar B B') (h' : derefStar B' B'') :
    derefStar B B'' := by
  rcases h with rfl | h
  · exact h'
  rcases h' with rfl | h'
  · exact Or.inr h
  · exact Or.inr (derefBkt_trans B B' B'' h h')

theorem star_bkt (B B' B'' : BRec) (h : derefStar B B') (h' : derefBkt B' B'') : derefBkt B B'' := by
  rcases h with rfl | h
  · exact h'
  · exact derefBkt_trans B B' B'' h h'

theorem bkt_star (B B' B'' : BRec) (h : derefBkt B B') (h' : derefStar B' B'') : derefBkt B B'' := by
  rcases h' with rfl | h'
  · exact h
  · exact derefBkt_trans B B' B'' h h'

theorem derefStar_ready (y : Loc) (Y Y' : BRec) (h : nodesReady y Y) (hd : derefStar Y Y') :
    nodesReady y Y' := by
  rcases hd with rfl | hd
  · exact h
  · exact derefBkt_ready y Y Y' h hd

/-! ### Maps of buckets -/

/-- The bucket `y` is `x` or cached under one reachable from it, in `bs`. -/
inductive reachB (bs : GMap Loc BRec) (x : Loc) : Loc → Prop
  | root : reachB bs x x
  | child (y : Loc) (Y : BRec) (name : GoString) (c : Loc) : reachB bs x y →
      bs !! y = some Y → Y.bm !! name = some c → reachB bs x c

/-- A cached child is lower than its parent. -/
def depOK (dep : Loc → Nat) (bs : GMap Loc BRec) : Prop :=
  ∀ y Y name c, bs !! y = some Y → Y.bm !! name = some c → dep c < dep y

/-- The buckets reachable from `x` are in `bs`, ready for `dereference`. -/
def readyAt (bs : GMap Loc BRec) (x : Loc) : Prop :=
  ∀ y, reachB bs x y → ∃ Y, bs !! y = some Y ∧ nodesReady y Y

/-- The buckets are of the transaction `txl`. -/
def txOK (txl : Loc) (bs : GMap Loc BRec) : Prop :=
  ∀ y Y, bs !! y = some Y → Y.bv.tx' = txl

/-- Every bucket of `bs` is the same or dereferenced in `bs'`. -/
def derefM (bs bs' : GMap Loc BRec) : Prop :=
  (∀ y, (bs !! y).isSome ↔ (bs' !! y).isSome) ∧
  ∀ y Y Y', bs !! y = some Y → bs' !! y = some Y' → derefStar Y Y'

/-- The buckets reachable from `x` in `bs` are dereferenced in `bs'`. -/
def derefFrom (bs bs' : GMap Loc BRec) (x : Loc) : Prop :=
  ∀ y, reachB bs x y → ∃ Y Y', bs !! y = some Y ∧ bs' !! y = some Y' ∧ derefBkt Y Y'

theorem derefM_refl (bs : GMap Loc BRec) : derefM bs bs :=
  ⟨fun _ => Iff.rfl, fun y Y Y' h h' => by rw [h] at h'; cases h'; exact Or.inl rfl⟩

theorem derefM_get (bs bs' : GMap Loc BRec) (h : derefM bs bs') (y : Loc) (Y' : BRec)
    (hy : bs' !! y = some Y') : ∃ Y, bs !! y = some Y ∧ derefStar Y Y' := by
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 ((h.1 y).2 (by rw [hy]; rfl))
  exact ⟨Y, hY, h.2 y Y Y' hY hy⟩

theorem derefM_get' (bs bs' : GMap Loc BRec) (h : derefM bs bs') (y : Loc) (Y : BRec)
    (hy : bs !! y = some Y) : ∃ Y', bs' !! y = some Y' ∧ derefStar Y Y' := by
  obtain ⟨Y', hY'⟩ := Option.isSome_iff_exists.1 ((h.1 y).1 (by rw [hy]; rfl))
  exact ⟨Y', hY', h.2 y Y Y' hy hY'⟩

theorem derefM_trans (A B C : GMap Loc BRec) (h : derefM A B) (h' : derefM B C) : derefM A C := by
  refine ⟨fun y => (h.1 y).trans (h'.1 y), fun y Y Y'' hY hY'' => ?_⟩
  obtain ⟨Y', hY', hd⟩ := derefM_get' A B h y Y hY
  exact derefStar_trans Y Y' Y'' hd (h'.2 y Y' Y'' hY' hY'')

theorem reach_dep (dep : Loc → Nat) (bs : GMap Loc BRec) (hd : depOK dep bs) {x y : Loc}
    (h : reachB bs x y) : dep y ≤ dep x := by
  induction h with
  | root => exact Nat.le_refl _
  | child y Y name c _ hY hc ih => have := hd y Y name c hY hc; omega

theorem reach_transfer (dep : Loc → Nat) (A A' : GMap Loc BRec) (hd : depOK dep A) (k : Nat)
    (hk : ∀ y Y, dep y ≤ k → A !! y = some Y → ∃ Y', A' !! y = some Y' ∧ Y'.bm = Y.bm)
    {x y : Loc} (hx : dep x ≤ k) (h : reachB A x y) : reachB A' x y := by
  have hdep := fun {z} (h : reachB A x z) => reach_dep dep A hd h
  induction h with
  | root => exact reachB.root
  | child y Y name c hr hY hc ih =>
    obtain ⟨Y', hY', hbm⟩ := hk y Y (by have := hdep hr; omega) hY
    exact reachB.child y Y' name c ih hY' (by rw [hbm]; exact hc)

theorem reach_head (bs : GMap Loc BRec) {x c y : Loc} (X : BRec) (name : GoString)
    (hX : bs !! x = some X) (hc : X.bm !! name = some c) (h : reachB bs c y) : reachB bs x y := by
  induction h with
  | root => exact reachB.child x X name c reachB.root hX hc
  | child y Y name' c' _ hY hc' ih => exact reachB.child y Y name' c' ih hY hc'

theorem reach_split (bs : GMap Loc BRec) {x y : Loc} (h : reachB bs x y) :
    y = x ∨ ∃ X name c, bs !! x = some X ∧ X.bm !! name = some c ∧ reachB bs c y := by
  induction h with
  | root => exact Or.inl rfl
  | child y Y name c _ hY hc ih =>
    rcases ih with rfl | ⟨X, n0, c0, hX, hc0, hr⟩
    · exact Or.inr ⟨Y, name, c, hY, hc, reachB.root⟩
    · exact Or.inr ⟨X, n0, c0, hX, hc0, reachB.child y Y name c hr hY hc⟩

/-! ### Composing the calls -/

/-- A child `c` of `x` (record `B`), called with the buckets but `x` (dereferenced to `R`). -/
theorem child_pre (dep : Loc → Nat) (txl x : Loc) (bs R : GMap Loc BRec) (B : BRec)
    (name : GoString) (c : Loc) (hB : bs !! x = some B) (hdep : depOK dep bs)
    (hready : readyAt bs x) (htx : txOK txl bs) (hR : derefM (GMap.delete x bs) R)
    (hc : B.bm !! name = some c) :
    dep c < dep x ∧ depOK dep R ∧ readyAt R c ∧ txOK txl R := by
  have hcx := hdep x B name c hB hc
  have hRb : ∀ y Y', R !! y = some Y' → ∃ Y, bs !! y = some Y ∧ y ≠ x ∧ derefStar Y Y' := by
    intro y Y' hy
    obtain ⟨Y, hY, hd⟩ := derefM_get _ R hR y Y' hy
    have hne : x ≠ y := by intro e; subst e; rw [GMap.lookup_delete] at hY; cases hY
    rw [GMap.lookup_delete_ne _ hne] at hY
    exact ⟨Y, hY, Ne.symm hne, hd⟩
  have hdR : depOK dep R := by
    intro y Y' n0 c0 hy hc0
    obtain ⟨Y, hY, -, hd⟩ := hRb y Y' hy
    rw [(derefStar_bm Y Y' hd).1] at hc0
    exact hdep y Y n0 c0 hY hc0
  refine ⟨hcx, hdR, ?_, ?_⟩
  · intro y hr
    have hr' : reachB bs c y := reach_transfer dep R bs hdR (dep c) (fun y Y' _ hy => by
      obtain ⟨Y, hY, -, hd⟩ := hRb y Y' hy
      exact ⟨Y, hY, (derefStar_bm Y Y' hd).1.symm⟩) (Nat.le_refl _) hr
    obtain ⟨Y, hY, hrd⟩ := hready y (reach_head bs B name hB hc hr')
    have hyx : x ≠ y := by
      intro e; subst e; have := reach_dep dep bs hdep hr'; omega
    obtain ⟨Y', hY', hd⟩ := derefM_get' _ R hR y Y (by rw [GMap.lookup_delete_ne _ hyx]; exact hY)
    exact ⟨Y', hY', derefStar_ready y Y Y' hrd hd⟩
  · intro y Y' hy
    obtain ⟨Y, hY, -, hd⟩ := hRb y Y' hy
    rw [(derefStar_bm Y Y' hd).2]; exact htx y Y hY

/-- After a child's call: the buckets dereferenced so far, and those the call reached. -/
theorem child_post (dep : Loc → Nat) (R0 R R' : GMap Loc BRec) (c : Loc) (hdep : depOK dep R0)
    (hR : derefM R0 R) (hR' : derefM R R') (hF : derefFrom R R' c) :
    derefM R0 R' ∧ derefFrom R0 R' c ∧ ∀ c', derefFrom R0 R c' → derefFrom R0 R' c' := by
  refine ⟨derefM_trans R0 R R' hR hR', ?_, ?_⟩
  · intro y hr
    have hr' : reachB R c y := reach_transfer dep R0 R hdep (dep c) (fun y Y _ hy => by
      obtain ⟨Y', hY', hd⟩ := derefM_get' R0 R hR y Y hy
      exact ⟨Y', hY', (derefStar_bm Y Y' hd).1⟩) (Nat.le_refl _) hr
    obtain ⟨Yi, Y'', hYi, hY'', hd⟩ := hF y hr'
    obtain ⟨Y, hY, hs⟩ := derefM_get R0 R hR y Yi hYi
    exact ⟨Y, Y'', hY, hY'', star_bkt Y Yi Y'' hs hd⟩
  · intro c' hF' y hr
    obtain ⟨Y, Yi, hY, hYi, hd⟩ := hF' y hr
    obtain ⟨Y'', hY'', hs⟩ := derefM_get' R R' hR' y Yi hYi
    exact ⟨Y, Y'', hY, hY'', bkt_star Y Yi Y'' hd hs⟩

/-- After the children's calls: `x` and the buckets reachable from it are dereferenced. -/
theorem final (dep : Loc → Nat) (x : Loc) (bs R : GMap Loc BRec) (B B1 : BRec)
    (hB : bs !! x = some B) (hdep : depOK dep bs) (hbkt : derefBkt B B1)
    (hR : derefM (GMap.delete x bs) R)
    (hall : ∀ name c, B.bm !! name = some c → derefFrom (GMap.delete x bs) R c) :
    derefM bs (<[x := B1]> R) ∧ derefFrom bs (<[x := B1]> R) x := by
  refine ⟨⟨fun y => ?_, fun y Y Y' hY hY' => ?_⟩, fun y hr => ?_⟩
  · by_cases e : x = y
    · subst e; rw [hB, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ e, ← hR.1 y, GMap.lookup_delete_ne _ e]
  · by_cases e : x = y
    · subst e; rw [hB] at hY; cases hY; rw [GMap.lookup_insert] at hY'; cases hY'
      exact Or.inr hbkt
    · rw [GMap.lookup_insert_ne _ _ e] at hY'
      exact hR.2 y Y Y' (by rw [GMap.lookup_delete_ne _ e]; exact hY) hY'
  · rcases reach_split bs hr with rfl | ⟨X, name, c, hX, hc, hr'⟩
    · exact ⟨B, B1, hB, GMap.lookup_insert _ _ _, hbkt⟩
    rw [hB] at hX; cases hX
    have hcx := hdep x B name c hB hc
    have hr2 : reachB (GMap.delete x bs) c y :=
      reach_transfer dep bs _ hdep (dep c) (fun z Z hz hZ => by
        have hne : x ≠ z := by intro e; subst e; omega
        exact ⟨Z, by rw [GMap.lookup_delete_ne _ hne]; exact hZ, rfl⟩) (Nat.le_refl _) hr'
    have hyx : x ≠ y := by
      intro e; subst e; have := reach_dep dep bs hdep hr'; omega
    obtain ⟨Y, Y', hY, hY', hd⟩ := hall name c hc y hr2
    rw [GMap.lookup_delete_ne _ hyx] at hY
    exact ⟨Y, Y', hY, by rw [GMap.lookup_insert_ne _ _ hyx]; exact hY', hd⟩

theorem bktReach_reachB (T : WTx) (rl y : Loc) (h : bktReach T rl y) : reachB T.bs rl y := by
  induction h with
  | root => exact reachB.root
  | child bl B name c _ hB hc ih => exact reachB.child bl B name c ih hB hc

/-- What the transaction's call is given. -/
theorem top_pre (T : WTx) (rl : Loc) (h : derefReady T rl) :
    ∃ dep, depOK dep T.bs ∧ readyAt T.bs rl := by
  obtain ⟨hrl, -, ⟨dep, hdep⟩, hb⟩ := h
  refine ⟨dep, fun y Y name c hY hc => hdep y Y name c hY hc, fun y hr => ?_⟩
  have hin : (T.bs !! y).isSome := by
    cases hr with
    | root => exact hrl
    | child y0 Y0 name _ _ hY0 hc => exact (hb y0 Y0 hY0).2 name _ hc
  obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 hin
  exact ⟨Y, hY, (hb y Y hY).1⟩

/-- What the transaction's call does. -/
theorem top_post (T : WTx) (rl : Loc) (bs' : GMap Loc BRec) (st' : TxStats) (h : derefReady T rl)
    (hM : derefM T.bs bs') (hF : derefFrom T.bs bs' rl) :
    derefRel T { T with bs := bs', t := { T.t with stats' := st' } } := by
  refine ⟨rfl, rfl, rfl, rfl, hM.1, fun bl B B' hB hB' => ?_⟩
  obtain ⟨Y, Y', hY, hY', hd⟩ := hF bl (bktReach_reachB T rl bl (h.2.1 bl (by rw [hB]; rfl)))
  rw [hB] at hY; cases hY
  change bs' !! bl = some B' at hB'
  rw [hB'] at hY'; cases hY'
  exact hd

/-- A bucket's own step: its tree's nodes dereferenced (`M`), the others dropped. -/
theorem own_step (B : BRec) (S : List Loc) (M : GMap Loc NRec) (hl : liveNodes B S)
    (hM : (∀ l, (M !! l).isSome ↔ l ∈ S) ∧ ∀ l r', M !! l = some r' → ∃ r, B.ns !! l = some r ∧ derefNode r r') :
    derefBkt B { B with ns := M, isrc := staleOf B.isrc } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hM.2, fun _ S' hl' l hS => ?_⟩
  rw [liveNodes_det B S' S hl' hl] at hS
  exact (hM.1 l).2 hS

/-- A bucket without a root node: its nodes dropped. -/
theorem own_step_nil (B : BRec) (hn : B.bv.rootNode' = null) :
    derefBkt B { B with ns := ∅, isrc := staleOf B.isrc } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun l r' h => by simp at h, fun h => absurd hn h⟩

end pure

end bbolt
end EtcdGrove
end Perennial
