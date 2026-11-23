/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Seq.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Pure lemmas: association lists (`Kept`), `precedes`, `lkDeps` and the dependency chains of a
sequence, `recOrder` (an order after the dependencies, given a potential), `recReaches`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Defs
public import Batteries.Data.List.Perm

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

theorem Kept.get_set (k : Kept) (x y : CmdId) (e : RecEntry) :
    (k.set x e).get y = if y = x then some e else k.get y := by
  unfold Kept.set Kept.get
  split
  · rename_i hx
    rw [List.find?_map]
    have hf : ((fun p : CmdId × RecEntry => p.1 == y) ∘
        (fun p : CmdId × RecEntry => if p.1 == x then (x, e) else p)) = (fun p => p.1 == y) := by
      funext p; by_cases h : p.1 = x <;> simp [h]
    rw [hf]
    by_cases hy : y = x
    · subst hy
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hx
      have := List.find?_some hq
      simp at this
      simp [hq, this]
    · simp only [hy, ite_false]
      cases hq : k.find? (fun p => p.1 == y) with
      | none => simp
      | some q =>
        have := List.find?_some hq
        simp at this
        have : q.1 ≠ x := by rw [this]; exact hy
        simp [this]
  · rename_i hx
    rw [List.find?_append]
    by_cases hy : y = x
    · subst hy
      cases h : k.find? (fun p => p.1 == y) with
      | none => simp
      | some q => rw [h] at hx; simp at hx
    · simp [hy, Ne.symm hy]

theorem lkDeps_snoc (s : Seq) (p : CmdId × Cmd) (c : Cmd) :
    lkDeps (s ++ [p]) c =
      if p.2.key = c.key then
        (if p.2.isPut then [p.1] else (if c.isPut then lkDeps s c ++ [p.1] else lkDeps s c))
      else lkDeps s c := by
  unfold lkDeps
  by_cases hk : p.2.key = c.key
  · simp only [List.filter_append, List.filter_cons, List.filter_nil, hk, beq_self_eq_true,
      ite_true, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    by_cases hp : p.2.isPut = true
    · simp [hp]
    · simp only [Bool.not_eq_true] at hp
      simp [hp, List.find?_cons, List.takeWhile_cons]
      split <;> simp
  · simp [hk]

theorem revInd {α : Type} {P : List α → Prop} (h0 : P []) (hs : ∀ l a, P l → P (l ++ [a])) :
    ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => simpa using h0
  | cons a l ih => simpa using hs _ a ih

theorem snoc_eq_append_cons {α : Type} (t t1 t2 : List α) (p q : α) :
    t ++ [p] = t1 ++ q :: t2 ↔
      (t2 = [] ∧ t1 = t ∧ q = p) ∨ (∃ t2', t2 = t2' ++ [p] ∧ t = t1 ++ q :: t2') := by
  rcases List.eq_nil_or_concat t2 with h | ⟨t2', r, h⟩
  · subst h
    rw [List.append_singleton_inj]
    constructor
    · rintro ⟨h1, h2⟩; exact Or.inl ⟨rfl, h1.symm, h2.symm⟩
    · rintro (⟨-, h1, h2⟩ | ⟨t2', h, -⟩)
      · exact ⟨h1.symm, h2.symm⟩
      · simp at h
  · subst h
    simp only [List.concat_eq_append]
    have e : t1 ++ q :: (t2' ++ [r]) = (t1 ++ q :: t2') ++ [r] := by simp
    rw [e, List.append_singleton_inj]
    constructor
    · rintro ⟨h1, h2⟩; subst h2; exact Or.inr ⟨t2', rfl, h1⟩
    · rintro (⟨h, -⟩ | ⟨t2'', h, h1⟩)
      · simp at h
      · rw [List.append_singleton_inj] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨h1, rfl⟩

theorem mem_lkDeps (t : Seq) (c : Cmd) (d : CmdId) :
    d ∈ lkDeps t c ↔ ∃ t1 q t2, t = t1 ++ q :: t2 ∧ q.1 = d ∧ q.2.key = c.key ∧
      (∀ q' ∈ t2, q'.2.key = c.key → q'.2.isPut = false) ∧ (q.2.isPut ∨ c.isPut) := by
  induction t using revInd with
  | h0 => simp [lkDeps]
  | hs t p ih =>
    rw [lkDeps_snoc]
    simp only [snoc_eq_append_cons]
    constructor
    · intro hd
      by_cases hk : p.2.key = c.key
      · rw [if_pos hk] at hd
        by_cases hp : p.2.isPut = true
        · rw [if_pos hp] at hd
          simp at hd; subst hd
          exact ⟨t, p, [], Or.inl ⟨rfl, rfl, rfl⟩, rfl, hk, by simp, Or.inl hp⟩
        · rw [if_neg hp] at hd
          have hp' : p.2.isPut = false := by simpa using hp
          by_cases hc : c.isPut = true
          · rw [if_pos hc, List.mem_append] at hd
            rcases hd with hd | hd
            · obtain ⟨t1, q, t2, h, h1, h2, h3, h4⟩ := (ih).mp hd
              refine ⟨t1, q, t2 ++ [p], Or.inr ⟨t2, rfl, h⟩, h1, h2, ?_, h4⟩
              intro q' hq' hk'; simp at hq'; rcases hq' with hq' | hq'
              · exact h3 q' hq' hk'
              · subst hq'; exact hp'
            · simp at hd; subst hd
              exact ⟨t, p, [], Or.inl ⟨rfl, rfl, rfl⟩, rfl, hk, by simp, Or.inr hc⟩
          · rw [if_neg hc] at hd
            obtain ⟨t1, q, t2, h, h1, h2, h3, h4⟩ := (ih).mp hd
            refine ⟨t1, q, t2 ++ [p], Or.inr ⟨t2, rfl, h⟩, h1, h2, ?_, h4⟩
            intro q' hq' hk'; simp at hq'; rcases hq' with hq' | hq'
            · exact h3 q' hq' hk'
            · subst hq'; exact hp'
      · rw [if_neg hk] at hd
        obtain ⟨t1, q, t2, h, h1, h2, h3, h4⟩ := (ih).mp hd
        refine ⟨t1, q, t2 ++ [p], Or.inr ⟨t2, rfl, h⟩, h1, h2, ?_, h4⟩
        intro q' hq' hk'; simp at hq'; rcases hq' with hq' | hq'
        · exact h3 q' hq' hk'
        · subst hq'; exact absurd hk' hk
    · rintro ⟨t1, q, t2, h | ⟨t2', rfl, h⟩, h1, h2, h3, h4⟩
      · obtain ⟨rfl, rfl, rfl⟩ := h
        rw [if_pos h2]
        by_cases hp : q.2.isPut = true
        · rw [if_pos hp]; simp [h1]
        · rw [if_neg hp]
          have hc : c.isPut = true := by
            rcases h4 with h4 | h4
            · exact absurd h4 hp
            · exact h4
          rw [if_pos hc]; simp [h1]
      · have hmem : d ∈ lkDeps t c :=
          (ih).mpr ⟨t1, q, t2', h, h1, h2, fun q' hq' hk' => h3 q' (by simp [hq']) hk', h4⟩
        by_cases hk : p.2.key = c.key
        · rw [if_pos hk]
          have hp : p.2.isPut = false := h3 p (by simp) hk
          rw [if_neg (by simp [hp])]
          split <;> simp [hmem]
        · rw [if_neg hk]; exact hmem

theorem before_split (t u : Seq) (p : CmdId × Cmd) (h : p.1 ∉ t.map Prod.fst) :
    before (t ++ p :: u) p.1 = t := by
  unfold before
  rw [List.takeWhile_append_of_pos]
  · simp
  · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
    intro hc; exact h (List.mem_map.mpr ⟨a, ha, hc⟩)

theorem cmdIn_split (t u : Seq) (p : CmdId × Cmd) (h : p.1 ∉ t.map Prod.fst) :
    cmdIn (t ++ p :: u) p.1 = some p.2 := by
  unfold cmdIn
  rw [List.find?_append]
  have : t.find? (fun q => q.1 == p.1) = none := by
    rw [List.find?_eq_none]; intro a ha; simp only [beq_iff_eq]
    intro hc; exact h (List.mem_map.mpr ⟨a, ha, hc⟩)
  simp [this]

theorem depsIn_split (t u : Seq) (p : CmdId × Cmd) (h : p.1 ∉ t.map Prod.fst) :
    depsIn (t ++ p :: u) p.1 = lkDeps t p.2 := by
  unfold depsIn; rw [cmdIn_split t u p h, before_split t u p h]

theorem last_put_split (b : Seq) (k : w64)
    (h : ∃ q ∈ b, q.2.key = k ∧ q.2.isPut = true) :
    ∃ b1 pm b2, b = b1 ++ pm :: b2 ∧ pm.2.key = k ∧ pm.2.isPut = true ∧
      ∀ q ∈ b2, q.2.key = k → q.2.isPut = false := by
  induction b using revInd with
  | h0 => simp at h
  | hs b p ih =>
    by_cases hp : p.2.key = k ∧ p.2.isPut = true
    · exact ⟨b, p, [], rfl, hp.1, hp.2, by simp⟩
    · have h' : ∃ q ∈ b, q.2.key = k ∧ q.2.isPut = true := by
        obtain ⟨q, hq, h1⟩ := h
        simp at hq; rcases hq with hq | hq
        · exact ⟨q, hq, h1⟩
        · subst hq; exact absurd h1 hp
      obtain ⟨b1, pm, b2, rfl, h1, h2, h3⟩ := ih h'
      refine ⟨b1, pm, b2 ++ [p], by simp, h1, h2, ?_⟩
      intro q hq hk; simp at hq; rcases hq with hq | hq
      · exact h3 q hq hk
      · subst hq; simpa [hk] using hp

theorem chain (s : Seq) (hnd : (s.map Prod.fst).Nodup) :
    ∀ (n : Nat) (a b c' : Seq) (py pz : CmdId × Cmd), b.length = n →
      s = a ++ py :: b ++ pz :: c' → py.2.key = pz.2.key → (py.2.isPut ∨ pz.2.isPut) →
      Relation.TransGen (fun z d => d ∈ depsIn s z) pz.1 py.1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b c' py pz hn hs hk hp
    have hnot : pz.1 ∉ (a ++ py :: b).map Prod.fst := by
      rw [hs] at hnd
      have : (a ++ py :: b ++ pz :: c') = (a ++ py :: b) ++ pz :: c' := by simp
      rw [this, List.map_append, List.nodup_append] at hnd
      intro hm; exact hnd.2.2 pz.1 hm pz.1 (by simp) rfl
    have hdeps : depsIn s pz.1 = lkDeps (a ++ py :: b) pz.2 := by
      rw [hs]
      have : (a ++ py :: b ++ pz :: c') = (a ++ py :: b) ++ pz :: c' := by simp
      rw [this]; exact depsIn_split _ _ _ hnot
    by_cases hb : ∃ q ∈ b, q.2.key = pz.2.key ∧ q.2.isPut = true
    · obtain ⟨b1, pm, b2, rfl, h1, h2, h3⟩ := last_put_split b pz.2.key hb
      have hedge : pm.1 ∈ depsIn s pz.1 := by
        rw [hdeps, mem_lkDeps]
        exact ⟨a ++ py :: b1, pm, b2, by simp, rfl, h1, h3, Or.inl h2⟩
      have hrec := ih b1.length (by rw [← hn]; simp) a b1 (b2 ++ pz :: c') py pm rfl
        (by rw [hs]; simp) (by rw [hk, h1]) (Or.inr h2)
      exact Relation.TransGen.trans (Relation.TransGen.single hedge) hrec
    · have hb' : ∀ q ∈ b, q.2.key = pz.2.key → q.2.isPut = false := by
        intro q hq hk'; cases hc : q.2.isPut with
        | false => rfl
        | true => exact absurd ⟨q, hq, hk', hc⟩ hb
      apply Relation.TransGen.single
      rw [hdeps, mem_lkDeps]
      exact ⟨a, py, b, rfl, rfl, hk, hb', hp⟩

/-- The kept dependencies of `c` in `k`. -/
def kdeps (k : Kept) (c : CmdId) : List CmdId := ((k.get c).map RecEntry.dep).getD []

/-- `recOrder`'s step. -/
def recOrderStep (k : Kept) (ids : List CmdId) (placed : List CmdId) : List CmdId :=
  let rest := ids.filter (· ∉ placed)
  let ready := rest.find? (fun c => ((k.get c).map RecEntry.dep).getD [] |>.all
    (fun d => (k.get d).isNone || d ∈ placed))
  match ready, rest.head? with
  | some c, _ => placed ++ [c]
  | none, some c => placed ++ [c]
  | none, none => placed

theorem recOrder_eq (k : Kept) (ids : List CmdId) :
    recOrder k ids = iter (recOrderStep k ids) ids.length [] := rfl

/-- The invariant of `recOrder`'s placed list. -/
def PlacedOk (k : Kept) (ids placed : List CmdId) : Prop :=
  placed.Nodup ∧ (∀ c ∈ placed, c ∈ ids) ∧
  ∀ l1 c l2, placed = l1 ++ c :: l2 → ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ l1

theorem iter_succ' {α : Type} (f : α → α) (n : Nat) (a : α) : iter f (n + 1) a = f (iter f n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => show iter f (n + 1) (f a) = f (iter f (n + 1) a); rw [ih]; rfl

theorem ready_exists (k : Kept) (ids placed : List CmdId) (φ : CmdId → Nat)
    (hφ : ∀ c ∈ ids, ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ ids ∧ φ d < φ c)
    (c : CmdId) (hc : c ∈ ids) (hcp : c ∉ placed) :
    ∃ c' ∈ ids, c' ∉ placed ∧ ∀ d ∈ kdeps k c', (k.get d).isSome → d ∈ placed := by
  induction hn : φ c using Nat.strongRecOn generalizing c with
  | ind n ih =>
    by_cases hr : ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ placed
    · exact ⟨c, hc, hcp, hr⟩
    · simp only [Classical.not_forall] at hr
      obtain ⟨d, hd, hk, hdp⟩ := hr
      obtain ⟨hdi, hlt⟩ := hφ c hc d hd hk
      exact ih (φ d) (by omega) d hdi hdp rfl

theorem recOrderStep_cases (k : Kept) (ids placed : List CmdId) (φ : CmdId → Nat)
    (hφ : ∀ c ∈ ids, ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ ids ∧ φ d < φ c) :
    (recOrderStep k ids placed = placed ∧ ∀ c ∈ ids, c ∈ placed) ∨
    ∃ c ∈ ids, c ∉ placed ∧ (∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ placed) ∧
      recOrderStep k ids placed = placed ++ [c] := by
  by_cases hall : ∀ c ∈ ids, c ∈ placed
  · left
    refine ⟨?_, hall⟩
    have : ids.filter (· ∉ placed) = [] := by
      rw [List.filter_eq_nil_iff]; intro a ha; simp [hall a ha]
    unfold recOrderStep; simp only [this]; rfl
  · right
    simp only [Classical.not_forall] at hall
    obtain ⟨c0, hc0, hc0p⟩ := hall
    obtain ⟨c1, hc1, hc1p, hr⟩ := ready_exists k ids placed φ hφ c0 hc0 hc0p
    have hfind : ∃ c, (ids.filter (· ∉ placed)).find? (fun c => ((k.get c).map RecEntry.dep).getD [] |>.all
        (fun d => (k.get d).isNone || d ∈ placed)) = some c := by
      apply Option.isSome_iff_exists.mp
      rw [List.find?_isSome]
      refine ⟨c1, by simp [hc1, hc1p], ?_⟩
      rw [List.all_eq_true]; intro d hd
      have := hr d hd
      cases h : (k.get d) with
      | none => simp
      | some _ => simp [h] at this; simp [this]
    obtain ⟨c, hc⟩ := hfind
    have hcm := List.mem_of_find?_eq_some hc
    have hcp := List.find?_some hc
    simp only [List.mem_filter, decide_eq_true_eq] at hcm
    refine ⟨c, hcm.1, hcm.2, ?_, ?_⟩
    · intro d hd hk
      rw [List.all_eq_true] at hcp
      have := hcp d hd
      simp [hk] at this
      cases h : k.get d with
      | none => simp [h] at hk
      | some _ => simp [h] at this; exact this
    · unfold recOrderStep; simp only [hc]

theorem recOrder_spec (k : Kept) (ids : List CmdId) (hnd : ids.Nodup) (φ : CmdId → Nat)
    (hφ : ∀ c ∈ ids, ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ ids ∧ φ d < φ c) :
    (∀ c, c ∈ recOrder k ids ↔ c ∈ ids) ∧ (recOrder k ids).Nodup ∧
    ∀ l1 c l2, recOrder k ids = l1 ++ c :: l2 → ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ l1 := by
  have key : ∀ n, PlacedOk k ids (iter (recOrderStep k ids) n []) ∧
      ((iter (recOrderStep k ids) n []).length = n ∨ ∀ c ∈ ids, c ∈ iter (recOrderStep k ids) n []) := by
    intro n
    induction n with
    | zero => exact ⟨⟨List.nodup_nil, by simp [iter], by intro l1 c l2 h; simp [iter] at h⟩, Or.inl rfl⟩
    | succ n ih =>
      rw [iter_succ']
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ih
      rcases recOrderStep_cases k ids (iter (recOrderStep k ids) n []) φ hφ with ⟨he, hall⟩ | ⟨c, hc, hcp, hr, he⟩
      · rw [he]; exact ⟨⟨h1, h2, h3⟩, Or.inr hall⟩
      · rw [he]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · rw [List.nodup_append]; refine ⟨h1, by simp, ?_⟩; intro a ha b hb; simp at hb; subst hb
          intro hab; subst hab; exact hcp ha
        · intro a ha; simp at ha; rcases ha with ha | ha
          · exact h2 a ha
          · subst ha; exact hc
        · intro l1 c' l2 hl d hd hk
          rcases List.eq_nil_or_concat l2 with hl2 | ⟨l2', z, hl2⟩
          · subst hl2
            rw [List.append_singleton_inj] at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact hr d hd hk
          · subst hl2
            have : l1 ++ c' :: (List.concat l2' z) = (l1 ++ c' :: l2') ++ [z] := by simp
            rw [this, List.append_singleton_inj] at hl
            obtain ⟨hl, -⟩ := hl
            exact h3 l1 c' l2' hl d hd hk
        · rcases h4 with h4 | h4
          · left; simp [h4]
          · right; intro a ha; simp [h4 a ha]
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := key ids.length
  rw [recOrder_eq]
  refine ⟨?_, h1, h3⟩
  intro c
  constructor
  · exact h2 c
  · intro hc
    rcases h4 with h4 | h4
    · -- every element is placed: a nodup sublist of ids of its length
      apply Classical.byContradiction; intro hcn
      have hsub : iter (recOrderStep k ids) ids.length [] ⊆ ids.erase c := by
        intro a ha
        rw [List.Nodup.mem_erase_iff hnd]
        exact ⟨fun h => hcn (h ▸ ha), h2 a ha⟩
      have hle := (List.subperm_of_subset h1 hsub).length_le
      rw [h4, List.length_erase_of_mem hc] at hle
      have : 0 < ids.length := List.length_pos_of_mem hc
      omega
    · exact h4 c hc

theorem recReaches_sound (k : Kept) (src dst : CmdId) (h : recReaches k src dst = true) :
    Relation.TransGen (fun y d => d ∈ kdeps k y) src dst := by
  unfold recReaches at h
  simp only [decide_eq_true_eq] at h
  have inv : ∀ n, ∀ y ∈ iter (fun (seen : List CmdId) =>
      (seen ++ (seen.flatMap (fun y => ((k.get y).map RecEntry.dep).getD []))).eraseDups) n [src],
      y = src ∨ Relation.TransGen (fun y d => d ∈ kdeps k y) src y := by
    intro n
    induction n with
    | zero => intro y hy; simp [iter] at hy; exact Or.inl hy
    | succ n ih =>
      intro y hy
      rw [iter_succ'] at hy
      rw [List.mem_eraseDups, List.mem_append, List.mem_flatMap] at hy
      rcases hy with hy | ⟨z, hz, hyz⟩
      · exact ih y hy
      · rcases ih z hz with rfl | hz'
        · exact Or.inr (Relation.TransGen.single hyz)
        · exact Or.inr (Relation.TransGen.trans hz' (Relation.TransGen.single hyz))
  rw [List.mem_flatMap] at h
  obtain ⟨y, hy, hd⟩ := h
  rcases inv _ y hy with rfl | hy'
  · exact Relation.TransGen.single hd
  · exact Relation.TransGen.trans hy' (Relation.TransGen.single hd)

theorem precedes_iff (O : List CmdId) (y x : CmdId) :
    precedes O y x ↔ y ∈ O ∧ O.idxOf y < O.idxOf x := by
  unfold precedes
  induction O with
  | nil => simp
  | cons a O ih =>
    rw [List.takeWhile_cons]
    by_cases hax : a = x
    · subst hax; simp
    · have : (a != x) = true := by simpa using hax
      rw [if_pos this, List.mem_cons, ih, List.mem_cons, List.idxOf_cons, List.idxOf_cons]
      by_cases hya : y = a
      · subst hya; simp [hax]
      · have h1 : (a == y) = false := by simpa using Ne.symm hya
        have h2 : (a == x) = false := by simpa using hax
        simp [h1, h2, hya]

theorem precedes_trans (O : List CmdId) (a b c : CmdId) (h1 : precedes O a b) (h2 : precedes O b c) :
    precedes O a c := by
  rw [precedes_iff] at *
  exact ⟨h1.1, by omega⟩

theorem precedes_irrefl (O : List CmdId) (a : CmdId) : ¬ precedes O a a := by
  rw [precedes_iff]; omega

theorem precedes_mem (O : List CmdId) (a b : CmdId) (h : precedes O a b) : a ∈ O :=
  ((precedes_iff O a b).mp h).1

/-- Two distinct members: one precedes the other. -/
theorem precedes_total (O : List CmdId) (a b : CmdId) (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) :
    precedes O a b ∨ precedes O b a := by
  rw [precedes_iff, precedes_iff]
  have : O.idxOf a ≠ O.idxOf b := by
    intro h
    apply hab
    have h1 := List.idxOf_lt_length_of_mem ha
    have e1 := List.getElem_idxOf h1
    have h2 := List.idxOf_lt_length_of_mem hb
    have e2 := List.getElem_idxOf h2
    simp only [h] at e1
    exact e1.symm.trans e2
  rcases Nat.lt_or_gt_of_ne this with h | h
  · exact Or.inl ⟨ha, h⟩
  · exact Or.inr ⟨hb, h⟩

/-- In an order where every command comes after its kept dependencies, a command comes after
everything it reaches. -/
theorem order_reach (k : Kept) (O : List CmdId) (hnd : O.Nodup)
    (hO : ∀ l1 c l2, O = l1 ++ c :: l2 → ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ l1)
    (hkept : ∀ c ∈ O, ∀ d ∈ kdeps k c, (k.get d).isSome)
    (c d : CmdId) (hc : c ∈ O) (h : Relation.TransGen (fun y d => d ∈ kdeps k y) c d) :
    precedes O d c := by
  have edge : ∀ c d, c ∈ O → d ∈ kdeps k c → precedes O d c := by
    intro c d hc hd
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
    have := hO l1 _ l2 rfl _ hd (hkept _ hc _ hd)
    unfold precedes
    rw [List.takeWhile_append_of_pos]
    · simp [this]
    · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
      intro h; subst h; exact (List.nodup_append.mp hnd).2.2 a ha a (by simp) rfl
  induction h with
  | single hd => exact edge _ _ hc hd
  | tail h1 h2 ih =>
    have hb := ih
    exact precedes_trans O _ _ _ (edge _ _ (precedes_mem O _ _ hb) h2) hb

/-! ## `recOrder` on an acyclic part (D33) -/

/-- `l` places every command after its kept dependencies. -/
def Ordered (k : Kept) (l : List CmdId) : Prop :=
  ∀ l1 c l2, l = l1 ++ c :: l2 → ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ l1

theorem Ordered.snoc {k : Kept} {l : List CmdId} {c : CmdId} (h : Ordered k l)
    (hr : ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ l) : Ordered k (l ++ [c]) := by
  intro l1 c' l2 hl d hd hk
  rcases List.eq_nil_or_concat l2 with hl2 | ⟨l2', z, hl2⟩
  · subst hl2
    rw [List.append_singleton_inj] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact hr d hd hk
  · subst hl2
    have : l1 ++ c' :: (List.concat l2' z) = (l1 ++ c' :: l2') ++ [z] := by simp
    rw [this, List.append_singleton_inj] at hl
    obtain ⟨hl, -⟩ := hl
    exact h l1 c' l2' hl d hd hk

/-- The step places a new command, or every command is placed. -/
theorem recOrderStep_any (k : Kept) (ids placed : List CmdId) :
    (recOrderStep k ids placed = placed ∧ ∀ c ∈ ids, c ∈ placed) ∨
    ∃ c ∈ ids, c ∉ placed ∧ recOrderStep k ids placed = placed ++ [c] := by
  by_cases hall : ∀ c ∈ ids, c ∈ placed
  · left
    refine ⟨?_, hall⟩
    have : ids.filter (· ∉ placed) = [] := by
      rw [List.filter_eq_nil_iff]; intro a ha; simp [hall a ha]
    unfold recOrderStep; simp only [this]; rfl
  · right
    have hne : ids.filter (· ∉ placed) ≠ [] := by
      intro h; apply hall; intro c hc
      apply Classical.byContradiction; intro hcp
      have : c ∈ ids.filter (· ∉ placed) := List.mem_filter.mpr ⟨hc, by simpa using hcp⟩
      rw [h] at this; simp at this
    unfold recOrderStep
    cases hf : (ids.filter (· ∉ placed)).find? (fun c => ((k.get c).map RecEntry.dep).getD [] |>.all
        (fun d => (k.get d).isNone || d ∈ placed)) with
    | some c =>
      have hcm := List.mem_of_find?_eq_some hf
      simp only [List.mem_filter, decide_eq_true_eq] at hcm
      exact ⟨c, hcm.1, hcm.2, by simp only [hf]⟩
    | none =>
      cases hh : (ids.filter (· ∉ placed)).head? with
      | none => exact absurd (List.head?_eq_none_iff.mp hh) hne
      | some c =>
        have hcm := List.mem_of_mem_head? hh
        simp only [List.mem_filter, decide_eq_true_eq] at hcm
        exact ⟨c, hcm.1, hcm.2, by simp only [hf, hh]⟩

/-- With a command `c1` ready, the step places a ready command. -/
theorem recOrderStep_ready (k : Kept) (ids placed : List CmdId) (c1 : CmdId) (hc1 : c1 ∈ ids)
    (hc1p : c1 ∉ placed) (hr : ∀ d ∈ kdeps k c1, (k.get d).isSome → d ∈ placed) :
    ∃ c ∈ ids, c ∉ placed ∧ (∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ placed) ∧
      recOrderStep k ids placed = placed ++ [c] := by
  have hfind : ∃ c, (ids.filter (· ∉ placed)).find? (fun c => ((k.get c).map RecEntry.dep).getD [] |>.all
      (fun d => (k.get d).isNone || d ∈ placed)) = some c := by
    apply Option.isSome_iff_exists.mp
    rw [List.find?_isSome]
    refine ⟨c1, by simp [hc1, hc1p], ?_⟩
    rw [List.all_eq_true]; intro d hd
    have := hr d hd
    cases h : (k.get d) with
    | none => simp
    | some _ => simp [h] at this; simp [this]
  obtain ⟨c, hc⟩ := hfind
  have hcm := List.mem_of_find?_eq_some hc
  have hcp := List.find?_some hc
  simp only [List.mem_filter, decide_eq_true_eq] at hcm
  refine ⟨c, hcm.1, hcm.2, ?_, ?_⟩
  · intro d hd hk
    rw [List.all_eq_true] at hcp
    have := hcp d hd
    simp [hk] at this
    cases h : k.get d with
    | none => simp [h] at hk
    | some _ => simp [h] at this; exact this
  · unfold recOrderStep; simp only [hc]

/-- `recOrder` places every command once (no potential needed). -/
theorem recOrder_mem (k : Kept) (ids : List CmdId) (hnd : ids.Nodup) :
    (∀ c, c ∈ recOrder k ids ↔ c ∈ ids) ∧ (recOrder k ids).Nodup := by
  have key : ∀ n, (iter (recOrderStep k ids) n []).Nodup ∧
      (∀ c ∈ iter (recOrderStep k ids) n [], c ∈ ids) ∧
      ((iter (recOrderStep k ids) n []).length = n ∨ ∀ c ∈ ids, c ∈ iter (recOrderStep k ids) n []) := by
    intro n
    induction n with
    | zero => exact ⟨List.nodup_nil, by simp [iter], Or.inl rfl⟩
    | succ n ih =>
      rw [iter_succ']
      obtain ⟨h1, h2, h4⟩ := ih
      rcases recOrderStep_any k ids (iter (recOrderStep k ids) n []) with ⟨he, hall⟩ | ⟨c, hc, hcp, he⟩
      · rw [he]; exact ⟨h1, h2, Or.inr hall⟩
      · rw [he]
        refine ⟨?_, ?_, ?_⟩
        · rw [List.nodup_append]; refine ⟨h1, by simp, ?_⟩; intro a ha b hb; simp at hb; subst hb
          intro hab; subst hab; exact hcp ha
        · intro a ha; simp at ha; rcases ha with ha | ha
          · exact h2 a ha
          · subst ha; exact hc
        · rcases h4 with h4 | h4
          · left; simp [h4]
          · right; intro a ha; simp [h4 a ha]
  obtain ⟨h1, h2, h4⟩ := key ids.length
  rw [recOrder_eq]
  refine ⟨?_, h1⟩
  intro c
  constructor
  · exact h2 c
  · intro hc
    rcases h4 with h4 | h4
    · apply Classical.byContradiction; intro hcn
      have hsub : iter (recOrderStep k ids) ids.length [] ⊆ ids.erase c := by
        intro a ha
        rw [List.Nodup.mem_erase_iff hnd]
        exact ⟨fun h => hcn (h ▸ ha), h2 a ha⟩
      have hle := (List.subperm_of_subset h1 hsub).length_le
      rw [h4, List.length_erase_of_mem hc] at hle
      have : 0 < ids.length := List.length_pos_of_mem hc
      omega
    · exact h4 c hc

/-- A ready command exists below an unplaced command whose dependencies (through `Ac`
commands) decrease a potential. -/
theorem ready_exists_loc (k : Kept) (ids placed : List CmdId) (Ac : CmdId → Prop) (φ : CmdId → Nat)
    (hφ : ∀ c ∈ ids, Ac c → ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ ids ∧ Ac d ∧ φ d < φ c)
    (c : CmdId) (hc : c ∈ ids) (hac : Ac c) (hcp : c ∉ placed) :
    ∃ c' ∈ ids, c' ∉ placed ∧ ∀ d ∈ kdeps k c', (k.get d).isSome → d ∈ placed := by
  induction hn : φ c using Nat.strongRecOn generalizing c with
  | ind n ih =>
    by_cases hr : ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ placed
    · exact ⟨c, hc, hcp, hr⟩
    · simp only [Classical.not_forall] at hr
      obtain ⟨d, hd, hk, hdp⟩ := hr
      obtain ⟨hdi, hda, hlt⟩ := hφ c hc hac d hd hk
      exact ih (φ d) (by omega) d hdi hda hdp rfl

/-- **`recOrder` on an acyclic part**: a command `x` whose dependencies (through `Ac`
commands) decrease a potential is placed after a prefix that is ordered after its
dependencies. Nothing is claimed of the other commands. -/
theorem recOrder_loc (k : Kept) (ids : List CmdId) (hnd : ids.Nodup) (Ac : CmdId → Prop)
    (φ : CmdId → Nat)
    (hφ : ∀ c ∈ ids, Ac c → ∀ d ∈ kdeps k c, (k.get d).isSome → d ∈ ids ∧ Ac d ∧ φ d < φ c)
    (x : CmdId) (hx : x ∈ ids) (hax : Ac x) :
    ∃ l1 l2, recOrder k ids = l1 ++ x :: l2 ∧ Ordered k (l1 ++ [x]) := by
  have key : ∀ n, (x ∉ iter (recOrderStep k ids) n [] → Ordered k (iter (recOrderStep k ids) n [])) ∧
      (x ∈ iter (recOrderStep k ids) n [] → ∃ l1 l2, iter (recOrderStep k ids) n [] = l1 ++ x :: l2 ∧
        Ordered k (l1 ++ [x])) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => by intro l1 c l2 h; simp [iter] at h, fun h => by simp [iter] at h⟩
    | succ n ih =>
      rw [iter_succ']
      obtain ⟨h1, h2⟩ := ih
      generalize hP : iter (recOrderStep k ids) n [] = P at h1 h2
      by_cases hxP : x ∈ P
      · obtain ⟨l1, l2, hP', hO⟩ := h2 hxP
        rcases recOrderStep_any k ids P with ⟨he, -⟩ | ⟨c, -, -, he⟩
        · rw [he]; exact ⟨fun h => absurd hxP h, fun _ => ⟨l1, l2, hP', hO⟩⟩
        · rw [he, hP']
          refine ⟨fun h => absurd (by simp) h, fun _ => ⟨l1, l2 ++ [c], by simp, hO⟩⟩
      · have hOP := h1 hxP
        obtain ⟨c1, hc1, hc1p, hr1⟩ := ready_exists_loc k ids P Ac φ hφ x hx hax hxP
        obtain ⟨c, -, hcp, hr, he⟩ := recOrderStep_ready k ids P c1 hc1 hc1p hr1
        rw [he]
        have hO' := hOP.snoc hr
        refine ⟨fun _ => hO', fun hx' => ?_⟩
        have hxc : x = c := by
          simp at hx'; rcases hx' with h | h
          · exact absurd h hxP
          · exact h
        subst hxc
        exact ⟨P, [], rfl, hO'⟩
  have hmem := (recOrder_mem k ids hnd).1 x
  rw [recOrder_eq] at hmem ⊢
  exact (key ids.length).2 (hmem.mpr hx)

/-- In an ordered list (complete for its kept dependencies), what a command reaches is placed
before it. -/
theorem Ordered.reach {k : Kept} {l : List CmdId} (h : Ordered k l) (hnd : l.Nodup)
    (hcomp : ∀ c ∈ l, ∀ d ∈ kdeps k c, (k.get d).isSome) {a b : CmdId} (ha : a ∈ l)
    (hr : Relation.TransGen (fun y d => d ∈ kdeps k y) a b) : precedes l b a := by
  have edge : ∀ c d, c ∈ l → d ∈ kdeps k c → precedes l d c := by
    intro c d hc hd
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem hc
    have hdl1 := h l1 c l2 hl d hd (hcomp c hc d hd)
    have hcl1 : c ∉ l1 := by
      intro hm; rw [hl, List.nodup_append] at hnd; exact hnd.2.2 c hm c (by simp) rfl
    rw [hl]; unfold precedes
    rw [List.takeWhile_append_of_pos]
    · simp [hdl1]
    · intro z hz; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; intro e; subst e; exact hcl1 hz
  induction hr with
  | single hd => exact edge _ _ ha hd
  | tail _ hd ih =>
    have h1 := ih
    exact precedes_trans _ _ _ _ (edge _ _ (precedes_mem _ _ _ h1) hd) h1

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
