/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 5: **the heights of the
logical tree's subtrees** (pure, over `Rebalance/RTree`'s finite trees). In a tree whose leaves
are at one depth `D` and whose branches all have children (`neT`), a subtree at depth `k` has
height `D - k` (`ht_of_dps`), so the children of a branch all have its height less one
(`child_ht`). A tree the logical tree reads over well-formed pages has its root page's height
(`pageT`). The subtrees of a tree (`subT`) and the uniqueness of the tree at a position
(`ltIs_unique`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
public import Proof.go_etcd_io.bbolt.Spill.BktEls

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section ht
variable [GooseExts]

/-- `s` is a subtree of `t` at depth `k`. -/
inductive subT (t : RTree) : Nat → RTree → Prop
  | refl : subT t 0 t
  | child (k : Nat) (p : w64) (ws : List WEntry) (cs : List RTree) (c : RTree) :
      subT t k (.mk p false ws cs) → c ∈ cs → subT t (k + 1) c

theorem subT_trans {t s x : RTree} {k k' : Nat} (h1 : subT t k s) (h2 : subT s k' x) :
    subT t (k + k') x := by
  induction h2 with
  | refl => exact h1
  | child k' p ws cs c _ hc ih => exact subT.child _ p ws cs c ih hc

/-- A subtree of a branch is itself or in a child's. -/
theorem subT_cases {p : w64} {b : Bool} {ws : List WEntry} {cs : List RTree} {k : Nat}
    {x : RTree} (h : subT (.mk p b ws cs) k x) :
    (k = 0 ∧ x = .mk p b ws cs) ∨ ∃ c ∈ cs, ∃ k', k = k' + 1 ∧ subT c k' x := by
  induction h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | child k q ws' cs' c _ hc ih =>
    rcases ih with ⟨rfl, e⟩ | ⟨c', hc', k', rfl, hs⟩
    · cases e; exact Or.inr ⟨c, hc, 0, rfl, subT.refl⟩
    · exact Or.inr ⟨c', hc', k' + 1, rfl, subT.child k' q ws' cs' c hs hc⟩

theorem htL_ge {c : RTree} : ∀ {cs : List RTree}, c ∈ cs → c.ht + 1 ≤ RTree.htL cs
  | [], h => by simp at h
  | c' :: cs, h => by
    simp only [RTree.htL]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := htL_ge h; omega

theorem htL_const {m : Nat} : ∀ {cs : List RTree}, cs ≠ [] → (∀ c ∈ cs, c.ht + 1 = m) →
    RTree.htL cs = m
  | [], h, _ => absurd rfl h
  | [c], _, h => by simp only [RTree.htL]; have := h c (by simp); omega
  | c :: c' :: cs, _, h => by
    have e := htL_const (cs := c' :: cs) (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [RTree.htL] at e ⊢
    have := h c List.mem_cons_self
    omega

theorem mem_dpsL_of {d x : Nat} {c : RTree} : ∀ {cs : List RTree}, c ∈ cs → x ∈ c.dps d →
    x ∈ RTree.dpsL d cs
  | [], h, _ => by simp at h
  | c' :: cs, h, hx => by
    simp only [RTree.dpsL, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl hx
    · exact Or.inr (mem_dpsL_of h hx)

/-- Every branch of `s` has children, every leaf none. -/
def neT (s : RTree) : Prop :=
  ∀ k p b ws cs, subT s k (.mk p b ws cs) → (b = true → cs = []) ∧ (b = false → cs ≠ [])

theorem neT_child {p : w64} {ws : List WEntry} {cs : List RTree} {c : RTree}
    (h : neT (.mk p false ws cs)) (hc : c ∈ cs) : neT c := fun k q b ws' cs' hs =>
  h (1 + k) q b ws' cs' (subT_trans (subT.child 0 p ws cs c subT.refl hc) hs)

/-- **A subtree's height is the leaves' depth less its own** (see the module doc). -/
theorem ht_of_dps (D : Nat) : ∀ n (s : RTree) (k : Nat), s.ht < n → neT s →
    (∀ x ∈ s.dps k, x = D) → s.ht + k = D
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, .mk p true ws cs, k, _, hne, hd => by
    have hcs := (hne 0 p true ws cs subT.refl).1 rfl
    subst hcs
    have := hd k (by simp [RTree.dps])
    simp only [RTree.ht, RTree.htL]; omega
  | n + 1, .mk p false ws cs, k, hn, hne, hd => by
    have hcs := (hne 0 p false ws cs subT.refl).2 rfl
    have hc : ∀ c ∈ cs, c.ht + 1 = D - k ∧ k < D := by
      intro c hcm
      have hlt : c.ht < n := by
        have := htL_ge hcm; simp only [RTree.ht] at hn; omega
      have := ht_of_dps D n c (k + 1) hlt (neT_child hne hcm) (fun x hx => hd x (by
        simp only [RTree.dps]; exact mem_dpsL_of hcm hx))
      omega
    obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil cs hcs
    have := (hc c0 hc0).2
    simp only [RTree.ht]
    rw [htL_const hcs (fun c hcm => (hc c hcm).1)]
    omega

theorem subT_dps {t s : RTree} {k D : Nat} (hd : ∀ x ∈ t.dps 0, x = D) (h : subT t k s) :
    ∀ x ∈ s.dps k, x = D := by
  induction h with
  | refl => exact hd
  | child k p ws cs c _ hc ih =>
    intro x hx
    exact ih x (by simp only [RTree.dps]; exact mem_dpsL_of hc hx)

/-- **A branch's children have its height less one**, in a tree of uniform leaf depth. -/
theorem child_ht {t : RTree} {D k : Nat} {p : w64} {ws : List WEntry} {cs : List RTree}
    {c : RTree} (hd : ∀ x ∈ t.dps 0, x = D) (hne : neT t)
    (hs : subT t k (.mk p false ws cs)) (hc : c ∈ cs) :
    c.ht + 1 = (RTree.mk p false ws cs).ht := by
  have h1 := ht_of_dps D _ _ k (Nat.lt_succ_self _)
    (fun k' q b ws' cs' h => hne (k + k') q b ws' cs' (subT_trans hs h)) (subT_dps hd hs)
  have hs' := subT.child k p ws cs c hs hc
  have h2 := ht_of_dps D _ _ (k + 1) (Nat.lt_succ_self _)
    (fun k' q b ws' cs' h => hne (k + 1 + k') q b ws' cs' (subT_trans hs' h)) (subT_dps hd hs')
  omega

/-! ## Children of a tree -/

theorem ltIsL_get {L : LTree} {bl : Loc} : ∀ {ws : List WEntry} {cs : List RTree},
    ltIsL L bl ws cs → cs.length = ws.length ∧
      ∀ (i : Nat) (c : RTree), cs[i]? = some c → ∃ w : WEntry, ws[i]? = some w ∧ c.pid = w.pgid ∧
        ltIs L bl c
  | [], [], _ => ⟨rfl, fun i c h => by simp at h⟩
  | w :: ws, c :: cs, h => by
    simp only [ltIsL] at h
    obtain ⟨h1, h2⟩ := ltIsL_get h.2.2
    refine ⟨by simp [h1], fun i c' hc => ?_⟩
    cases i with
    | zero => simp at hc; subst hc; exact ⟨w, rfl, h.1, h.2.1⟩
    | succ i => simpa using h2 i c' (by simpa using hc)
  | [], _ :: _, h => by simp only [ltIsL] at h
  | _ :: _, [], h => by simp only [ltIsL] at h

theorem ltIs_mk {L : LTree} {bl : Loc} {p : w64} {b : Bool} {ws : List WEntry}
    {cs : List RTree} (h : ltIs L bl (.mk p b ws cs)) :
    L bl p = some (b, ws) ∧ (b = true → cs = []) ∧ (b = false → ltIsL L bl ws cs) := by
  cases b with
  | true => simp only [ltIs] at h; exact ⟨h.1, fun _ => h.2, (fun e => by cases e)⟩
  | false => simp only [ltIs] at h; exact ⟨h.1, (fun e => by cases e), fun _ => h.2⟩

theorem subT_ltIs {L : LTree} {bl : Loc} {t s : RTree} {k : Nat} (ht : ltIs L bl t)
    (h : subT t k s) : ltIs L bl s := by
  induction h with
  | refl => exact ht
  | child k p ws cs c _ hc ih =>
    obtain ⟨i, hi⟩ := List.getElem_of_mem hc |>.imp fun i ⟨h, e⟩ => (by
      rw [← e]; exact List.getElem?_eq_getElem h : cs[i]? = some c)
    obtain ⟨-, -, -, hc'⟩ := ((ltIsL_get ((ltIs_mk ih).2.2 rfl)).2 i c hi)
    exact hc'

/-- **The tree at a position is unique.** -/
theorem ltIs_unique {L : LTree} {bl : Loc} : ∀ n (s s' : RTree), s.ht < n → ltIs L bl s →
    ltIs L bl s' → s.pid = s'.pid → s = s'
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, .mk p b ws cs, .mk p' b' ws' cs', hn, h, h', hp => by
    simp only [RTree.pid] at hp
    subst hp
    have e1 := (ltIs_mk h).1
    rw [(ltIs_mk h').1] at e1
    simp only [Option.some.injEq, Prod.mk.injEq] at e1
    obtain ⟨e1, e2⟩ := e1
    subst e2; subst e1
    cases b' with
    | true => rw [(ltIs_mk h).2.1 rfl, (ltIs_mk h').2.1 rfl]
    | false =>
      have g := ltIsL_get ((ltIs_mk h).2.2 rfl)
      have g' := ltIsL_get ((ltIs_mk h').2.2 rfl)
      congr 1
      apply List.ext_getElem?
      intro i
      cases hc : cs[i]? with
      | none =>
        have : i ≥ cs.length := List.getElem?_eq_none_iff.1 hc
        rw [eq_comm, List.getElem?_eq_none_iff]; omega
      | some c =>
        obtain ⟨w, hw, hcp, hcl⟩ := g.2 i c hc
        have hi : i < cs'.length := by
          have := (List.getElem?_eq_some_iff.1 hw).1; omega
        rw [List.getElem?_eq_getElem hi] at ⊢
        obtain ⟨w', hw', hcp', hcl'⟩ := g'.2 i cs'[i] (List.getElem?_eq_getElem hi)
        rw [hw] at hw'; cases hw'
        have hlt : c.ht < n := by
          have := htL_ge (List.mem_of_getElem? hc); simp only [RTree.ht] at hn; omega
        rw [ltIs_unique n c cs'[i] hlt hcl hcl' (by rw [hcp, hcp'])]

/-! ## Page subtrees -/

/-- **A tree the logical tree reads over well-formed pages** has its root page's height, and
children at every branch. -/
theorem pageT (L : LTree) (bl : Loc) (P : Pages) (hwm : Nat) (pht : Nat → Nat)
    (hht : pageHts P pht) : ∀ n (s : RTree), s.ht < n → ltIs L bl s → treeWF P hwm s.pid.toNat →
      (∀ q : w64, treeHas P s.pid.toNat q.toNat → L bl q = (P !! q.toNat).map pgRead) →
      s.ht = pht s.pid.toNat ∧ neT s
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, .mk p b ws cs, hn, h, hw, hL => by
    simp only [RTree.pid] at hw hL ⊢
    obtain ⟨hLp, hlf, hbr⟩ := ltIs_mk h
    cases hw with
    | page _ pg _ _ hpg _ _ hpt =>
    rw [hL p (treeHas.root _ pg hpg), hpg] at hLp
    simp only [Option.map_some, Option.some.injEq, pgRead, Prod.mk.injEq] at hLp
    obtain ⟨hb, rfl⟩ := hLp
    cases hpt with
    | leaf _ _ hfl =>
      have hbt : b = true := by rw [← hb]; simp [hfl]
      subst hbt
      have hcs := hlf rfl
      subst hcs
      refine ⟨by simp only [RTree.ht, RTree.htL]; exact ((hht p.toNat pg hpg).1 hfl).symm, ?_⟩
      intro k q b' ws' cs' hs
      rcases subT_cases hs with ⟨-, e⟩ | ⟨c, hc, -⟩
      · cases e; exact ⟨fun _ => rfl, (fun e => by cases e)⟩
      · simp at hc
    | branch _ _ hfl hbw hch =>
      have hbf : b = false := by
        rw [← hb]; simp only [decide_eq_false_iff_not]; rw [hfl]; decide
      subst hbf
      have g := ltIsL_get (hbr rfl)
      have hlen : cs.length = pageCount pg := by rw [g.1]; unfold pageWs; simp
      have hcs : cs ≠ [] := by
        intro e; rw [e] at hlen; have := hbw.1; simp at hlen; omega
      have hc : ∀ c ∈ cs, c.ht + 1 = pht p.toNat ∧ neT c := by
        intro c hcm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcm
        obtain ⟨w, hw, hcp, hcl⟩ := g.2 i cs[i] (List.getElem?_eq_getElem hi)
        have hi' : i < pageCount pg := by omega
        have hwi : w = pageW pg i := by
          unfold pageWs at hw; rw [List.getElem?_map, List.getElem?_range hi'] at hw
          simp at hw; exact hw.symm
        have hpid : cs[i].pid.toNat = branchPgid pg i := by
          rw [hcp, hwi]
          have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
            have hnl : pageFlags pg ≠ leafPageFlag := by rw [hfl]; decide
            simp [pageW, hnl]
          rw [this, branchPgid_toNat']
        have hlt : cs[i].ht < n := by
          have := htL_ge hcm; simp only [RTree.ht] at hn; omega
        have ih := pageT L bl P hwm pht hht n cs[i] hlt hcl (by rw [hpid]; exact hch i hi')
          (fun q hq => hL q (by
            rw [hpid] at hq; exact treeHas.sub _ pg _ hpg (pageHas.child pg i _ hfl hi' hq)))
        rw [hpid] at ih
        exact ⟨by rw [ih.1]; exact (hht p.toNat pg hpg).2 hfl i hi', ih.2⟩
      refine ⟨by simp only [RTree.ht]; exact htL_const hcs (fun c hcm => (hc c hcm).1), ?_⟩
      intro k q b' ws' cs' hs
      rcases subT_cases hs with ⟨-, e⟩ | ⟨c, hcm, k', -, hs'⟩
      · cases e; exact ⟨(fun e => by cases e), fun _ => hcs⟩
      · exact (hc c hcm).2 k' q b' ws' cs' hs'

end ht

end Spill

end bbolt
end EtcdGrove
end Perennial
