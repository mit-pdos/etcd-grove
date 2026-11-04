/-
`node.spill` (U9h, `notes/bbolt-proof-plan.md`; pure): composing the spill's steps. A spill step
(`spStep`) and frame (`spFrame`) are reflexive and transitive, and a step for a larger frame of
owned slots is one for a smaller; `newSlot` grows with the steps and a lower mark. The children's
loop of `node.spill` (`Spill/NodeSpillLoop`) composes its children's spills with these.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpec
public import Proof.go_etcd_io.bbolt.Spill.DerefModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section comp
variable [GooseExts]

/-! ## Records modulo sources -/

theorem nodeSim_refl (r : NRec) : nodeSim r r :=
  ⟨rfl, Iff.rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nodeSim_trans {r1 r2 r3 : NRec} (h1 : nodeSim r1 r2) (h2 : nodeSim r2 r3) :
    nodeSim r1 r3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := h2
  refine ⟨?_, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1, g2.trans g1⟩
  rw [a2, a1]

theorem bktSim_refl (B : BRec) : bktSim B B := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bktSim_trans' {B1 B2 B3 : BRec} (h1 : bktSim B1 B2) (h2 : bktSim B2 B3) :
    bktSim B1 B3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem optRel_nodeSim_refl (o : Option NRec) : optRel nodeSim o o :=
  optRel_refl (R := nodeSim) nodeSim_refl o

theorem optRel_nodeSim_trans {o1 o2 o3 : Option NRec} (h1 : optRel nodeSim o1 o2)
    (h2 : optRel nodeSim o2 o3) : optRel nodeSim o1 o3 :=
  optRel_trans (R := nodeSim) (fun _ _ _ h1 h2 => nodeSim_trans h1 h2) o1 o2 o3 h1 h2

theorem optRel_nodeSim_isSome {o1 o2 : Option NRec} (h : optRel nodeSim o1 o2) :
    o1.isSome = o2.isSome := by
  cases o1 <;> cases o2 <;> simp_all [optRel]

/-! ## The frame -/

/-- A meta is itself with its own mark (structure eta). -/
theorem meta_with_pgid_self (m : Meta) : m = { m with pgid' := m.pgid' } := rfl

/-- A meta equal to `m` is `m` with its own mark. -/
theorem meta_with_pgid_of_eq {m m' : Meta} (h : m' = m) : m' = { m with pgid' := m'.pgid' } := by
  subst h; exact meta_with_pgid_self _

theorem spFrame_refl (X : WX) (bl : Loc) (T : List Loc) : spFrame X X bl T :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, meta_with_pgid_self _, Nat.le_refl _, fun _ _ h => h, fun _ _ h => h,
    fun _ _ B hB => ⟨B, hB, bktSim_refl B, fun _ => optRel_nodeSim_refl _⟩,
    fun _ _ h => h,
    fun B hB => ⟨B, hB, bktSim_refl B, fun _ _ => optRel_nodeSim_refl _⟩,
    fun _ _ _ _ _ _ => Iff.rfl, fun _ h => h,
    fun _ B B' _ r r' hB hB' hr hr' _ _ hv => by
      rw [hB] at hB'; cases hB'; rw [hr] at hr'; cases hr'; exact hv⟩

/-- A frame for fewer touched nodes is one for more. -/
theorem spFrame_mono {X X' : WX} {bl : Loc} {T T' : List Loc} (h : spFrame X X' bl T)
    (hT : ∀ l ∈ T, l ∈ T') : spFrame X X' bl T' := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q, z⟩ := h
  refine ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, fun B hB => ?_,
    fun y bl' B hB hs hy => p y bl' B hB hs (fun he hm => hy he (hT y hm)), q,
    fun bl' B B' y r r' hB hB' hr hr' hy => z bl' B B' y r r' hB hB' hr hr'
      (fun he hm => hy he (hT y hm))⟩
  obtain ⟨B', hB', hs, hn⟩ := o B hB
  exact ⟨B', hB', hs, fun y hy => hn y (fun hm => hy (hT y hm))⟩

/-- **Frames compose**, their touched nodes joined. -/
theorem spFrame_trans {X1 X2 X3 : WX} {bl : Loc} {T1 T2 : List Loc} (h1 : spFrame X1 X2 bl T1)
    (h2 : spFrame X2 X3 bl T2) : spFrame X1 X3 bl (T1 ++ T2) := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1, k1, l1, m1, n1, o1, p1, q1, z1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2, k2, l2, m2, n2, o2, p2, q2, z2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1,
    g2.trans g1, by rw [i2, i1], Nat.le_trans j1 j2, fun id bs h => k2 id bs (k1 id bs h),
    fun id p h => l2 id p (l1 id p h), ?_, fun bl' hne h => n2 bl' hne (n1 bl' hne h), ?_, ?_,
    fun l h => q2 l (q1 l h), ?_⟩
  · intro bl' hne B hB
    obtain ⟨B2, hB2, hs2, hn2⟩ := m1 bl' hne B hB
    obtain ⟨B3, hB3, hs3, hn3⟩ := m2 bl' hne B2 hB2
    exact ⟨B3, hB3, bktSim_trans' hs2 hs3, fun l => optRel_nodeSim_trans (hn2 l) (hn3 l)⟩
  · intro B hB
    obtain ⟨B2, hB2, hs2, hn2⟩ := o1 B hB
    obtain ⟨B3, hB3, hs3, hn3⟩ := o2 B2 hB2
    refine ⟨B3, hB3, bktSim_trans' hs2 hs3, fun l hl => ?_⟩
    have hl1 : l ∉ T1 := fun hm => hl (List.mem_append_left _ hm)
    have hl2 : l ∉ T2 := fun hm => hl (List.mem_append_right _ hm)
    exact optRel_nodeSim_trans (hn2 l hl1) (hn3 l hl2)
  · intro l bl' B hB hsome hT
    have hl1 : bl' = bl → l ∉ T1 := fun he hm => hT he (List.mem_append_left _ hm)
    have hl2 : bl' = bl → l ∉ T2 := fun he hm => hT he (List.mem_append_right _ hm)
    obtain ⟨B2, hB2, hs2⟩ : ∃ B2, X2.t.bs !! bl' = some B2 ∧ (B2.ns !! l).isSome := by
      by_cases hb : bl' = bl
      · subst hb
        obtain ⟨B2, hB2, -, hn2⟩ := o1 B hB
        exact ⟨B2, hB2, by rw [← optRel_nodeSim_isSome (hn2 l (hl1 rfl))]; exact hsome⟩
      · obtain ⟨B2, hB2, -, hn2⟩ := m1 bl' hb B hB
        exact ⟨B2, hB2, by rw [← optRel_nodeSim_isSome (hn2 l)]; exact hsome⟩
    exact (p2 l bl' B2 hB2 hs2 hl2).trans (p1 l bl' B hB hsome hl1)
  · intro bl' B B3 l r r3 hB hB3 hr hr3 hT hlv hv
    have hl1 : bl' = bl → l ∉ T1 := fun he hm => hT he (List.mem_append_left _ hm)
    have hl2 : bl' = bl → l ∉ T2 := fun he hm => hT he (List.mem_append_right _ hm)
    obtain ⟨B2, hB2, hs⟩ : ∃ B2, X2.t.bs !! bl' = some B2 ∧ optRel nodeSim (B.ns !! l) (B2.ns !! l) := by
      by_cases hb : bl' = bl
      · subst hb
        obtain ⟨B2, hB2, -, hn2⟩ := o1 B hB
        exact ⟨B2, hB2, hn2 l (hl1 rfl)⟩
      · obtain ⟨B2, hB2, -, hn2⟩ := m1 bl' hb B hB
        exact ⟨B2, hB2, hn2 l⟩
    rw [hr] at hs
    cases e2 : B2.ns !! l with
    | none => rw [e2] at hs; exact absurd hs (by simp [optRel])
    | some r2 =>
      exact z2 bl' B2 B3 l r2 r3 hB2 hB3 e2 hr3 hl2
        ((p1 l bl' B hB (by rw [hr]; rfl) hl1).2 hlv) (z1 bl' B B2 l r r2 hB hB2 hr e2 hl1 hlv hv)

/-! ## The step -/

theorem applySteps_append (fl : FLPg) (txid : w64) (s1 s2 : List FLStep) :
    fl.applySteps txid (s1 ++ s2) = (fl.applySteps txid s1).applySteps txid s2 := by
  unfold FLPg.applySteps; rw [List.foldl_append]

theorem spStep_refl {X : WX} {w : WDb} (O : List Nat) (hG : spG X w.wtxid (mapLen w.ms) w.fl)
    (hm : X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms) : spStep X X w w O [] :=
  ⟨rfl, rfl, rfl, hG, hm, fun _ h => h, fun _ h => absurd rfl h, fun _ _ h => h, id⟩

/-- **A spill step keeps the buffers dirty pages of fresh slots** (`bufsOK`; `Bucket.spill`'s
`RInv.bufs`, U9x's `bkDone_bufsOK`). -/
theorem spStep_bufsOK {X X' : WX} {w w' : WDb} {O : List Nat} {st : List FLStep}
    (h : spStep X X' w w' O st) (hb : bufsOK X w.C w.fl) : bufsOK X' w.C w'.fl :=
  h.2.2.2.2.2.2.2.2 hb

/-- The freelist's steps only take ids out of the free list. -/
theorem applySteps_free_sub (st : List FLStep) : ∀ (fl : FLPg) (txid : w64) (y : w64),
    y ∈ (fl.applySteps txid st).free → y ∈ fl.free := by
  induction st with
  | nil => intro fl txid y h; exact h
  | cons s st ih =>
    intro fl txid y h
    have h' := ih _ txid y (by unfold FLPg.applySteps at h ⊢; rw [List.foldl_cons] at h; exact h)
    cases s with
    | free id n => exact h'
    | alloc id n => exact (List.mem_filter.1 h').1

/-- A step for a larger frame of owned slots is one for a smaller. -/
theorem spStep_mono {X X' : WX} {w w' : WDb} {O O' : List Nat} {st : List FLStep}
    (h : spStep X X' w w' O st) (hO : ∀ x ∈ O', x ∈ O) : spStep X X' w w' O' st := by
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, fun x hx => ⟨fun hm => (g x hx).1 (hO x hm), (g x hx).2⟩,
    fun F hF hfr => i F (fun id hid => hO id (hF id hid)) hfr, j⟩

theorem wtxid_of_C {w w' : WDb} (h : w'.C = w.C) : w'.wtxid = w.wtxid := by
  unfold WDb.wtxid; rw [h]

/-- **Steps compose.** -/
theorem spStep_trans {X1 X2 X3 : WX} {w1 w2 w3 : WDb} {O : List Nat} {s1 s2 : List FLStep}
    (h1 : spStep X1 X2 w1 w2 O s1) (h2 : spStep X2 X3 w2 w3 O s2) :
    spStep X1 X3 w1 w3 O (s1 ++ s2) := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2⟩ := h2
  have ht : w2.wtxid = w1.wtxid := wtxid_of_C a1
  rw [ht] at b2 d2 i2
  refine ⟨a2.trans a1, by rw [b2, b1, applySteps_append], c2.trans c1, d2, e2,
    fun s hs => f2 s (f1 s hs), fun x hx => ?_, fun F hF hfr => i2 F hF (i1 F hF hfr),
    fun hb => by have := j2 (by rw [a1]; exact j1 hb); rwa [a1] at this⟩
  by_cases hx1 : spP X2 !! x = spP X1 !! x
  · obtain ⟨hO, hp⟩ := g2 x (by rw [hx1]; exact hx)
    exact ⟨hO, fun hm => hp (f1 x hm)⟩
  · exact g1 x hx1

/-- `newSlot` grows with the steps (a prefix) and a lower mark. -/
theorem newSlot_mono {st st' : List FLStep} {hwm hwm' s : Nat} (h : newSlot st hwm s)
    (hst : ∀ x ∈ st, x ∈ st') (hle : hwm' ≤ hwm) : newSlot st' hwm' s := by
  rcases h with ⟨id, n, hm, h1, h2⟩ | h
  · exact Or.inl ⟨id, n, hst _ hm, h1, h2⟩
  · exact Or.inr (Nat.le_trans hle h)

/-- The frame keeps the meta's txid. -/
theorem spFrame_txid {X X' : WX} {bl : Loc} {T : List Loc} (h : spFrame X X' bl T) :
    X'.t.mv.txid' = X.t.mv.txid' := by
  rw [h.2.2.2.2.2.2.2.1]

end comp

end Spill

end bbolt
end EtcdGrove
end Perennial
