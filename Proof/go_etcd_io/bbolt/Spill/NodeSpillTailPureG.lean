/-
`node.spill` after its children's loop (U9u, `notes/bbolt-proof-plan.md`; pure): **the spill's
global state across a node's record change** that keeps its parent and children (`spG_setNode`):
a piece's free (its page id), its write (`pcRec`), its parent's put (`pcPar`), with the changed
record's keys not empty and its sources not stale.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Spill.DerefModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section setnode
variable [GooseExts]

/-- A node's record changed but its parent and children. -/
def nodeQ (r r' : NRec) : Prop := r'.nv.parent' = r.nv.parent' ∧ r'.cs = r.cs

/-- A bucket's record but its nodes, those changed but their parents and children. -/
def bktQ (B B' : BRec) : Prop :=
  { B' with ns := B.ns } = B ∧ ∀ l, optRel nodeQ (B.ns !! l) (B'.ns !! l)

theorem optRel_isSomeQ {α β : Type} {R : α → β → Prop} {o : Option α} {o' : Option β}
    (h : optRel R o o') : o.isSome = o'.isSome := by
  cases o <;> cases o' <;> simp_all [optRel]

theorem setNode_eqQ {X : WX} {bl n : Loc} {B : BRec} (hB : X.t.bs !! bl = some B) (r' : NRec) :
    X.setNode bl n r' =
      { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := B.ns.insert n r' } } } := by
  unfold WX.setNode WX.setBkt
  rw [hB]

theorem nodeQ_refl (r : NRec) : nodeQ r r := ⟨rfl, rfl⟩

theorem bktQ_fields {B B' : BRec} (h : bktQ B B') : B'.bv = B.bv ∧ B'.bm = B.bm := by
  have e := h.1
  rw [← e]; exact ⟨rfl, rfl⟩

theorem descIn_Q {B B' : BRec} (h : bktQ B B') {a d : Loc} (hd : descIn B a d) :
    descIn B' a d := by
  induction hd with
  | self a => exact .self a
  | child a c d r hr hc _ ih =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2 a)
    exact .child a c d r' hr' (by rw [hs.2]; exact hc) ih

theorem nodeRootIn_Q {B B' : BRec} (h : bktQ B B') {a rt : Loc} (hd : nodeRootIn B a rt) :
    nodeRootIn B' a rt := by
  induction hd with
  | top a r hr hp =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2 a)
    exact .top a r' hr' (by rw [hs.1]; exact hp)
  | up a rt r hr hp _ ih =>
    obtain ⟨r', hr', hs⟩ := optRel_some_l (hr ▸ h.2 a)
    exact .up a rt r' hr' (by rw [hs.1]; exact hp) (by rw [hs.1]; exact ih)

variable {X : WX} {bl l : Loc} {B : BRec} {r r' : NRec}

theorem bs_Q (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hq : nodeQ r r')
    (bl' : Loc) :
    optRel bktQ (X.t.bs !! bl') ((X.t.bs.insert bl { B with ns := B.ns.insert l r' }) !! bl') := by
  by_cases he : bl = bl'
  · subst he
    rw [GMap.lookup_insert, hB]
    refine ⟨rfl, fun l' => ?_⟩
    by_cases hl : l = l'
    · subst hl; rw [GMap.lookup_insert, hr]; exact hq
    · rw [GMap.lookup_insert_ne _ _ hl]; exact optRel_refl nodeQ_refl _
  · rw [GMap.lookup_insert_ne _ _ he]
    exact optRel_refl (fun B => ⟨rfl, fun _ => optRel_refl nodeQ_refl _⟩) _

/-- The node lookups after the change: `l`'s the new record, the others' as before. -/
theorem ns_Q (hB : X.t.bs !! bl = some B) {bl0 : Loc} {B0 : BRec} {l0 : Loc} {r0 : NRec}
    (hB0 : (X.t.bs.insert bl { B with ns := B.ns.insert l r' }) !! bl0 = some B0)
    (hr0 : B0.ns !! l0 = some r0) :
    (bl0 = bl ∧ l0 = l ∧ r0 = r') ∨ ∃ B1, X.t.bs !! bl0 = some B1 ∧ B1.ns !! l0 = some r0 := by
  by_cases he : bl = bl0
  · subst he
    rw [GMap.lookup_insert] at hB0; cases hB0
    by_cases hl : l = l0
    · subst hl; rw [GMap.lookup_insert] at hr0; cases hr0; exact Or.inl ⟨rfl, rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ hl] at hr0; exact Or.inr ⟨B, hB, hr0⟩
  · rw [GMap.lookup_insert_ne _ _ he] at hB0; exact Or.inr ⟨B0, hB0, hr0⟩

theorem node_bsQ {X : WX} {bl l : Loc} {r : NRec} (hn : X.node bl l = some r) :
    ∃ B, X.t.bs !! bl = some B ∧ B.ns !! l = some r := by
  unfold WX.node at hn
  cases e : X.t.bs !! bl with
  | none => rw [e] at hn; cases hn
  | some B => rw [e] at hn; exact ⟨B, rfl, hn⟩

/-- **The spill's global state across a record change of `l`** (see the module doc). -/
theorem spG_setNode (hn : X.node bl l = some r) (hq : nodeQ r r')
    (hbk : r'.nv.bucket' = r.nv.bucket') (hk : ∀ w ∈ r'.ws, 0 < w.key.length)
    (hkey : r'.nv.key' = slice.nil ∨ 0 < r'.key.length) (hwl : wsLive r'.ws)
    (hks : r'.nv.key' ≠ slice.nil → r'.ksrc ≠ Src.stale)
    {txid : w64} {ml : Nat} {fl : FLPg} (h : spG X txid ml fl) :
    spG (X.setNode bl l r') txid ml fl := by
  obtain ⟨B, hB, hr⟩ := node_bsQ hn
  have hbs := bs_Q hB hr hq
  obtain ⟨a1, a2, ⟨d1, d2, d3, d4, d5⟩, a4, a5, a6, a7, a8⟩ := h
  rw [setNode_eqQ hB]
  refine ⟨a1, a2, ⟨?_, ?_, ?_, ?_, d5⟩, ?_, ⟨?_, ?_⟩, a6, a7, a8⟩
  · intro bl0 B0 l0 r0 hB0 hr0 hl
    have hcs : ∀ c ∈ r0.cs, c ∈ X.live ∧ (B0.ns !! c).isSome := by
      obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
      obtain ⟨r1, hr1, hrs⟩ := optRel_some_r (hr0 ▸ hs.2 l0)
      intro c hc
      obtain ⟨hcl, hcs⟩ := (d1 bl0 B1 l0 r1 hB1 hr1 hl).2.2.2 c (by rw [← hrs.2]; exact hc)
      exact ⟨hcl, by rw [← optRel_isSomeQ (hs.2 c)]; exact hcs⟩
    rcases ns_Q hB hB0 hr0 with ⟨e1, e2, e3⟩ | ⟨B1, hB1, hr1⟩
    · subst e1 e2 e3
      obtain ⟨b1, -⟩ := d1 bl0 B l0 r hB hr hl
      exact ⟨by rw [hbk]; exact b1, hk, hkey, hcs⟩
    · obtain ⟨b1, b2, b3, -⟩ := d1 bl0 B1 l0 r0 hB1 hr1 hl
      exact ⟨b1, b2, b3, hcs⟩
  · intro bl0 B0 hB0 hbl
    obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨b1, b2⟩ := d2 bl0 B1 hB1 hbl
    have hf := bktQ_fields hs
    refine ⟨fun k c hk => ?_, fun hrn => ?_⟩
    · obtain ⟨c1, c2⟩ := b1 k c (by rw [← hf.2]; exact hk)
      exact ⟨c1, by rw [← optRel_isSomeQ (hbs c)]; exact c2⟩
    · obtain ⟨rt, hrt, hrtl⟩ := b2 (by rw [← hf.1]; exact hrn)
      exact ⟨rt, by rw [hf.1]; exact nodeRootIn_Q hs hrt, hrtl⟩
  · intro bl0 B0 hB0
    obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨b1, b2⟩ := d3 bl0 B1 hB1
    refine ⟨b1, ?_⟩
    have := optRel_isSomeQ (hs.2 null)
    rw [b2] at this
    cases e : B0.ns !! null with
    | none => rfl
    | some _ => rw [e] at this; cases this
  · show ((X.t.bs.insert bl _) !! X.rl).isSome
    rw [← optRel_isSomeQ (hbs X.rl)]; exact d4
  · intro bl0 B0 l0 r0 hB0 hr0 hl
    rcases ns_Q hB hB0 hr0 with ⟨-, -, e3⟩ | ⟨B1, hB1, hr1⟩
    · subst e3; exact ⟨hwl, hks⟩
    · exact a4 bl0 B1 l0 r0 hB1 hr1 hl
  · intro bl0 B0 hB0 hbl
    have hbr : ∀ d, bktReach X d →
        bktReach { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := B.ns.insert l r' } } } d := by
      intro d hd
      induction hd with
      | root => exact .root
      | child bl1 c B1 k hB1 hk _ ih =>
        obtain ⟨B2, hB2, hs⟩ := optRel_some_l (hB1 ▸ hbs bl1)
        exact .child bl1 c B2 k hB2 (by rw [(bktQ_fields hs).2]; exact hk) ih
    obtain ⟨B1, hB1, -⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    exact hbr bl0 (a5.1 bl0 B1 hB1 hbl)
  · intro bl0 B0 l0 r0 hB0 hr0 hl
    obtain ⟨B1, hB1, hs⟩ := optRel_some_r (hB0 ▸ hbs bl0)
    obtain ⟨r1, hr1, -⟩ := optRel_some_r (hr0 ▸ hs.2 l0)
    obtain ⟨rt, hrt, hd⟩ := a5.2 bl0 B1 l0 r1 hB1 hr1 hl
    exact ⟨rt, by rw [(bktQ_fields hs).1]; exact nodeRootIn_Q hs hrt, descIn_Q hs hd⟩

/-- **The spill's global state across a change of the buffers** keeping which ids have one
(`WX.setBuf` of an allocated id). -/
theorem spG_bufs {X X' : WX} (hX : X' = { X with t := { X.t with bufs := X'.t.bufs } })
    (hb : ∀ id, (X'.t.bufs !! id).isSome ↔ (X.t.bufs !! id).isSome)
    {txid : w64} {ml : Nat} {fl : FLPg} (h : spG X txid ml fl) : spG X' txid ml fl := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  have hbr : ∀ d, bktReach X d → bktReach X' d := by
    intro d hd
    induction hd with
    | root => rw [hX]; exact .root
    | child bl1 c B1 k hB1 hk _ ih => exact .child bl1 c B1 k (by rw [hX]; exact hB1) hk ih
  have hbr' : ∀ d, bktReach X d →
      bktReach { X with t := { X.t with bufs := X'.t.bufs } } d := by rw [← hX]; exact hbr
  rw [hX]
  refine ⟨a1, a2, a3, a4, ⟨fun bl B hB hl => hbr' bl (a5.1 bl B hB hl), a5.2⟩, ?_, a7, ?_⟩
  · intro id; rw [a6 id]; exact (hb id).symm
  · intro id hid; exact a8 id ((hb id).1 hid)

end setnode

end Spill

end bbolt
end EtcdGrove
end Perennial
