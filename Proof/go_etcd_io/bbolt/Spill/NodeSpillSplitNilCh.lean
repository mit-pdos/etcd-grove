/-
`node.spill` after its children's loop (U9v, `notes/bbolt-proof-plan.md`; pure): **the spill's
global state across `n.children = nil`** (`spG_nilCh`): `n`'s children cleared and its old children
dead keep `spG`, given that those children are nodes of `n`'s bucket, childless, not roots, and
no other live node's children (the facts of the children's loop's end), and that every node is in
at most one bucket (`objsDisj`, the heap's).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesKill
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitG

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nilch
variable [GooseExts]

/-- The root a `nodeRootIn` ends at is a node with no parent. -/
theorem nodeRootIn_top {B : BRec} {x rt : Loc} (h : nodeRootIn B x rt) :
    ∃ r, B.ns !! rt = some r ∧ r.nv.parent' = null := by
  induction h with
  | top x r hr hp => exact ⟨r, hr, hp⟩
  | up _ _ _ _ _ _ ih => exact ih

/-- A childless node's descendants are itself. -/
theorem descIn_nil {B : BRec} {c d : Loc} {rc : NRec} (hc : B.ns !! c = some rc) (h0 : rc.cs = [])
    (h : descIn B c d) : d = c := by
  cases h with
  | self => rfl
  | child _ c' _ r hr hm _ =>
    rw [hc] at hr; cases hr; rw [h0] at hm; cases hm

/-- `descIn` across `n`'s children cleared, to a node none of them (they are childless). -/
theorem descIn_nilCh {B : BRec} {n : Loc} {r : NRec} (hn : B.ns !! n = some r)
    (hcs : ∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ rc.cs = [])
    {a l : Loc} (h : descIn B a l) (hl : l ∉ r.cs) :
    descIn { B with ns := B.ns.insert n r.nilCh } a l := by
  induction h with
  | self x => exact descIn.self x
  | child x c d rx hx hc hd ih =>
    by_cases e : x = n
    · subst e; rw [hn] at hx; cases hx
      obtain ⟨rc, hrc, h0⟩ := hcs c hc
      have := descIn_nil hrc h0 hd
      subst this; exact absurd hc hl
    · exact descIn.child x c d rx (by
        show (B.ns.insert n r.nilCh) !! x = some rx
        rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hx) hc (ih hl)

/-- **The spill's global state across `n.children = nil`** (see the module doc). -/
theorem spG_nilCh {X : WX} {bl n : Loc} {B : BRec} {r : NRec}
    (hb : X.t.bs !! bl = some B) (hn : B.ns !! n = some r) (hd : objsDisj X.t)
    (hcs : ∀ c ∈ r.cs, ∃ rc, B.ns !! c = some rc ∧ rc.cs = [] ∧ rc.nv.parent' ≠ null)
    (huniq : ∀ m rm, B.ns !! m = some rm → m ∈ X.live → m ≠ n → ∀ c ∈ rm.cs, c ∉ r.cs)
    {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl) :
    spG (X.nilCh bl n r) txid ml fl := by
  obtain ⟨h1, h2, ⟨dA, dB, dC, dD, dE⟩, hF, ⟨rB, rN'⟩, h6, h7, h8, h9⟩ := hG
  let B2 : BRec := { B with ns := B.ns.insert n r.nilCh }
  have hX : X.nilCh bl n r = (X.setBkt bl B2).killL r.cs := by
    unfold WX.nilCh WX.setNode; rw [hb]
  have hlive : ∀ l, l ∈ (X.nilCh bl n r).live ↔ l ∈ X.live ∧ l ∉ r.cs := by
    intro l; unfold WX.nilCh; rw [killL_live]
    unfold WX.setNode; rw [hb]; rfl
  rw [hX]
  have hbsX : ∀ c, ((X.setBkt bl B2).killL r.cs).t.bs !! c = (X.t.bs.insert bl B2) !! c :=
    fun _ => rfl
  have hlive' : ∀ l, l ∈ ((X.setBkt bl B2).killL r.cs).live ↔ l ∈ X.live ∧ l ∉ r.cs :=
    killL_live (X.setBkt bl B2) r.cs
  have hbs : ∀ c C, (X.t.bs.insert bl B2) !! c = some C →
      (c = bl ∧ C = B2) ∨ (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C hC
    by_cases e : c = bl
    · subst e; rw [GMap.lookup_insert] at hC; cases hC; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hC; exact Or.inr ⟨e, hC⟩
  have hB2 : ∀ l, B2.ns !! l = if l = n then some r.nilCh else B.ns !! l := by
    intro l
    show (B.ns.insert n r.nilCh) !! l = _
    by_cases e : l = n
    · subst e; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), if_neg e]
  have hpar : ∀ x rx, B.ns !! x = some rx → ∃ r', B2.ns !! x = some r' ∧ r'.nv.parent' = rx.nv.parent' := by
    intro x rx hx
    by_cases e : x = n
    · rw [e] at hx ⊢; rw [hn] at hx; cases hx; exact ⟨r.nilCh, by rw [hB2, if_pos rfl], rfl⟩
    · exact ⟨rx, by rw [hB2, if_neg e]; exact hx, rfl⟩
  -- a node of `bl` live after: its record and liveness before
  have hrec : ∀ l rl, B2.ns !! l = some rl → ∃ r0, B.ns !! l = some r0 ∧
      ((l ≠ n ∧ rl = r0) ∨ (l = n ∧ rl = r.nilCh)) := by
    intro l rl hl
    rw [hB2] at hl
    by_cases e : l = n
    · rw [if_pos e] at hl; cases hl; rw [e]; exact ⟨r, hn, Or.inr ⟨rfl, rfl⟩⟩
    · rw [if_neg e] at hl; exact ⟨rl, hl, Or.inl ⟨e, rfl⟩⟩
  -- a child of a node of another bucket is no child of `n`
  have hoth : ∀ c C l rl, c ≠ bl → X.t.bs !! c = some C → C.ns !! l = some rl → l ∈ X.live →
      ∀ c' ∈ rl.cs, c' ∉ r.cs := by
    intro c C l rl hc hC hl hlv c' hc' hm
    obtain ⟨-, -, -, hch⟩ := dA c C l rl hC hl hlv
    obtain ⟨rc, hrc, -⟩ := hcs c' hm
    have := hd bl B hb c' (by rw [hrc]; rfl) c C hC hc
    have h2 := (hch c' hc').2
    rw [this] at h2; cases h2
  refine ⟨h1, h2, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, h6, h7, h8, h9⟩
  · intro c C l rl hC hl hlv
    rw [hlive'] at hlv
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · obtain ⟨r0, h0, ⟨hln, e⟩ | ⟨hl', e⟩⟩ := hrec l rl hl
      · rw [e]
        obtain ⟨a, b, d, f⟩ := dA c B l r0 hb h0 hlv.1
        refine ⟨a, b, d, fun c' hc' => ⟨(hlive' c').2 ⟨(f c' hc').1, huniq l r0 h0 hlv.1 hln c' hc'⟩, ?_⟩⟩
        have := (f c' hc').2
        by_cases e : c' = n
        · rw [e, hB2, if_pos rfl]; rfl
        · rw [hB2, if_neg e]; exact this
      · rw [hl'] at hlv h0; rw [e]
        obtain ⟨a, b, d, -⟩ := dA c B n r hb hn hlv.1
        exact ⟨a, b, d, fun c' hc' => by simp [NRec.nilCh] at hc'⟩
    · obtain ⟨a, b, d, f⟩ := dA c C l rl hC hl hlv.1
      exact ⟨a, b, d, fun c' hc' =>
        ⟨(hlive' c').2 ⟨(f c' hc').1, hoth c C l rl hc hC hl hlv.1 c' hc'⟩, (f c' hc').2⟩⟩
  · intro c C hC hcl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · obtain ⟨hbm, hrt⟩ := dB c B hb hcl
      refine ⟨fun k c' hk => ?_, fun hrn => ?_⟩
      · obtain ⟨a, b⟩ := hbm k c' hk
        refine ⟨a, ?_⟩
        rw [hbsX]
        by_cases e : c' = c
        · rw [e, GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact b
      · obtain ⟨rt, h, hm⟩ := hrt hrn
        refine ⟨rt, nodeRootIn_tr hpar h, (hlive' rt).2 ⟨hm, fun hm' => ?_⟩⟩
        obtain ⟨r0, h0, hp0⟩ := nodeRootIn_top h
        obtain ⟨rc, hrc, -, hpc⟩ := hcs rt hm'
        rw [h0] at hrc; cases hrc; exact hpc hp0
    · obtain ⟨hbm, hrt⟩ := dB c C hC hcl
      refine ⟨fun k c' hk => ?_, fun hrn => ?_⟩
      · obtain ⟨a, b⟩ := hbm k c' hk
        refine ⟨a, ?_⟩
        rw [hbsX]
        by_cases e : c' = bl
        · rw [e, GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact b
      · obtain ⟨rt, h, hm⟩ := hrt hrn
        refine ⟨rt, h, (hlive' rt).2 ⟨hm, fun hm' => ?_⟩⟩
        obtain ⟨r0, h0, -⟩ := nodeRootIn_top h
        obtain ⟨rc, hrc, -⟩ := hcs rt hm'
        have := hd bl B hb rt (by rw [hrc]; rfl) c C hC hc
        rw [this] at h0; cases h0
  · intro c C hC
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · refine ⟨(dC c B hb).1, ?_⟩
      rw [hB2]
      have hnn : n ≠ null := by intro e; rw [e, (dC c B hb).2] at hn; cases hn
      rw [if_neg (Ne.symm hnn)]; exact (dC c B hb).2
    · exact dC c C hC
  · show ((X.t.bs.insert bl B2) !! X.rl).isSome
    by_cases e : X.rl = bl
    · rw [e, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact dD
  · intro l hl hlv
    exact dE l hl ((hlive' l).1 hlv).1
  · intro c C l rl hC hl hlv
    rw [hlive'] at hlv
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · obtain ⟨r0, h0, ⟨-, e⟩ | ⟨hl', e⟩⟩ := hrec l rl hl
      · rw [e]; exact hF c B l r0 hb h0 hlv.1
      · rw [hl'] at hlv; rw [e]; exact hF c B n r hb hn hlv.1
    · exact hF c C l rl hC hl hlv.1
  · intro c C hC hcl
    have hbr : ∀ {c'}, bktReach X c' →
        bktReach ((X.setBkt bl B2).killL r.cs) c' := by
      intro c' h
      induction h with
      | root => exact bktReach.root
      | child bl' c'' B' k hB' hk _ ih =>
        by_cases e : bl' = bl
        · subst e; rw [hb] at hB'; cases hB'
          exact bktReach.child bl' c'' B2 k (GMap.lookup_insert _ _ _) hk ih
        · exact bktReach.child bl' c'' B' k
            (by show (X.t.bs.insert bl B2) !! bl' = some B'
                rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hB') hk ih
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · exact hbr (rB c B hb hcl)
    · exact hbr (rB c C hC hcl)
  · intro c C l rl hC hl hlv
    rw [hlive'] at hlv
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · obtain ⟨r0, h0, -⟩ := hrec l rl hl
      obtain ⟨rt, h, hdsc⟩ := rN' c B l r0 hb h0 hlv.1
      exact ⟨rt, nodeRootIn_tr hpar h,
        descIn_nilCh hn (fun c' hc' => by obtain ⟨rc, a, b, -⟩ := hcs c' hc'; exact ⟨rc, a, b⟩)
          hdsc hlv.2⟩
    · exact rN' c C l rl hC hl hlv.1

end nilch

end Spill

end bbolt
end EtcdGrove
end Perennial
