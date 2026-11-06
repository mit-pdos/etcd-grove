/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`; pure): **the spill's global state across
`splitX`** (`spG_splitX`): records of bucket `bl` replaced and fresh nodes added keep `spG`, given
the put records' own facts (`derefPre`'s and `liveFresh`'s), the bucket's root node's root and
every live node of the bucket reached in the new records. The transfers of `nodeRootIn`, `descIn`
and `bktReach` it rests on.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitPut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section g
variable [GooseExts]

/-- A location no node object has is no dead node. -/
theorem dead_none_of_objs {T : WTx} {l : Loc} (h : T.objs !! l = none) : T.dead !! l = none := by
  have := objs_other T l (Write.objs_none T l h)
  rw [h] at this
  unfold WTx.deadObjs at this
  rw [GMap.lookup_fmap] at this
  cases hd : T.dead !! l with
  | none => rfl
  | some p => rw [hd] at this; cases this

theorem bktReach_splitX {X : WX} {bl : Loc} {B : BRec} {ps1 ps2 : List (Loc × NRec)}
    (hb : X.t.bs !! bl = some B) {c : Loc} (h : bktReach X c) :
    bktReach (splitX X bl B ps1 ps2) c := by
  induction h with
  | root => exact bktReach.root
  | child bl' c B' k hB hk _ ih =>
    by_cases e : bl' = bl
    · subst e; rw [hb] at hB; cases hB
      exact bktReach.child bl' c _ k (splitX_bs _ _ _ _ _) hk ih
    · exact bktReach.child bl' c B' k (by rw [splitX_bs_ne _ _ _ _ _ _ e]; exact hB) hk ih

/-- `nodeRootIn` across records keeping every node's parent. -/
theorem nodeRootIn_tr {B B2 : BRec}
    (hp : ∀ x r, B.ns !! x = some r → ∃ r', B2.ns !! x = some r' ∧ r'.nv.parent' = r.nv.parent')
    {x rt : Loc} (h : nodeRootIn B x rt) : nodeRootIn B2 x rt := by
  induction h with
  | top x r hr hpn =>
    obtain ⟨r', hr', e⟩ := hp x r hr
    exact nodeRootIn.top x r' hr' (by rw [e]; exact hpn)
  | up x rt r hr hpn _ ih =>
    obtain ⟨r', hr', e⟩ := hp x r hr
    exact nodeRootIn.up x rt r' hr' (by rw [e]; exact hpn) (by rw [e]; exact ih)

/-- `nodeRootIn` across records keeping every node's parent but the root `n`'s, now `pl` (a
root). -/
theorem nodeRootIn_tr_top {B B2 : BRec} {n pl : Loc} {rN rn' rq : NRec}
    (hp : ∀ x r, B.ns !! x = some r → x ≠ n →
      ∃ r', B2.ns !! x = some r' ∧ r'.nv.parent' = r.nv.parent')
    (hn : B.ns !! n = some rN) (h0 : rN.nv.parent' = null) (hn2 : B2.ns !! n = some rn')
    (hn2p : rn'.nv.parent' = pl) (hpl : pl ≠ null) (hq : B2.ns !! pl = some rq)
    (hq0 : rq.nv.parent' = null)
    {x rt : Loc} (h : nodeRootIn B x rt) : nodeRootIn B2 x (if rt = n then pl else rt) := by
  induction h with
  | top x r hr hpn =>
    by_cases e : x = n
    · subst e
      rw [if_pos rfl]
      exact nodeRootIn.up x pl rn' hn2 (by rw [hn2p]; exact hpl)
        (by rw [hn2p]; exact nodeRootIn.top pl rq hq hq0)
    · rw [if_neg e]
      obtain ⟨r', hr', e'⟩ := hp x r hr e
      exact nodeRootIn.top x r' hr' (by rw [e']; exact hpn)
  | up x rt r hr hpn _ ih =>
    have e : x ≠ n := by
      rintro rfl; rw [hn] at hr; cases hr; exact hpn h0
    obtain ⟨r', hr', e'⟩ := hp x r hr e
    exact nodeRootIn.up x _ r' hr' (by rw [e']; exact hpn) (by rw [e']; exact ih)

/-- `descIn` across records whose children grow. -/
theorem descIn_tr {B B2 : BRec}
    (hs : ∀ x r, B.ns !! x = some r → ∃ r', B2.ns !! x = some r' ∧ ∀ c ∈ r.cs, c ∈ r'.cs)
    {a b : Loc} (h : descIn B a b) : descIn B2 a b := by
  induction h with
  | self n => exact descIn.self n
  | child n c d r hr hc _ ih =>
    obtain ⟨r', hr', hcs⟩ := hs n r hr
    exact descIn.child n c d r' hr' (hcs c hc) ih

theorem descIn_snoc {B : BRec} {a b c : Loc} {r : NRec} (h : descIn B a b)
    (hr : B.ns !! b = some r) (hc : c ∈ r.cs) : descIn B a c := by
  induction h with
  | self n => exact descIn.child n c c r hr hc (descIn.self c)
  | child n c' d r' hr' hc' _ ih => exact descIn.child n c' c r' hr' hc' (ih hr)

/-- **The spill's global state across `splitX`** (see the module doc). -/
theorem spG_splitX {X : WX} {bl : Loc} {B : BRec} {psOld psNew : List (Loc × NRec)}
    (hb : X.t.bs !! bl = some B) (hnd : ((psOld ++ psNew).map (·.1)).Nodup)
    (hold : ∀ p ∈ psOld, (B.ns !! p.1).isSome)
    (hnew : ∀ p ∈ psNew, X.t.objs !! p.1 = none ∧ p.1 ≠ null)
    (hrec : ∀ p ∈ psOld ++ psNew, p.2.nv.bucket' = bl ∧ (∀ w ∈ p.2.ws, 0 < w.key.length) ∧
      (p.2.nv.key' = slice.nil ∨ 0 < p.2.key.length) ∧
      (∀ c ∈ p.2.cs, (c ∈ X.live ∨ c ∈ psNew.map (·.1)) ∧
        (nsIns B.ns (psOld ++ psNew) !! c).isSome) ∧
      wsLive p.2.ws ∧ (p.2.nv.key' ≠ slice.nil → p.2.ksrc ≠ Src.stale))
    (hroot : bl ∈ X.liveB → B.bv.rootNode' ≠ null → ∃ rt,
      nodeRootIn { B with ns := nsIns B.ns (psOld ++ psNew) } B.bv.rootNode' rt ∧
        (rt ∈ X.live ∨ rt ∈ psNew.map (·.1)))
    (hreach : ∀ l r, nsIns B.ns (psOld ++ psNew) !! l = some r →
      (l ∈ X.live ∨ l ∈ psNew.map (·.1)) → ∃ rt,
        nodeRootIn { B with ns := nsIns B.ns (psOld ++ psNew) } B.bv.rootNode' rt ∧
        descIn { B with ns := nsIns B.ns (psOld ++ psNew) } rt l)
    {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl) :
    spG (splitX X bl B psOld psNew) txid ml fl := by
  obtain ⟨h1, h2, ⟨dA, dB, dC, dD, dE⟩, hF, ⟨rB, rN'⟩, h6, h7, h8, h9⟩ := hG
  have hlive : ∀ l, l ∈ (splitX X bl B psOld psNew).live ↔ l ∈ X.live ∨ l ∈ psNew.map (·.1) :=
    fun l => splitX_live l
  have hlv1 : ∀ l, l ∈ X.live → l ∈ (splitX X bl B psOld psNew).live :=
    fun l h => (hlive l).2 (Or.inl h)
  -- a node of another bucket is no fresh node
  have hother : ∀ c C l, c ≠ bl → X.t.bs !! c = some C → (C.ns !! l).isSome →
      l ∉ psNew.map (·.1) := by
    intro c C l _ hC hl hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    have := Write.objs_isSome_node X.t c C p.1 hC hl
    rw [(hnew p hp).1] at this; cases this
  have hbs : ∀ c C, (splitX X bl B psOld psNew).t.bs !! c = some C →
      (c = bl ∧ C = { B with ns := nsIns B.ns (psOld ++ psNew) }) ∨
      (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C hC
    by_cases e : c = bl
    · subst e; rw [splitX_bs] at hC; cases hC; exact Or.inl ⟨rfl, rfl⟩
    · rw [splitX_bs_ne _ _ _ _ _ _ e] at hC; exact Or.inr ⟨e, hC⟩
  -- an untouched node of `bl`
  have hunt : ∀ l r, nsIns B.ns (psOld ++ psNew) !! l = some r →
      (∃ p ∈ psOld ++ psNew, p.1 = l ∧ p.2 = r) ∨ (l ∉ (psOld ++ psNew).map (·.1) ∧ B.ns !! l = some r) := by
    intro l r hl
    by_cases hm : l ∈ (psOld ++ psNew).map (·.1)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      rw [nsIns_in _ _ hnd p hp] at hl; cases hl
      exact Or.inl ⟨p, hp, rfl, rfl⟩
    · rw [nsIns_out _ _ _ hm] at hl; exact Or.inr ⟨hm, hl⟩
  have hnotnew : ∀ l r, l ∉ (psOld ++ psNew).map (·.1) → B.ns !! l = some r →
      l ∈ (splitX X bl B psOld psNew).live → l ∈ X.live := by
    intro l r hm _ hl
    rcases (hlive l).1 hl with h | h
    · exact h
    · exact absurd (by rw [List.map_append]; exact List.mem_append_right _ h) hm
  refine ⟨h1, h2, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, h6, h7, h8, h9⟩
  · -- derefPre: live nodes
    intro c C l r hC hr hl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · rcases hunt l r hr with ⟨p, hp, rfl, rfl⟩ | ⟨hm, hr⟩
      · obtain ⟨a, b, d, e, -⟩ := hrec p hp
        refine ⟨a, b, d, fun c' hc' => ⟨(hlive c').2 (e c' hc').1, (e c' hc').2⟩⟩
      · obtain ⟨a, b, d, e⟩ := dA c B l r hb hr (hnotnew l r hm hr hl)
        refine ⟨a, b, d, fun c' hc' => ⟨hlv1 c' (e c' hc').1, nsIns_isSome _ _ _ (e c' hc').2⟩⟩
    · have hl' : l ∈ X.live := by
        rcases (hlive l).1 hl with h | h
        · exact h
        · exact absurd h (hother c C l hc hC (by rw [hr]; rfl))
      obtain ⟨a, b, d, e⟩ := dA c C l r hC hr hl'
      exact ⟨a, b, d, fun c' hc' => ⟨hlv1 c' (e c' hc').1, (e c' hc').2⟩⟩
  · -- derefPre: live buckets
    intro c C hC hcl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · obtain ⟨hbm, -⟩ := dB c B hb hcl
      refine ⟨fun k c' hk => ?_, fun hrn => ?_⟩
      · obtain ⟨a, b⟩ := hbm k c' hk
        refine ⟨a, ?_⟩
        by_cases e : c' = c
        · subst e; rw [splitX_bs]; rfl
        · rw [splitX_bs_ne _ _ _ _ _ _ e]; exact b
      · obtain ⟨rt, h, hm⟩ := hroot hcl hrn
        exact ⟨rt, h, (hlive rt).2 hm⟩
    · obtain ⟨hbm, hrt⟩ := dB c C hC hcl
      refine ⟨fun k c' hk => ?_, fun hrn => ?_⟩
      · obtain ⟨a, b⟩ := hbm k c' hk
        refine ⟨a, ?_⟩
        by_cases e : c' = bl
        · subst e; rw [splitX_bs]; rfl
        · rw [splitX_bs_ne _ _ _ _ _ _ e]; exact b
      · obtain ⟨rt, h, hm⟩ := hrt hrn
        exact ⟨rt, h, hlv1 rt hm⟩
  · -- derefPre: every bucket live, no node at null
    intro c C hC
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · refine ⟨(dC c B hb).1, ?_⟩
      show nsIns B.ns (psOld ++ psNew) !! null = none
      rw [nsIns_out]
      · exact (dC c B hb).2
      · intro hm
        obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
        rcases List.mem_append.1 hp with hp | hp
        · have := hold p hp; rw [e, (dC c B hb).2] at this; cases this
        · exact (hnew p hp).2 e
    · exact dC c C hC
  · -- derefPre: the root bucket
    by_cases e : X.rl = bl
    · show ((splitX X bl B psOld psNew).t.bs !! X.rl).isSome
      rw [e, splitX_bs]; rfl
    · show ((splitX X bl B psOld psNew).t.bs !! X.rl).isSome
      rw [splitX_bs_ne _ _ _ _ _ _ e]; exact dD
  · -- derefPre: no dead object live
    intro l hl hlv
    rcases (hlive l).1 hlv with h | h
    · exact dE l hl h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      change (X.t.dead !! p.1).isSome = true at hl
      rw [dead_none_of_objs (hnew p hp).1] at hl; cases hl
  · -- liveFresh
    intro c C l r hC hr hl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · rcases hunt l r hr with ⟨p, hp, rfl, rfl⟩ | ⟨hm, hr⟩
      · obtain ⟨-, -, -, -, a, b⟩ := hrec p hp; exact ⟨a, b⟩
      · exact hF c B l r hb hr (hnotnew l r hm hr hl)
    · have hl' : l ∈ X.live := by
        rcases (hlive l).1 hl with h | h
        · exact h
        · exact absurd h (hother c C l hc hC (by rw [hr]; rfl))
      exact hF c C l r hC hr hl'
  · -- liveReach: buckets
    intro c C hC hcl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · exact bktReach_splitX hb (rB c B hb hcl)
    · exact bktReach_splitX hb (rB c C hC hcl)
  · -- liveReach: nodes
    intro c C l r hC hr hl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hc, hC⟩
    · exact hreach l r hr ((hlive l).1 hl)
    · have hl' : l ∈ X.live := by
        rcases (hlive l).1 hl with h | h
        · exact h
        · exact absurd h (hother c C l hc hC (by rw [hr]; rfl))
      exact rN' c C l r hC hr hl'

end g

end Spill

end bbolt
end EtcdGrove
end Perennial
