/-
`Bucket.spill`'s root loop (U9x3, `notes/bbolt-proof-plan.md`): **the root bucket's keys at the
start** (`rootKeys_wOKR`, `BktLoopPureStart.rootKeys_start`'s proof). The walk of a bucket's
logical tree visits a materialized node or a page under one of its page positions (`walkInv`, the
converse of `BktSlotCov.pos_ownHas`: from a node's branch entry an unmaterialized child is a
position, from a page a branch child is under the same position, `ownTo`); a node's entries are
bounded by `entriesBounded`, a page's leaf entries by `posShape` (the root bucket's names at most
`MaxKeySize`) and `pageKeys_pos`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktRootPos

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section rootkeys
variable [GooseExts]

/-- A position the walk of `B` visits: a materialized node, or a page under a page position. -/
def walkInv (X : WX) (B : BRec) (pid : w64) : Prop :=
  (resolve B pid).isSome ∨ ∃ c, posRoot B c ∧ ownTo X.v.pages c pid.toNat

/-- The pages under a well-formed tree's root are well-formed. -/
theorem treeWF_ownHas {P : Pages} {hwm c p : Nat} (h : ownHas P c p) (hw : treeWF P hwm c) :
    treeWF P hwm p := by
  induction h with
  | root => exact hw
  | child r pg i id hpg hf hi _ ih =>
    apply ih
    rcases hw with ⟨_, pg', _, _, hpg', _, _, hpt⟩
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf' _ _ =>
      rw [hf] at hf'; exact absurd hf' (by unfold branchPageFlag leafPageFlag; decide)
    | branch _ _ _ _ hch => exact hch i hi

/-- A child the walk reaches from a branch entry `w` of the node `l` is a walk position. -/
theorem walkInv_node {X : WX} {B : BRec} (h0 : B.ib.root' ≠ W64 0) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) (hlf : r.nv.isLeaf' = false) {w : WEntry} (hw : w ∈ r.ws) :
    walkInv X B w.pgid := by
  by_cases hs : (resolve B w.pgid).isSome
  · exact Or.inl hs
  · right
    have hnm : B.nm !! w.pgid = none := by
      unfold resolve at hs; rw [if_neg h0] at hs
      cases h : B.nm !! w.pgid with
      | none => rfl
      | some _ => rw [h] at hs; simp at hs
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
    exact ⟨w.pgid.toNat, Or.inr ⟨l, i, by rw [Write.w64_toNat_cast]; exact ⟨r, w, hr, hlf, hi,
      rfl, hnm⟩, w.pgid.isLt⟩, Or.inl rfl⟩

/-- **The walk of the root bucket's logical tree meets keys of `1..MaxKeySize` bytes.** -/
theorem walk_keys {X : WX} {B : BRec} (hok : wOKR X) (hB : X.t.bs !! X.rl = some B)
    (h0 : B.ib.root' ≠ W64 0) :
    ∀ n pid, walkInv X B pid → ∀ ws ∈ lleaves (ltree X) X.rl n pid, ∀ we ∈ ws,
      0 < we.key.length ∧ we.key.length ≤ maxKeySize := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (hok.1.2.2.2.2.2 X.rl B hB).1
  have hvw : viewWF X.v := hok.2.2.2.2.2.2.2
  intro n
  induction n with
  | zero => intro pid _ ws hws; simp [lleaves] at hws
  | succ n ih =>
    intro pid hinv ws hws we hwe
    unfold lleaves at hws
    cases hres : resolve B pid with
    | some l =>
      have hL : ltree X X.rl pid = (B.ns !! l).map (fun r => (r.nv.isLeaf', r.ws)) := by
        unfold ltree; rw [hB]; simp only [hres]
      rw [hL] at hws
      cases hr : B.ns !! l with
      | none => rw [hr] at hws; simp at hws
      | some r =>
        rw [hr] at hws
        simp only [Option.map_some] at hws
        cases hlf : r.nv.isLeaf' with
        | true =>
          rw [hlf] at hws
          simp only [List.mem_singleton] at hws
          subst hws
          have := hok.2.2.2.1 X.rl B hB l r hr we hwe
          exact ⟨this.1, this.2.2 rfl⟩
        | false =>
          rw [hlf] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          exact ih w.pgid (walkInv_node h0 hr hlf hw) ws hws' we hwe
    | none =>
      obtain ⟨c, hc, hto⟩ : ∃ c, posRoot B c ∧ ownTo X.v.pages c pid.toNat := by
        rcases hinv with h | h
        · rw [hres] at h; cases h
        · exact h
      cases hp : X.v.pages !! pid.toNat with
      | none =>
        have hL : ltree X X.rl pid = none := by
          unfold ltree wpageAt; rw [hB]; simp only [hres]; rw [if_neg h0, hp]; rfl
        rw [hL] at hws; simp at hws
      | some pg =>
        have hL : ltree X X.rl pid = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
          unfold ltree wpageAt; rw [hB]; simp only [hres]; rw [if_neg h0, hp]; rfl
        rw [hL] at hws
        have hown := ownTo_ownHas hto hp
        have hpt : pageTreeWF X.v.pages X.t.mv.pgid'.toNat pg pg.length := by
          rcases treeWF_ownHas hown (posRoot_treeWF hcl hc) with ⟨_, pg', _, _, hpg', _, _, hpt⟩
          rw [hp] at hpg'; cases hpg'; exact hpt
        by_cases hfl : pageFlags pg = leafPageFlag
        · rw [decide_eq_true hfl] at hws
          simp only [List.mem_singleton] at hws
          subst hws
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hwe
          rw [List.mem_range] at hi
          have hkpos := Write.pageKeys_pos _ _ pg hpt ((mat_strict X.v hvw).1 _ pg hp)
          refine ⟨by rw [mat_pageW_key]; exact hkpos i hi, ?_⟩
          have hs := hok.1.2.1.2.2.2.1 X.rl B hB c pid.toNat pg hc hown hp hfl i hi
          rw [(mat_pageW_leaf pg i hfl).2.2.1]
          unfold leafKey
          have := Write.bytesAt_length_le pg (elemOff i + leafPos pg i) (leafKsize pg i)
          have := hs.2.2.1 rfl
          omega
        · rw [decide_eq_false hfl] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have hbr : pageFlags pg = branchPageFlag := by
            rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
            · exact absurd h hfl
            · exact h
          refine ih _ ?_ ws hws' we hwe
          by_cases hs : (resolve B (pageW pg i).pgid).isSome
          · exact Or.inl hs
          · refine Or.inr ⟨c, hc, Or.inr ⟨pid.toNat, pg, i, hown, hp, hbr, hi, ?_⟩⟩
            rw [pageW_pgid_branch pg i hbr, rp_cast_toNat (Write.branchPgid_lt pg i)]

/-- **The root bucket's entries' keys are not empty and at most `MaxKeySize`** (from `wOKR`). -/
theorem rootKeys_wOKR {X : WX} (hok : wOKR X) :
    ∀ we ∈ X.allEnts X.rl, 0 < we.key.length ∧ we.key.length ≤ maxKeySize := by
  have htc := hok.1
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 htc.2.2.2.2.1
  have h0 : B.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B hB
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (htc.2.2.2.2.2 X.rl B hB).1
  intro we hwe
  unfold WX.allEnts WX.leaves at hwe
  obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hwe
  have hrp : X.rootPid X.rl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  rw [hrp] at hws
  refine walk_keys hok hB h0 _ _ ?_ ws hws we hw
  by_cases hs : (resolve B B.ib.root').isSome
  · exact Or.inl hs
  · right
    have hrn : B.bv.rootNode' = null := by
      apply Classical.byContradiction
      intro hne
      apply hs
      unfold resolve; rw [if_neg h0, hcl.2.2.2.1 hne]; rfl
    exact ⟨_, Or.inl ⟨hrn, h0, rfl⟩, Or.inl rfl⟩

/-- A flag word whose low bit is set is a bucket's. -/
theorem isBkt_of_lowBit {n : Nat} (hn : n < 2 ^ 32) (h : n % 2 = 1) :
    isBktFlag (W32 (n : Int)) := by
  unfold isBktFlag
  intro e
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_and] at e'
  have h1 : (W32 (n : Int)).toNat = n := by simp only [BitVec.toNat_ofInt]; omega
  rw [h1] at e'
  have h2 : n &&& (W32 1).toNat = n % 2 := by
    show n &&& 1 = n % 2; rw [Nat.and_one_is_mod]
  rw [h2, h] at e'
  exact absurd e' (by decide)

/-- **The walk of the root bucket's logical tree meets bucket entries only** (`leafShape` for a
node's entries, `posShape` for a page's under a page position). -/
theorem walk_bkt {X : WX} {B : BRec} (hok : wOKR X) (hB : X.t.bs !! X.rl = some B)
    (h0 : B.ib.root' ≠ W64 0) :
    ∀ n pid, walkInv X B pid → ∀ ws ∈ lleaves (ltree X) X.rl n pid, ∀ we ∈ ws,
      isBktFlag we.flags := by
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (hok.1.2.2.2.2.2 X.rl B hB).1
  intro n
  induction n with
  | zero => intro pid _ ws hws; simp [lleaves] at hws
  | succ n ih =>
    intro pid hinv ws hws we hwe
    unfold lleaves at hws
    cases hres : resolve B pid with
    | some l =>
      have hL : ltree X X.rl pid = (B.ns !! l).map (fun r => (r.nv.isLeaf', r.ws)) := by
        unfold ltree; rw [hB]; simp only [hres]
      rw [hL] at hws
      cases hr : B.ns !! l with
      | none => rw [hr] at hws; simp at hws
      | some r =>
        rw [hr] at hws
        simp only [Option.map_some] at hws
        cases hlf : r.nv.isLeaf' with
        | true =>
          rw [hlf] at hws
          simp only [List.mem_singleton] at hws
          subst hws
          exact (hok.1.2.1.2.2.1 X.rl B hB l r hr hlf we hwe).2 rfl
        | false =>
          rw [hlf] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          exact ih w.pgid (walkInv_node h0 hr hlf hw) ws hws' we hwe
    | none =>
      obtain ⟨c, hc, hto⟩ : ∃ c, posRoot B c ∧ ownTo X.v.pages c pid.toNat := by
        rcases hinv with h | h
        · rw [hres] at h; cases h
        · exact h
      cases hp : X.v.pages !! pid.toNat with
      | none =>
        have hL : ltree X X.rl pid = none := by
          unfold ltree wpageAt; rw [hB]; simp only [hres]; rw [if_neg h0, hp]; rfl
        rw [hL] at hws; simp at hws
      | some pg =>
        have hL : ltree X X.rl pid = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
          unfold ltree wpageAt; rw [hB]; simp only [hres]; rw [if_neg h0, hp]; rfl
        rw [hL] at hws
        have hown := ownTo_ownHas hto hp
        have hpt : pageTreeWF X.v.pages X.t.mv.pgid'.toNat pg pg.length := by
          rcases treeWF_ownHas hown (posRoot_treeWF hcl hc) with ⟨_, pg', _, _, hpg', _, _, hpt⟩
          rw [hp] at hpg'; cases hpg'; exact hpt
        by_cases hfl : pageFlags pg = leafPageFlag
        · rw [decide_eq_true hfl] at hws
          simp only [List.mem_singleton] at hws
          subst hws
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hwe
          rw [List.mem_range] at hi
          have hs := hok.1.2.1.2.2.2.1 X.rl B hB c pid.toNat pg hc hown hp hfl i hi
          rw [(mat_pageW_leaf pg i hfl).1]
          refine isBkt_of_lowBit (by unfold leafFlags; exact BitVec.isLt _) ?_
          have := hs.1.2 rfl
          unfold bucketLeafFlag at this; exact this
        · rw [decide_eq_false hfl] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have hbr : pageFlags pg = branchPageFlag := by
            rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
            · exact absurd h hfl
            · exact h
          refine ih _ ?_ ws hws' we hwe
          by_cases hs : (resolve B (pageW pg i).pgid).isSome
          · exact Or.inl hs
          · refine Or.inr ⟨c, hc, Or.inr ⟨pid.toNat, pg, i, hown, hp, hbr, hi, ?_⟩⟩
            rw [pageW_pgid_branch pg i hbr, rp_cast_toNat (Write.branchPgid_lt pg i)]

/-- **The root bucket's entries are bucket entries** (from `wOKR`; `RInv.rootBkt` at the start). -/
theorem rootBkt_wOKR {X : WX} (hok : wOKR X) : ∀ we ∈ X.allEnts X.rl, isBktFlag we.flags := by
  have htc := hok.1
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 htc.2.2.2.2.1
  have h0 : B.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B hB
  have hcl : bktClean X.v X.t.mv.pgid'.toNat X.rl B := (htc.2.2.2.2.2 X.rl B hB).1
  intro we hwe
  unfold WX.allEnts WX.leaves at hwe
  obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hwe
  have hrp : X.rootPid X.rl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  rw [hrp] at hws
  refine walk_bkt hok hB h0 _ _ ?_ ws hws we hw
  by_cases hs : (resolve B B.ib.root').isSome
  · exact Or.inl hs
  · right
    have hrn : B.bv.rootNode' = null := by
      apply Classical.byContradiction
      intro hne
      apply hs
      unfold resolve; rw [if_neg h0, hcl.2.2.2.1 hne]; rfl
    exact ⟨_, Or.inl ⟨hrn, h0, rfl⟩, Or.inl rfl⟩

end rootkeys

end Spill

end bbolt
end EtcdGrove
end Perennial
