/-
U7p (`notes/bbolt-proof-plan.md`): **a bucket other than the root holds no nested bucket**
(`allEnts_plain_nonroot`, for `DeleteBucket`'s child, `Write/DelBktWp`): the entries of its logical
tree are plain, by `leafShape` on its leaf nodes, `posShape` on its view pages under its page
positions, and `inlineGood` on an inline bucket's page (`Spill/BktPlain`'s walk).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktPlain

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section plain
variable [GooseExts]

/-- **A bucket other than the root holds no nested bucket** (`leafShape`, `posShape`). -/
theorem allEnts_plain_nonroot (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hroot : bl ≠ X.rl) :
    ∀ w ∈ X.allEnts bl, ¬ isBktFlag w.flags := by
  have htc := hok.1
  have hcl : bktClean X.v X.t.mv.pgid'.toNat bl B := (htc.2.2.2.2.2 bl B hB).1
  have hnode : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, Spill.plainE w := by
    intro l r hr hlf w hw
    have hs := htc.2.1.2.2.1 bl B hB l r hr hlf w hw
    have he := hok.2.2.2.1 bl B hB l r hr w hw
    exact ⟨(Spill.notBkt_iff _).1 (fun h => hroot (hs.1 h)), he.1, he.2.1⟩
  have hpage : ∀ c0 p pg, posRoot B c0 → ownHas X.v.pages c0 p → X.v.pages !! p = some pg →
      pageFlags pg = leafPageFlag → ∀ i < pageCount pg,
        leafFlags pg i % 2 = 0 ∧ 0 < leafKsize pg i ∧
          leafKsize pg i + leafVsize pg i ≤ bboltEntryMax := by
    intro c0 p pg hc ho hp hfl i hi
    have hs := htc.2.1.2.2.2.1 bl B hB c0 p pg hc ho hp hfl i hi
    refine ⟨?_, hs.2.1⟩
    have : leafFlags pg i % 2 ≠ bucketLeafFlag := fun h => hroot (hs.1.1 h)
    unfold bucketLeafFlag at this; omega
  have hfx : ∀ (pg : List w8) j, (W32 (leafFlags pg j : Int)).toNat = leafFlags pg j := by
    intro pg j
    have := Spill.leafFlags_lt pg j
    rw [BitVec.toNat_ofInt]; simp; omega
  intro w hw
  unfold WX.allEnts WX.leaves at hw
  obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hw
  have hrp : X.rootPid bl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  rw [hrp] at hws
  apply (Spill.notBkt_iff _).2
  by_cases hrn : B.bv.rootNode' = null
  · by_cases h0 : B.ib.root' = W64 0
    · obtain ⟨-, -, hig, -⟩ := hcl.1 h0 hrn
      have hL : ltree X bl B.ib.root' = some (true, pageWs B.ipg) := by
        unfold ltree wpageAt resolve; rw [hB]; simp only
        rw [if_pos h0, if_pos hrn]; simp only
        rw [if_pos h0, if_pos h0]; simp only [Option.map_some, hig.2.1, decide_true]
      have hf : X.fuel = (X.v.pages.size + X.t.bs.size) + 1 := rfl
      rw [hf] at hws
      simp only [lleaves, hL, List.mem_singleton] at hws
      subst hws
      unfold pageWs at hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
      have hj' := List.mem_range.1 hj
      simp only [pageW, if_pos hig.2.1]
      rw [hfx]
      exact (hig.2.2.2.2 j hj').2
    · have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat B.ib.root'.toNat := (hcl.2.1 h0).2 hrn
      have hnm : B.nm = ∅ := (hcl.2.2.1 hrn).2
      have hLq : ∀ q : w64, treeHas X.v.pages B.ib.root'.toNat q.toNat →
          ltree X bl q = (X.v.pages !! q.toNat).map Spill.pgRead := by
        intro q _
        have hres : resolve B q = none := by
          unfold resolve; rw [if_neg h0, hnm]; rfl
        unfold ltree; rw [hB]; simp only
        rw [hres]; simp only
        unfold wpageAt; rw [if_neg h0, Option.map_map]; rfl
      rw [Spill.lleaves_pages (ltree X) bl X.v.pages X.t.mv.pgid'.toNat X.fuel B.ib.root' hwf hLq]
        at hws
      obtain ⟨pg, hpg, rfl⟩ := List.mem_map.1 hws
      obtain ⟨p, hown, hp, hfl, -⟩ := Spill.leavesF_wf _ _ _ _ hwf pg hpg
      have hpos : posRoot B B.ib.root'.toNat := Or.inl ⟨hrn, h0, rfl⟩
      unfold pageWs at hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
      have hj' := List.mem_range.1 hj
      simp only [pageW, if_pos hfl]
      rw [hfx]
      exact (hpage _ p pg hpos hown hp hfl j hj').1
  · obtain ⟨r0, hr0⟩ : ∃ r0, B.ns !! B.bv.rootNode' = some r0 := by
      obtain ⟨r, hr, -⟩ := (hcl.2.2.2.2.1 _ _ (hcl.2.2.2.1 hrn)).2; exact ⟨r, hr⟩
    have hres : resolve B B.ib.root' = some B.bv.rootNode' := by
      unfold resolve
      by_cases h0 : B.ib.root' = W64 0
      · rw [if_pos h0, if_neg hrn]
      · rw [if_neg h0]; exact hcl.2.2.2.1 hrn
    exact (Spill.lleaves_plain hB hcl hnode hpage X.fuel _ _ r0 hres hr0 ws hws w hw).1

end plain

end Write

end bbolt
end EtcdGrove
end Perennial
