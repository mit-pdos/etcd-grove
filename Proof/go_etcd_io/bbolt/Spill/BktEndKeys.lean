/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`): **a searchable bucket's
leaf entries have distinct keys** (`leaves_keys_ne`, from `bktLocalOK` alone: `BktValKey`'s
`allEnts_key_injR` over `wOKR`, as distinct occurrences). Each leaf's entries are sorted (a node's
by `nodeClean`, a page's by `viewWF`), and the walk's blocks have disjoint key bounds
(`LR.bInvL_walk`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktValKey

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section keys
variable [GooseExts]

/-- A leaf of a clean bucket's walk is sorted (`leaf_pwR` from `bktClean` and `viewWF`). -/
theorem leaf_pw_loc {X : WX} {bl : Loc} {B : BRec} {hwm : Nat} (hB : X.t.bs !! bl = some B)
    (hc : bktClean X.v hwm bl B) (hv : viewWF X.v)
    (p : w64) (ws : List WEntry) (hL : ltree X bl p = some (true, ws)) : Write.wsPw ws := by
  unfold ltree at hL
  rw [hB] at hL
  simp only at hL
  cases hr : resolve B p with
  | some l =>
    rw [hr] at hL
    simp only at hL
    cases hrl : B.ns !! l with
    | none => rw [hrl] at hL; cases hL
    | some r =>
      rw [hrl] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      rw [← hL.2]
      exact Write.wsSorted_pw _ (hc.2.2.2.2.2.2.2.1 l r hrl).2.2.2.1
  | none =>
    rw [hr] at hL
    simp only at hL
    cases hp : wpageAt X.v B p with
    | none => rw [hp] at hL; cases hL
    | some x =>
      obtain ⟨pa, pg⟩ := x
      rw [hp] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
      obtain ⟨hfl, rfl⟩ := hL
      by_cases hin : B.ib.root' = W64 0
      · have hrn : B.bv.rootNode' = null := by
          unfold resolve at hr; rw [if_pos hin] at hr; split at hr
          · assumption
          · cases hr
        have hg := (hc.1 hin hrn).2.2.1
        unfold wpageAt at hp; rw [if_pos hin] at hp
        split at hp
        · simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨-, rfl⟩ := hp
          exact LR.pageWs_pw _ hg.2.1 hg.2.2.1.2.2.2
        · cases hp
      · have hpg : X.v.pages !! p.toNat = some pg := by
          unfold wpageAt at hp; rw [if_neg hin] at hp
          cases h : X.v.pages !! p.toNat with
          | none => rw [h] at hp; cases hp
          | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                          Prod.mk.injEq] at hp; rw [hp.2]
        exact LR.pageWs_pw pg hfl (LR.viewWF_leaf_sorted X.v hv _ pg hpg hfl)

/-- **A searchable bucket's leaf entries have distinct keys** (as occurrences). -/
theorem leaves_keys_ne {X : WX} {bl : Loc} (h : bktLocalOK X bl) :
    ((X.leaves bl).flatten).Pairwise (fun a b => a.key ≠ b.key) := by
  obtain ⟨-, B, hB, hc, ⟨bnd, hbk⟩, -, -, hv⟩ := h
  have hwalk := LR.bInvL_walk X bl B bnd _ hB hc hbk hv X.fuel _ _
    (LR.bInvL_root X bl B bnd _ hB hc hbk hv)
  unfold WX.leaves
  rw [← Write.lleavesB_snd, List.pairwise_flatten, List.pairwise_map]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have hL := Write.lleavesB_leaf (ltree X) bl X.fuel _ _ x hx
    refine (leaf_pw_loc hB hc hv x.1 x.2.2 hL).imp fun {a b} h e => ?_
    rw [e] at h; exact go.goStringLt_irrefl _ h
  · refine List.Pairwise.imp_of_mem ?_ hwalk.2.1
    intro x y hx hy hxy a ha b hb e
    exact hxy a.key (hwalk.1 x hx a ha) (e ▸ hwalk.1 y hy b hb)

end keys

end Spill

end bbolt
end EtcdGrove
end Perennial
