/-
`node.spill` after its children's loop (U9w2, `notes/bbolt-proof-plan.md`; pure): **a top node is
its bucket's root after the children's loop and the kill** (`tail_rootN'`, the split's `G`
premise): `spCtx.top`'s chain from the bucket's root node to `n` at the start, its other nodes
spilled (so not in `N`) and not fresh, kept modulo sources by the children's loop's frame and
untouched by the kill; `n`'s parent still null; a node's root is unique.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneStep
public import Proof.go_etcd_io.bbolt.Spill.UTreeBnd
public import Proof.go_etcd_io.bbolt.Spill.DerefRel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section root
variable [GooseExts] [GoGlobalContext]

/-- A chain to `n` carried over to a bucket whose chain nodes have the same parents and `n` is a
root. -/
theorem nodeRootIn_transport {B B1 : BRec} {n : Loc} {r1 : NRec} (hn1 : B1.ns !! n = some r1)
    (hnull : r1.nv.parent' = null) {a rt : Loc} (h : nodeRootIn B a rt) (hrt : rt = n)
    (hk : ∀ x r, onChain B a n x → x ≠ n → B.ns !! x = some r →
      ∃ r', B1.ns !! x = some r' ∧ r'.nv.parent' = r.nv.parent') : nodeRootIn B1 a n := by
  induction h with
  | top m r hm hp =>
    subst hrt; exact nodeRootIn.top m r1 hn1 hnull
  | up m rt r hm hp hrest ih =>
    subst hrt
    by_cases e : m = rt
    · subst e; exact nodeRootIn.top m r1 hn1 hnull
    · obtain ⟨r', hr', hpar⟩ := hk m r (onChain.self m rt) e hm
      refine nodeRootIn.up m rt r' hr' (by rw [hpar]; exact hp) ?_
      rw [hpar]
      exact ih rfl fun x rx hx hne hrx => hk x rx (onChain.up m rt x r hm e hx) hne hrx

/-- **A top node is its bucket's root after the children's loop and the kill** (see the module
doc). -/
theorem tail_rootN' {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) (h0 : r'.nilCh.nv.parent' = null) :
    ∀ B rt, (X'.nilCh bl n r').t.bs !! bl = some B → nodeRootIn B B.bv.rootNode' rt → rt = n := by
  intro B1 rt hB1 hrt
  obtain ⟨hn', -, -, hnv, -, -, hfr0, hT⟩ := spEnd_rec hpre hsp hend
  obtain ⟨hn, -, hc⟩ := hpre
  rcases hc with ⟨hs, -⟩ | ⟨hut, hctx, -⟩
  · rw [hsp] at hs; cases hs
  have hpar : rn.nv.parent' = null := by
    have : r'.nv.parent' = rn.nv.parent' := by rw [hnv]
    exact this ▸ h0
  cases cs with
  | child pl rp j plo phi => exact absurd (hctx.1.symm.trans hpar) hctx.2.1
  | top =>
  obtain ⟨-, B0, hB0, hroot, hchain⟩ := hctx
  obtain ⟨B', hB', hsim, hns⟩ := hfr0.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B0 hB0
  rw [nilCh_eq hB', GMap.lookup_insert] at hB1
  cases hB1
  have hN := uTree_N_unspilled hut
  have hroot1 : nodeRootIn ({ B' with ns := B'.ns.insert n r'.nilCh } : BRec) B0.bv.rootNode' n := by
    refine nodeRootIn_transport (GMap.lookup_insert _ _ _) h0 hroot rfl ?_
    intro x r hx hne hr
    obtain ⟨rc, hrc, hsp'⟩ := hchain x hx hne
    have hxr : X.node bl x = some r := by unfold WX.node; rw [hB0]; exact hr
    rw [hxr] at hrc; cases hrc
    have hxT : x ∉ N ++ T := by
      intro hm
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨r2, hr2, hs2⟩ := hN x hm
        rw [hxr] at hr2; cases hr2; rw [hsp'] at hs2; cases hs2
      · rw [node_none_of_objs (hT x hm)] at hxr; cases hxr
    have hs := hns x hxT
    rw [hr] at hs
    cases e : B'.ns !! x with
    | none => rw [e] at hs; exact absurd hs id
    | some r2 =>
      rw [e] at hs
      refine ⟨r2, ?_, nodeSim_parent hs⟩
      show (B'.ns.insert n r'.nilCh) !! x = some r2
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact e
  have hbv : ({ B' with ns := B'.ns.insert n r'.nilCh } : BRec).bv.rootNode' = B0.bv.rootNode' := by
    show B'.bv.rootNode' = _; rw [hsim.1]
  rw [hbv] at hrt
  exact nodeRootIn_unique hrt hroot1

end root

end Spill

end bbolt
end EtcdGrove
end Perennial
