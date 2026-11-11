/-
`Bucket.spill`'s root loop (U9q, `notes/bbolt-proof-plan.md`; U9x5): **the loop's end**
(`rinv_end_nil`, `rinv_end`; moved here from `Spill/BktLoopInv`): from `RInv` after the last key,
the spill's success (`spillOK`, `spillBufs`) with no root node, or the root node's spill's pre and,
after it, the spill's success. The pieces are `Spill/BktEnd*`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndNilEls
public import Proof.go_etcd_io.bbolt.Spill.BktEndRoot

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section fin
variable [GooseExts]


/-- A bucket's parent pointers from its records' well-formedness (`nodeClean`'s last clause). -/
theorem parOK_of_local {X : WX} {bl : Loc} (h : bktLocalOK X bl) : parOK X bl := by
  obtain ⟨-, B, hB, hcl, -⟩ := h
  intro m rm hm _ c hc
  unfold WX.node at hm ⊢
  rw [hB] at hm ⊢
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17⟩ := hcl.2.2.2.2.2.2.2.1 m rm hm
  exact h17 c hc

/-- On the chain from a node up to itself, only the node. -/
theorem onChain_self {B : BRec} {a x : Loc} (h : onChain B a a x) : x = a := by
  cases h with
  | self => rfl
  | up _ _ _ _ _ hne _ => exact absurd rfl hne

/-- **The end, no root node**: nothing was put, the root bucket has no root node, and the records
are the spill's success as they are (`RInv.same`, `RInv.putRoot`; `hvC`: `wdbW_ofC` at the
call). -/
theorem rinv_end_nil {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' = null)
    (hvC : X.v = View.ofC X.v.base w.C) (htx : X0.t.mv.txid'.toNat < 2 ^ 63) :
    spillOK X0 X w0.C w0.fl w.fl w0.wtxid ∧ spillBufs X w0.C w.fl := by
  have hnv : ∀ k ∈ keys, ∀ v p, ks k ≠ .val v p := by
    intro k hkm v p he
    cases p with
    | true => exact hI.putRoot ⟨k, v, he⟩ B hB hrn
    | false =>
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hkm
      have hjl : j < keys.length := (List.getElem?_eq_some_iff.1 hj).1
      exact ((hks j k hj).1 hjl).2 v he
  obtain ⟨rfl, rfl, rfl⟩ := hI.same hnv
  rw [hB0] at hB; cases hB
  have hkids : ∀ k c, B0.bm !! k = some c → ∃ C0, X.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null := by
    intro k c hc
    have hkm : k ∈ keys := (hk k).2 (by rw [hc]; rfl)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hkm
    have hjl : j < keys.length := (List.getElem?_eq_some_iff.1 hj).1
    have hnt := ((hks j k hj).1 hjl).1
    have hch := hI.kids k c hc
    cases hkk : ks k with
    | todo => exact absurd hkk hnt
    | nilc => rw [hkk] at hch; exact hch.2
    | val v p => exact absurd hkk (hnv k hkm v p)
  obtain ⟨h, S, hS, hbase, hSb, hEls⟩ := end_nilTree' hpre hreach hfv hB0 hrn hkids
    (fun k c hc => by obtain ⟨Dc0, -, hDc0⟩ := hI.lroot; obtain ⟨-, -, -, -, hne, -⟩ := hDc0 k c hc; exact hne)
    hvC hI.cok hI.hwm0
  have hcp : w.C.pages = X.v.pages := by
    have := congrArg View.pages hvC; simpa [View.ofC] using this.symm
  obtain ⟨hshape, hnames, hbkts⟩ := hEls (spP X) X.rootPage _ h S hS rfl (fun _ _ => rfl)
  refine ⟨?_, end_bufs_nil hI⟩
  exact spillOK_of_root' X X w.C w.fl w.fl w.wtxid [] h S (pgSlots (spP X) S) hcp rfl
    (by rw [BitVec.le_def]; exact Nat.le_refl _) hS hshape htx hnames hbkts rfl hbase
    (fun s hs => Or.inl hs) (fun s hs => Or.inl (hSb s hs))

/-- **The end, with a root node**: the root bucket's root node is the top of an unspilled tree
over the current page map and mark (`InitB`: its nested values `bvalS`, the visited children's new
ones, `BktVal`'s for the others), owning every owned slot (`O = []`); and after its spill and
`b.rootNode = root; SetRootPage` the spill's success. -/
theorem rinv_end {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hB : X.t.bs !! X0.rl = some B) (hrn : B.bv.rootNode' ≠ null)
    (hvC : X.v = View.ofC X.v.base w.C) (htx : X0.t.mv.txid'.toNat < 2 ^ 63) :
    ∃ rn h F D N E, rn.nv.spilled' = false ∧
      spPre X w X0.rl B.bv.rootNode' rn [] none none h F D N E .top ∧
      ∀ (X1 : WX) (w1 : WDb) (st1 : List FLStep) (B1 : BRec) (rt : Loc) (rr : NRec),
        spDone X X1 w w1 X0.rl B.bv.rootNode' rn [] none none h D N E .top st1 →
        X1.t.bs !! X0.rl = some B1 → B1.ns !! rt = some rr → rt ∈ X1.live →
        rr.nv.spilled' = true → rr.nv.parent' = null → nodeRootIn B1 B1.bv.rootNode' rt →
        spillOK X0 (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w0.fl w1.fl w0.wtxid ∧
          spillBufs (X1.setBkt X0.rl (bkRooted B1 rt rr.nv.pgid')) w0.C w1.fl := by
  obtain ⟨rn, h, F, D, N, E, hnode, hpar, hunsp, hu, hF, hnd, hDo, hDi, hEls⟩ :=
    end_rootTree hpre hreach hfv hB0 hk hI hks hB hrn hvC
  have hwid : w.wtxid = w0.wtxid := wtxid_of_C hI.C
  have hrn' : B.ns !! B.bv.rootNode' = some rn := by
    unfold WX.node at hnode; rw [hB] at hnode; exact hnode
  obtain ⟨hsnd, hsl, hids, hlt⟩ := hI.slots
  refine ⟨rn, h, F, D, N, E, hunsp, ⟨hnode, by rw [hwid]; exact hI.G, Or.inr ⟨hu, ?_, ?_,
    by rw [hwid]; exact hF, hvC, rinv_freeNC hI, rinv_treeLt hI,
    parOK_of_local hI.rootOK.1⟩⟩, ?_⟩
  · refine ⟨hpar, B, hB, nodeRootIn.top _ rn hrn' hpar, fun x hx hne => ?_⟩
    exact absurd (onChain_self hx) hne
  · refine ⟨by simpa using hnd, fun s hs => hsl s (hDi s (by simpa using hs)), hids, hlt⟩
  · intro X1 w1 st1 B1 rt rr hdone hB1 hrr _ _ _ hroot
    exact end_post hI hvC htx (end_txid hI) hB hDo hDi hEls hunsp hdone hB1 hrr hroot

end fin

end Spill

end bbolt
end EtcdGrove
end Perennial
