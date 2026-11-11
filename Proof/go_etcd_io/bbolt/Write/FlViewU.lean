/-
`flViewU` (the exclusive part's agreement of the records with the freelist) under a non-root
leaf's node record replaced by `node.put`'s or `node.del`'s (U7h, the review's U1: `Put`,
`Delete`): `withWs`'s (`flView_withWs'`, `covU_withWs`), carried to `setNode` (the same logical
tree, page ids and cache).
-/
module

public import Proof.go_etcd_io.bbolt.Write.CovU
public import Proof.go_etcd_io.bbolt.Write.DataCongr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section flviewu
variable [GooseExts]

/-- **A non-root leaf's new entries keep `flViewU`.** -/
theorem flViewU_withWs (X : WX) (fl : FLPg) (bl l : Loc) (ws' : List WEntry) (h : flViewU X fl)
    (hleaf : ∀ B r, X.t.bs !! bl = some B → B.ns !! l = some r → r.nv.isLeaf' = true)
    (hroot : bl ≠ X.rl) : flViewU (X.withWs bl l ws') fl :=
  ⟨flView_withWs' X fl bl l ws' h.1 hleaf hroot, covU_withWs X bl l ws' h.2.1 hleaf hroot,
    h.2.2.1, h.2.2.2⟩

/-- **`setNode` and `withWs` agree on what `flViewU` reads** (the record keeps its page id and
leaf flag). -/
theorem flViewU_setNode (X : WX) (fl : FLPg) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r.nv.isLeaf' = true)
    (hlf' : r'.nv.isLeaf' = r.nv.isLeaf') (hpg : r'.nv.pgid' = r.nv.pgid')
    (hroot : bl ≠ X.rl) (h : flViewU X fl) : flViewU (X.setNode bl l r') fl := by
  have hY := flViewU_withWs X fl bl l r'.ws h (fun B0 r0 hB0 hr0 => by
    rw [hB] at hB0; cases hB0; rw [hr] at hr0; cases hr0; exact hlf) hroot
  let Y := X.withWs bl l r'.ws
  let Z := X.setNode bl l r'
  have hZ : Z.t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l r' } := by
    show (X.setNode bl l r').t.bs = _
    unfold WX.setNode WX.setBkt; rw [hB]
  have hYb : Y.t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l { r with ws := r'.ws } } := by
    show (X.withWs bl l r'.ws).t.bs = _
    unfold WX.withWs; rw [hB]; simp only [hr]
  have hv : Z.v = Y.v := by
    show (X.setNode bl l r').v = (X.withWs bl l r'.ws).v
    unfold WX.setNode WX.setBkt; rw [hB]; rfl
  have hrl : Z.rl = Y.rl := by
    show (X.setNode bl l r').rl = (X.withWs bl l r'.ws).rl
    unfold WX.setNode WX.setBkt; rw [hB]; rfl
  have hlt : ltree Z = ltree Y := ltree_setNode_eq X bl l B r r' hB hr hlf'
  have hfuel : Z.fuel = Y.fuel := by
    unfold WX.fuel; rw [hZ, hYb, GMap.map_size_insert_Some _ _ _ _ hB,
      GMap.map_size_insert_Some _ _ _ _ hB, hv]
  have hbsc : ∀ c, (Z.t.bs !! c).map (fun C => (C.ib, C.bv, C.nm, C.bm)) =
      (Y.t.bs !! c).map (fun C => (C.ib, C.bv, C.nm, C.bm)) := by
    intro c; rw [hZ, hYb]
    by_cases hc : c = bl
    · subst hc; simp
    · simp [Ne.symm hc]
  have hrp : ∀ c, Z.rootPid c = Y.rootPid c := by
    intro c; unfold WX.rootPid
    have := congrArg (Option.map fun x : InBucket × _ × _ × _ => x.1.root') (hbsc c)
    simp only [Option.map_map, Function.comp_def] at this
    exact congrArg (fun o => Option.getD o 0) this
  have hbkt : ∀ n, bktLoc Z n = bktLoc Y n := by
    intro n; unfold bktLoc; rw [hrl]
    have := congrArg (Option.map fun x : InBucket × _ × _ × GMap GoString Loc => x.2.2.2) (hbsc Y.rl)
    simp only [Option.map_map, Function.comp_def] at this
    cases e1 : Z.t.bs !! Y.rl <;> cases e2 : Y.t.bs !! Y.rl <;> simp_all
  have hleaves : ∀ c, Z.leaves c = Y.leaves c := by
    intro c; unfold WX.leaves; rw [hlt, hfuel, hrp]
  have hroots : rootEnts Z = rootEnts Y := by unfold rootEnts; rw [hrl, hleaves]
  have hsome : ∀ c, (Z.t.bs !! c).isSome = (Y.t.bs !! c).isSome := by
    intro c; have := congrArg Option.isSome (hbsc c); simpa using this
  have hpos : ∀ c, Z.positions c = Y.positions c := by
    intro c; unfold WX.positions; rw [hlt, hfuel, hrp]
  have hpe : ∀ c pid, Z.posExtent c pid = Y.posExtent c pid := by
    intro c pid
    apply posExtent_eq Y Z c pid hv
    rw [hZ, hYb]
    by_cases hc : c = bl
    · subst hc
      simp only [GMap.lookup_insert, Option.map_some, Option.some.injEq]
      unfold posIdOf
      show (match resolve B pid with
          | some l0 => ((B.ns.insert l r' !! l0).map fun r0 : NRec => r0.nv.pgid').getD 0
          | none => pid) =
        (match resolve B pid with
          | some l0 => ((B.ns.insert l { r with ws := r'.ws } !! l0).map fun r0 : NRec => r0.nv.pgid').getD 0
          | none => pid)
      cases resolve B pid with
      | none => rfl
      | some l0 =>
        by_cases hl0 : l0 = l
        · subst hl0; simp [hpg]
        · simp [Ne.symm hl0]
    · simp [Ne.symm hc]
  have hext : ∀ c, Z.extents c = Y.extents c := by
    intro c; unfold WX.extents; rw [hpos]; congr 1; funext pid; exact hpe c pid
  refine ⟨flView_congr Y Z fl hv (lCovers_congr Y Z hv hroots hbkt hsome (fun c _ => hext c)) hY.1,
    covU_congr Y Z hv hroots hbkt hsome (fun c _ => hpos c) (fun c pid _ => hpe c pid) hY.2.1,
    ?_, hY.2.2.2⟩
  rw [hv]; exact hY.2.2.1

end flviewu

end Write

end bbolt
end EtcdGrove
end Perennial
