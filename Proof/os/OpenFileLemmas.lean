/-
The lemmas of `OpenFile.lean`'s proofs (`walk_upd_insert`, `lookupH_create`, `openFd_rw`,
`osTree_halves`), in a module of their own so that the modules over them import them without the
proofs (import tiers, 2026-11-18).
-/
module

public import Proof.os.ErrorOk
public import Proof.syscall.ErrorOk
public import Spec.os.OpenFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- A walk that succeeds never took the entry `b` of `j`, which is absent: adding it changes
nothing. -/
theorem walk_upd_insert {m : Tree} {j : Ino} {b : GoString} {v : Node} (hn : m.entry j b = none) :
    ∀ (cs : List GoString) (n x : Node), walk m n cs = some x →
      walk (m.upd j (fun d => <[b := v]> d)) n cs = some x
  | [], n, x, h => h
  | c :: cs, n, x, h => by
    cases n with
    | file _ => simp [walk] at h
    | dir j' =>
      simp only [walk] at h ⊢
      have he : (m.upd j (fun d => <[b := v]> d)).entry j' c = m.entry j' c := by
        rw [entry_upd]
        split
        · rename_i hj
          subst hj
          by_cases hc : b = c
          · subst hc; rw [hn] at h; cases h
          · rw [GMap.lookup_insert_ne _ _ hc, getD_lookup]; rfl
        · rfl
      rw [he]
      cases hm : m.entry j' c with
      | none => rw [hm] at h; cases h
      | some n' =>
        rw [hm] at h
        exact walk_upd_insert hn cs n' x h

/-- After a create of `b` in the directory `j` that `d` names (nothing at `d/b` before), `d/b`
names the new file. -/
theorem lookupH_create {R : Roots} {V : Hist} {d b : GoString} {j i : Ino} (s : Nat)
    (hr : RootsOk R) (hd : lookupH R V d = some (.dir j)) (hb : NameOk b)
    (hn : lookupH R V (child d b) = none) :
    lookupH R (V.push ⟨.create j b i, s⟩) (child d b) = some (.file i) := by
  have ht : (Hist.st R (V.push ⟨.create j b i, s⟩)).tree =
      (Hist.st R V).tree.upd j (fun dd => <[b := Node.file i]> dd) := by
    show (V.push _).now = _
    rw [Hist.push_now]; rfl
  have hen : (Hist.st R V).tree.entry j b = none := by
    rw [← lookup_child (st := Hist.st R V) hr hd hb]; exact hn
  have hd' : lookupH R (V.push ⟨.create j b i, s⟩) d = some (.dir j) := by
    obtain ⟨r, j0, cs, hrj, hcs, hp, hw⟩ := lookup_some (st := Hist.st R V) hd
    unfold lookupH
    rw [hp, lookup_joinPath (st := Hist.st R (V.push _)) hr hrj hcs, ht]
    exact walk_upd_insert hen cs _ _ hw
  unfold lookupH
  rw [lookup_child (st := Hist.st R (V.push _)) hr hd' hb, ht, entry_upd, if_pos rfl]
  exact GMap.lookup_insert _ _ _

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

theorem openFd_rw (i : Ino) : openFd i (W64 0x80042) = ⟨i, true, true, none, none⟩ := by
  simp [openFd, O_WRONLY, O_RDONLY]

theorem osTree_halves (q : Qp) (R : Roots) (V : Hist) :
    osTree (GF := GF) (DFrac.own q) R V ⊣⊢ osTree (DFrac.own (q.half + q.half)) R V := by
  rw [Qp.half_add_half]; exact BIBase.BiEntails.rfl


end proof

end EtcdGrove
end Perennial
