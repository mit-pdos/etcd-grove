/- Lean-first (no Rocq counterpart).

# The WAL's boot, pure obligations (`notes/wal-fsext-w4c-plan.md`, §3 and "W4c U3 log")

`walInv_alloc`'s pure premises that are facts of the WAL state `s` alone:

* **`DirsOk`/`DirsAvoid` from `DirsRoots`**: a durable directory (`s.dirs`) that is a root of the
  shared mode resolves in every tree (a root's lookup walks no entry), so it resolves after any crash
  and through no slot of the area. `Create` needs `dirDurable r` of its area `r`, and no `fsExt` step
  adds to `s.dirs` (`TouchDirAll`'s spec gives a commit bound, not `dirDurable`); so the boot makes the
  area durable by taking it as a root: `s.dirs = {r}`, `(r, jr) ∈ R` (a world premise of the closed
  theorem). A directory below a root would need the claims of its spine in the invariant's `cl`,
  which the program's `osPathS` of the area holds instead.
* **`WalsBounded` across a crash** (`walsBounded_crash`): a crash keeps each WAL's metadata, and its
  history becomes an image (a prefix, possibly with a prefix of one more `Save`'s entries), with no
  index the old history lacked.
* **The first boot's state** (`walBoot0St`): the area, no WAL, the area durable.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- A root names its directory in every tree. -/
theorem lookupH_root {R : Roots} (hR : RootsOk R) {r : GoString} {j : Ino} (hr : (r, j) ∈ R)
    (m : Tree) : lookupH R (m, []) r = some (.dir j) := by
  unfold lookupH
  have h := lookup_joinPath (st := Hist.st R (m, [])) hR hr (cs := []) (fun c hc => by cases hc)
  simp only [joinPath, List.flatMap_nil, List.append_nil] at h
  rw [h]; rfl

/-- **The durable directories resolve after any crash**, being roots. -/
theorem dirsOk_roots {R : Roots} (hR : RootsOk R) {s : AbsDiskState} (h : DirsRoots R s)
    (cl : List Claim) (n : Nat) : DirsOk R s cl n := by
  intro dd hd m' _
  obtain ⟨j, hj⟩ := h dd hd
  exact ⟨j, lookupH_root hR hj m'⟩

/-- **The durable directories resolve through no slot of the area**, being roots. -/
theorem dirsAvoid_roots {R : Roots} (hR : RootsOk R) {s : AbsDiskState} (h : DirsRoots R s)
    (jr : Ino) : DirsAvoid R jr s := by
  intro dd hd m1 m2 _
  obtain ⟨j, hj⟩ := h dd hd
  rw [lookupH_root hR hj m1, lookupH_root hR hj m2]

/-- A crash keeps the durable directories. -/
theorem walStCrash_dirs {s s' : AbsDiskState} (h : walStCrash s s') : s'.dirs = s.dirs := h.2.1

/-- A crash keeps `DirsRoots`. -/
theorem dirsRoots_crash {R : Roots} {s s' : AbsDiskState} (hc : walStCrash s s')
    (h : DirsRoots R s) : DirsRoots R s' := by
  intro dd hd
  rw [walStCrash_dirs hc] at hd
  exact h dd hd

/-- A prefix of the entries of a history's `Save` has no maximal index if the `Save` has none. -/
theorem walHasMaxIdx_image {H I : List (WalOpG WalEnt)} {n : Nat} (hI : walImg H n I)
    (h : ¬ walHasMaxIdx (H.map WalOpG.toM)) : ¬ walHasMaxIdx (I.map WalOpG.toM) := by
  obtain ⟨j, -, -, hI⟩ := hI
  rintro ⟨o, ho, hm⟩
  rcases hI with rfl | ⟨hs, es, k, hj, -, rfl⟩
  · rw [List.map_take] at ho
    exact h ⟨o, List.mem_of_mem_take ho, hm⟩
  · rw [List.map_append, List.mem_append] at ho
    rcases ho with ho | ho
    · rw [List.map_take] at ho
      exact h ⟨o, List.mem_of_mem_take ho, hm⟩
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
      subst ho
      obtain ⟨e, he, hme⟩ := hm
      refine h ⟨WalOpG.toM (.save hs es), List.mem_map.2 ⟨_, List.mem_of_getElem? hj, rfl⟩, ?_⟩
      refine ⟨e, ?_, hme⟩
      simp only [List.map_take] at he
      exact List.mem_of_mem_take he

/-- **A crash keeps `WalsBounded`**: the metadata is kept, the history becomes an image of it. -/
theorem walsBounded_crash {s s' : AbsDiskState} (hc : walStCrash s s') (h : WalsBounded s) :
    WalsBounded s' := by
  intro dir d' hd'
  cases hd : s.wal !! dir with
  | none => rw [hc.2.2.2 dir hd] at hd'; cases hd'
  | some d =>
    obtain ⟨h1, h2, h3⟩ := h dir d hd
    rcases hc.2.2.1 dir d hd with ⟨-, h0⟩ | ⟨I, k, hI, -, h1'⟩
    · rw [h0] at hd'; cases hd'
    · rw [h1'] at hd'; cases hd'
      exact ⟨h1, h2, fun hx => walHasMaxIdx_image hI
        (fun hy => h3 ((walHasMaxIdx_normFrom _ _).2 hy)) ((walHasMaxIdx_normFrom _ _).1 hx)⟩

/-- **The first boot's WAL state**: the area `r`, no WAL, the area durable. -/
def walBoot0St (r : GoString) : AbsDiskState := ⟨r, ∅, {[r := ()]}⟩

theorem walBoot0St_bounded (r : GoString) : WalsBounded (walBoot0St r) := by
  intro dir d hd; simp [walBoot0St] at hd

theorem walBoot0St_dirsRoots {R : Roots} {r : GoString} {jr : Ino} (hr : (r, jr) ∈ R) :
    DirsRoots R (walBoot0St r) := by
  intro dd hd
  by_cases hne : dd = r
  · subst hne; exact ⟨jr, hr⟩
  · simp [walBoot0St] at hd; exact absurd hd.symm hne

end pure

end WalFs
end EtcdGrove
end Perennial

end
