/- Lean-first (no Rocq counterpart).

# `Create`'s commit points, pure part (W4, `notes/wal-fsext-plan.md`, "W4 implementation log")

* `regionCrashed_mono`: a crash a bigger commit bound allows is one a smaller allows.
* `LastWrite h j b x e E`: the claim's last logged entry writing the name `b` of `j` is `x`, after
  which its names were `E`; `regionCrashed_lastWrite`: once `x` is below the commit bound, every crash
  the claims allow leaves `b` as `E` has it (`RegionCrashed`'s `K` holds `x`, the last writer).
* `crashOk_named`: the WAL's crash condition with `named` raised, once its name's last writer (the
  rename onto it, holding the WAL's directory) is committed: the parent's fsync after `Create`'s
  rename, the step to `walNamed`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Abs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- A crash a bigger commit bound allows is one a smaller allows. -/
theorem regionCrashed_mono {cl : List Claim} {n n' : Nat} {m' : Tree} (hn : n ≤ n')
    (h : RegionCrashed cl n' m') : RegionCrashed cl n m' := by
  obtain ⟨K, h1, h2, h3⟩ := h
  exact ⟨K, h1, fun c hc y e E hy hlt => h2 c hc y e E hy (Nat.lt_of_lt_of_le hlt hn), h3⟩

open Classical in
/-- **The claim's last entry writing the name `b` of `j`** is `x` (the entry `e`), after which the
claim's names were `E`. -/
def LastWrite (h : NamesH) (j : Ino) (b : GoString) (x : Nat) (e : LogEntry) (E : Ents) : Prop :=
  (h.ents.filter (fun xe => decide (xe.2.1.op.Writes j b))).getLast? = some (x, e, E)

theorem filter_getLast_and {α : Type} (l : List α) (p q : α → Bool) (a : α)
    (h : (l.filter p).getLast? = some a) (hq : q a = true) :
    (l.filter (fun x => q x && p x)).getLast? = some a := by
  have hf : l.filter (fun x => q x && p x) = (l.filter p).filter q := by
    rw [List.filter_filter]
  rw [hf]
  obtain ⟨l', hl⟩ := List.getLast?_eq_some_iff.1 h
  rw [hl, List.filter_append]
  simp [hq]

open Classical in
/-- **A committed last writer decides its name in every crash.** -/
theorem regionCrashed_lastWrite {cl : List Claim} {n : Nat} {m' : Tree} {j : Ino} {N : NameSet}
    {h : NamesH} {b : GoString} {x : Nat} {e : LogEntry} {E : Ents} (hc : (j, N, h) ∈ cl)
    (hb : N.Mem b) (hl : LastWrite h j b x e E) (hx : x < n) (hr : RegionCrashed cl n m') :
    m'.entry j b = E !! b := by
  obtain ⟨K, -, h2, h3⟩ := hr
  have hmem : (x, e, E) ∈ h.ents := by
    have := List.mem_of_getLast? hl
    exact (List.mem_filter.1 this).1
  have hK : K x := h2 _ hc x e E hmem hx
  rw [h3 _ hc b hb]
  show NamesH.valAfter h j K b = E !! b
  unfold NamesH.valAfter
  have := filter_getLast_and h.ents (fun xe => decide (xe.2.1.op.Writes j b))
    (fun xe => decide (K xe.1)) (x, e, E) hl (by simpa using hK)
  have heq : (fun xe : Nat × LogEntry × Ents => decide (K xe.1) && decide (xe.2.1.op.Writes j b)) =
      (fun xe => decide (K xe.1 ∧ xe.2.1.op.Writes j b)) := by
    funext xe; simp
  rw [heq] at this
  rw [this]

/-- The intended bytes and records do not depend on `named`. -/
theorem segStream_named (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (k : Nat)
    (b : Bool) : segStream C Mr { d with named := b } cuts k = segStream C Mr d cuts k := rfl

/-- **The crash condition with `named` raised**, the WAL's name `lay.nm` decided, in every crash the
claims allow with the commit bound `n`, as the directory `J` (its last writer committed). -/
theorem crashOk_named (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (cl : List Claim)
    (n0 n : Nat) (hn : n0 ≤ n) (hok : CrashOk C Mr d lay cl n0)
    (hname : ∀ m', RegionCrashed cl n m' → ∃ J, m'.entry lay.jr lay.nm = some (.dir J)) :
    CrashOk C Mr { d with named := true } lay cl n := by
  intro m' fo hr hf hnm hw1
  rcases hok m' fo (regionCrashed_mono hn hr) hf hnm hw1 with ⟨-, hnone⟩ | hright
  · obtain ⟨J, hJ⟩ := hname m' hr
    rw [hnone] at hJ; cases hJ
  · exact Or.inr hright

/-- `crashOk_named`'s premise from a committed last writer of the name, in a claim of the WAL's
directory. -/
theorem crashOk_named_of_lastWrite (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay)
    (cl : List Claim) (n0 n : Nat) (hn : n0 ≤ n) (hok : CrashOk C Mr d lay cl n0) {N : NameSet}
    {h : NamesH} {x : Nat} {e : LogEntry} {E : Ents} {J : Ino} (hc : (lay.jr, N, h) ∈ cl)
    (hb : N.Mem lay.nm) (hl : LastWrite h lay.jr lay.nm x e E) (hx : x < n)
    (hE : E !! lay.nm = some (.dir J)) :
    CrashOk C Mr { d with named := true } lay cl n :=
  crashOk_named C Mr d lay cl n0 n hn hok fun m' hr =>
    ⟨J, by rw [regionCrashed_lastWrite hc hb hl hx hr, hE]⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
