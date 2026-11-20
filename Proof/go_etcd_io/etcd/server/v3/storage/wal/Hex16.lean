/- Lean-first (no Rocq counterpart).

# `%016x` (pure)

Go's `fmt.Sprintf("%016x", n)` of a `uint64`, as bytes: the WAL's segment names (`walFileName`,
`Abs.lean`) and the snapshotter's database snapshot names (`snap.snapDBName`,
`etcdserver/api/snap/Defs.lean`). Moved out of `Abs.lean` and `CutName.lean` (wal-link, 2026-11-19;
names and statements unchanged) so that the snapshotter's vocabulary can name it without the WAL's
model.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

/-- A hex digit, lower case (`%x`). -/
def hexDigit (n : Nat) : w8 := if n < 10 then BitVec.ofNat 8 (48 + n) else BitVec.ofNat 8 (87 + n)

/-- `%016x` of `n` (`n < 2^64`). -/
def hex16 (n : Nat) : GoString := ((List.range 16).reverse).map (fun i => hexDigit (n / 16 ^ i % 16))

/-- No hexadecimal digit is `/`. -/
theorem hexDigit_ne_slash : ∀ k : Fin 16, hexDigit k.val ≠ (47 : w8) := by decide

theorem hex16_ne_slash (n : Nat) : ∀ c ∈ hex16 n, c ≠ (47 : w8) := by
  intro c hc
  unfold hex16 at hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact hexDigit_ne_slash ⟨_, Nat.mod_lt _ (by decide)⟩

theorem hexDigit_ne_nul : ∀ k : Fin 16, hexDigit k.val ≠ (0 : w8) := by decide

theorem hex16_ne_nul (n : Nat) : ∀ c ∈ hex16 n, c ≠ (0 : w8) := by
  intro c hc
  unfold hex16 at hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact hexDigit_ne_nul ⟨_, Nat.mod_lt _ (by decide)⟩

end WalFs
end EtcdGrove
end Perennial
