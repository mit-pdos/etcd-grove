/-
Lean-first (no Rocq counterpart).

# The driver's `Obj.SetResourceVersion`, as a function (k8s 7g step 3)

`setRVL s old`: the resource version `(*Obj).SetResourceVersion(s)` leaves in an object whose
version was `old` (`k8setcd3.go`): `0` for `""`, the decimal value of `s` if `strconv.ParseUint(s,
10, 64)` accepts it, `old` otherwise. On `strconv.FormatUint(n, 10)` (`decStr n`), the form the
maintainers' checker's `Model` writes, it is `n` (`setRVL_decStr`, through
`parseUint_decStr`: `ParseUint` reads back what `FormatUint` writes).
-/
module

public import Proof.strconv.FormatUintDefs
public import Perennial.Proof.internal.strconv.ParseUintBasics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open internal.strconv

/-- **`(*Obj).SetResourceVersion(s)`'s resource version** on one that was `old`. -/
def setRVL (s : GoString) (old : w64) : w64 :=
  if s = [] then 0 else
    match parseUint s 10 64 with
    | .ok n => W64 n
    | _ => old

theorem digitVal_digitChar (d : Nat) (h : d < 10) : digitVal (digitChar d) = some d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `ParseUint`'s loop reads `FormatUint`'s decimal digits of a value up to the maximum. -/
theorem parseDigits_baseDigits (M : Nat) :
    ∀ n, n ≤ M → parseDigits 10 M ((baseDigits 10 (by omega) n).map digitChar) 0 = .ok n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rw [baseDigits]
    split
    · next h =>
      simp only [List.map_cons, List.map_nil]
      rw [parseDigits_cons_ok (digitVal_digitChar n h) h (by omega)]
      simp [parseDigits]
    · next h =>
      rw [List.map_append, parseDigits_append_ok,
        ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) (by omega)]
      simp only [List.map_cons, List.map_nil]
      have hm : n % 10 < 10 := Nat.mod_lt n (by omega)
      have he : n / 10 * 10 + n % 10 = n := by omega
      rw [parseDigits_cons_ok (digitVal_digitChar _ hm) hm (by omega), he]
      rfl

/-- **`ParseUint(FormatUint(n, 10), 10, 64)` is `n`.** -/
theorem parseUint_decStr (n : w64) : parseUint (decStr n) 10 64 = .ok n.toNat := by
  rw [parseUint_of_ne (decStr_ne_nil n), decStr_eq]
  apply parseDigits_baseDigits
  have := n.isLt
  rw [show effBitSize 64 = 64 from rfl]
  omega

/-- **`SetResourceVersion(FormatUint(n, 10))` sets `n`.** -/
theorem setRVL_decStr (n old : w64) : setRVL (decStr n) old = n := by
  unfold setRVL
  rw [if_neg (decStr_ne_nil n), parseUint_decStr]
  simp

end k8s_etcd3
end EtcdGrove
end Perennial
