/-
Ported from dsverify-lab examples/gryff/proof/Harness/ModelsCas.lean (run gryff-bump-1, lab master 915f964;
notes/dsv-gryff.md): the pure model only (`casRegister`, `casApply`); the lab's Go model and
its porcupine wiring are replaced by the kit's model (`examples/gryffnet/kit.go`'s `Model`).

The register with read, write and a compare-and-swap whose reply does not say whether it swapped.
-/
module

public import Dsverify.Proof.gryff.Lab.Model
public import Perennial.Std.Word

@[expose] public section

noncomputable section

namespace Perennial

namespace dsverify_lab.harness

/-! ## The model -/

/-- The register with read, write and a compare-and-swap whose reply does not say whether it
swapped (Gryff's RMW reply; kits/gryff-net), from `v0`: as `register`, but a compare-and-swap's
output is `.done`. -/
def casRegister (V : Type) [DecidableEq V] (v0 : V) : Model where
  State := V
  Input := RegInput V
  Output := RegOutput V
  init := v0
  step s i s' o := match i with
    | .read => s' = s ∧ o = .value s
    | .write v => s' = v ∧ o = .done
    | .cas a b => s' = (if s = a then b else s) ∧ o = .done

/-! ## The porcupine model, pure -/

/-- The step as a function: the next state and the output. -/
def casApply (s : w64) : RegInput w64 → w64 × RegOutput w64
  | .read => (s, .value s)
  | .write v => (v, .done)
  | .cas a b => (if s = a then b else s, .done)

theorem casRegister_step_iff (v0 s : w64) (i : RegInput w64) (s' : w64) (o : RegOutput w64) :
    (casRegister w64 v0).step s i s' o ↔ casApply s i = (s', o) := by
  cases i with
  | read => simp [casRegister, casApply, eq_comm]
  | write v => simp [casRegister, casApply, eq_comm]
  | cas a b => simp [casRegister, casApply, eq_comm]

end dsverify_lab.harness

end Perennial
