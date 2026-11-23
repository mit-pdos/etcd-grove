/-
`strconv.Atoi`'s value on QuePaxa's numbers (a spec, not a hypothesis: proved over Perennial's
translation of `strconv`/`internal/strconv` in `AtoiProof.lean`): for a string of 1 to 18
decimal digits, `Atoi(s)` returns its value (`decVal s`) and a `nil` error. Perennial's own
`strconv.Atoi.spec` does not give the value; QuePaxa's peer names and addresses need it.
The class `AtoiSpec` carries it to the proofs that call `Atoi` (which see it as a spec, per the
import tiers); its instance `atoiSpec_inst` is in `AtoiProof.lean`, which the `Results` modules
import, so it is no premise of the results.
-/
module

public import Perennial.Proof.strconv.Base
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos.hyp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strconv

/-- The value of a string of decimal digits. -/
def decVal (s : List w8) : Nat := s.foldl (fun acc b => acc * 10 + (b.toNat - 48)) 0

/-- `s` is a non-empty string of at most 18 decimal digits. -/
def smallDigits (s : List w8) : Prop :=
  1 ≤ s.length ∧ s.length ≤ 18 ∧ ∀ b ∈ s, 48 ≤ b.toNat ∧ b.toNat ≤ 57

section atoi
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `strconv.Atoi(s)` for a string of 1 to 18 decimal digits: its value and a `nil` error (the
lab's `wp_Atoi`; proved by `hyp.strconv.Atoi.wp_proof`, `AtoiProof.lean`, over `internal/strconv`'s
fast path). -/
abbrev Atoi.spec : Prop :=
  ∀ (s : GoString), smallDigits s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! Perennial.strconv.Atoi)) (Val #s))
    {{ RET (PairV #(W64 (decVal s)) #GoInterface.nil); True }}

end atoi

end strconv

/-- `strconv.Atoi`'s value spec, for the proofs that call it (proved: its instance is
`atoiSpec_inst`, `AtoiProof.lean`). -/
class AtoiSpec [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Atoi : strconv.Atoi.spec (GF := GF) (hG := hG)

end Perennial.raxos.hyp
