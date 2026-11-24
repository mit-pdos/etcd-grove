/-
Lean-first (no Rocq counterpart).

# lintest/perclient: the specs' vocabulary (2026-11-22)

`applySpecId S inOk libState Eapp clients P f`: lintest's `applySpec` (`lintest/Defs.lean`) for a
library `f` that is told which client calls it: `f(id, i)`, for a client index `0 ≤ id < clients`,
is logically atomic against `S.M` over `libState`, lent the calling goroutine's thread token, and
given one of client `id`'s per-call resources `P id` (a call budget: `remote`'s units). `calls P n`:
`n` of them, what each client starts with for its `ops` calls. Every other part of `perclient.Run`'s
specs is lintest's (`clockSpec`, `genSpec`, `linInv`, `clientTok`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace perclient

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open lintest

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {σ : Type}

/-- `n` calls' worth of the per-call resource `P`. -/
def calls (P : IProp GF) : Nat → IProp GF
  | 0 => iprop(True)
  | n + 1 => iprop(P ∗ calls P n)

theorem calls_succ (P : IProp GF) (n : Nat) : calls P (n + 1) = iprop(P ∗ calls P n) := rfl

/-- A library operation told its client's index (see the file header). -/
def applySpecId (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF) (libState : σ → IProp GF)
    (Eapp : CoPset) (clients : w64) (P : Nat → IProp GF) (f : GoFunc) : IProp GF :=
  iprop(∀ (id : w64) (i : GoInterface),
    {{ ⌜0 ≤ sint.Z id ∧ sint.Z id < sint.Z clients⌝ ∗ inOk i ∗ threadTok ∗ P (sint.nat id) }}
      <<{ ∀∀ s, libState s }>> (App (App (Val #f) (Val #id)) (Val #i)) @@ Eapp
    <<{ ∃∃ s' o, libState s' ∗ ⌜S.M.step s (i, o) = some s'⌝ }>>
    {{ (o' : GoInterface), RET #o'; ⌜∀ s, S.M.step s (i, o') = S.M.step s (i, o)⌝ ∗
        S.ioOk i o' ∗ threadTok }})

instance applySpecId_persistent (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF)
    (libState : σ → IProp GF) (Eapp : CoPset) (clients : w64) (P : Nat → IProp GF) (f : GoFunc) :
    Persistent (applySpecId S inOk libState Eapp clients P f) := by
  unfold applySpecId; infer_instance

end defs

end perclient
end EtcdGrove
end Perennial
