/-
Lean-first (no Rocq counterpart).

# lintest/perclient: the specs' vocabulary (2026-11-22)

`applySpecId S inOk libState Eapp clients f`: lintest's `applySpec` (`lintest/Defs.lean`) for a
library `f` that is told which client calls it: `f(id, i)`, for a client index `0 ≤ id < clients`,
is logically atomic against `S.M` over `libState`, lent the calling goroutine's thread token. Every
other part of `perclient.Run`'s specs is lintest's (`clockSpec`, `genSpec`, `linInv`, `clientTok`).
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

/-- A library operation told its client's index (see the file header). -/
def applySpecId (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF) (libState : σ → IProp GF)
    (Eapp : CoPset) (clients : w64) (f : GoFunc) : IProp GF :=
  iprop(∀ (id : w64) (i : GoInterface),
    {{ ⌜0 ≤ sint.Z id ∧ sint.Z id < sint.Z clients⌝ ∗ inOk i ∗ threadTok }}
      <<{ ∀∀ s, libState s }>> (App (App (Val #f) (Val #id)) (Val #i)) @@ Eapp
    <<{ ∃∃ s' o, libState s' ∗ ⌜S.M.step s (i, o) = some s'⌝ }>>
    {{ (o' : GoInterface), RET #o'; ⌜∀ s, S.M.step s (i, o') = S.M.step s (i, o)⌝ ∗
        S.ioOk i o' ∗ threadTok }})

instance applySpecId_persistent (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF)
    (libState : σ → IProp GF) (Eapp : CoPset) (clients : w64) (f : GoFunc) :
    Persistent (applySpecId S inOk libState Eapp clients f) := by
  unfold applySpecId; infer_instance

end defs

end perclient
end EtcdGrove
end Perennial
