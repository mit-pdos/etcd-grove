/-
U4's infrastructure hypotheses (`notes/bbolt-proof-plan.md`; design §5): facts about code outside
bbolt that its error paths need and that no spec of this repository or of Perennial gives yet.
U4's proofs take them as hypotheses (as they take their callees' specs); each is discharged once
its infrastructure lands, and is no trust assumption until then (the linked results would have to
supply it).

- `errnoErrOk` (§5 item 5, D20′): a nonzero errno's `error` (`syscall.Errno`, boxed) is an error
  `fmt` formats by its `Error()`. `Errno`'s method set has `Error() string` and no `Format`
  (goose's `Errno.TypeAssumptions`); what is missing is `Errno.Error`'s spec (its body is not
  translated).
-/
module

public import Spec.fmt.ErrorOk
public import Proof.syscall.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section infra
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A nonzero errno's error is `fmtErrorOk`** (§5 item 5). -/
def errnoErrOk : Prop := ∀ e : w64, e ≠ 0 → ⊢ fmtErrorOk (GF := GF) (errnoErr e)

end infra

end bbolt
end EtcdGrove
end Perennial
