/- Lean-first (no Rocq counterpart).

`weightsFit(w)` (`examples/mvccfull/config.go`): whether the positive weights among the first six of
`w` add up to less than `2 ^ 63` (`readMixOk`'s last conjunct; the weights read only).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev weightsFit.spec : Prop :=
  ∀ (w : GoSlice) (ws : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      w ↦*{dq} ws }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.weightsFit)) (Val #w))
  {{ (b : Bool), RET #b; w ↦*{dq} ws ∗
      ⌜b = true → (((ws.map sint.Z).take 6).map (fun x => max 0 x)).sum < 2 ^ 63⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
