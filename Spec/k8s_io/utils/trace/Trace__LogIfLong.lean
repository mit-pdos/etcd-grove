/-
`(*Trace).LogIfLong(threshold)`: the trust boundary (`k8s.io/utils/trace` is translated names only). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO, whose
slow-queue trace calls it).
-/
module

public import GeneratedProof.k8s_io.utils.trace

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.trace.Assumptions]

/-- `t.LogIfLong(threshold)`: returns (it may log). -/
abbrev trace.Trace.LogIfLong.spec : Prop :=
  ∀ (t : Loc) (d : w64),
  {{ (True : IProp GF) }}
    (App (Val (t @!! go.GoType.PointerType k8s_io.utils.trace.Trace.ty @!! go!"LogIfLong")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
