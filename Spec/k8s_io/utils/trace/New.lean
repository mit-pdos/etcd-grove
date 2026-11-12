/-
`trace.New(name, fields...)`: the trust boundary (`k8s.io/utils/trace` is translated names only). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO, whose
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

/-- `trace.New(name, fields)`: some trace (a pointer). -/
abbrev trace.New.spec : Prop :=
  ∀ (name : GoString) (fields : GoSlice),
  {{ (True : IProp GF) }}
    (App (App (Val (@! k8s_io.utils.trace.New)) (Val #name)) (Val #fields))
  {{ (t : Loc), RET #t; True }}

end spec

end EtcdGrove
end Perennial
