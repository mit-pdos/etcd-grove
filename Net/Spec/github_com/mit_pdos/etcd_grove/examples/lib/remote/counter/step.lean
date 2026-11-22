/-
`step(s, incr, o)` (counter.go): the model's step on `State`s, as `stepG` computes it on Go's
`int64`s (no precondition: it never panics). Proved in `Net/Proof/.../lib/remote/counter/step.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- See the file header. -/
abbrev step.spec : Prop :=
  ∀ (s : State) (incr : Bool) (o : Out),
  {{ (True : IProp GF) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.step))
      (Val #s)) (Val #incr)) (Val #o))
  {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); ⌜(ok, s') = stepG s incr o⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
