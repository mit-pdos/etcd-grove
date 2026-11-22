/-
`Model()` (counter.go): the counter's porcupine model with pending increments, as `cS`
specifies it (`Net/Proof/.../lib/remote/counter/ModelDefs.lean`): `Partition`, `StepContext` and
`Hash` are `nil`, `Init`, `Step` and `Equal` are the closures of the model. Proved in
`Net/Proof/.../lib/remote/counter/Model.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net github_com.anishathalye.porcupine

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Model)) (Val #()))
  {{ (m : github_com.anishathalye.porcupine.Model), RET #m; isModel (cS (GF := GF)) m }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
