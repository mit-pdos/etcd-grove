/- Lean-first (no Rocq counterpart).

`Model()` (counter.go): the counter's porcupine model, as `counterS` specifies it
(`Proof/.../lintest/counter/Defs.lean`): `Partition`, `StepContext` and `Hash` are `nil`,
`Init`, `Step` and `Equal` are the closures of the model.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.Model)) (Val #()))
  {{ (m : Model), RET #m; isModel (counterS (GF := GF)) m }}

end spec

end counter
end lintest
end EtcdGrove
end Perennial
