/- Lean-first (no Rocq counterpart).

`Model()` (logkvsnap.go): the register's porcupine model, as `regS` specifies it
(`Proof/.../lintest/logkvsnap/Defs.lean`): `Partition`, `StepContext` and `Hash` are `nil`,
`Init`, `Step` and `Equal` are the closures of the model.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvsnap

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Model)) (Val #()))
  {{ (m : Model), RET #m; isModel (regS (GF := GF)) m }}

end spec

end logkvsnap
end lintest
end EtcdGrove
end Perennial
