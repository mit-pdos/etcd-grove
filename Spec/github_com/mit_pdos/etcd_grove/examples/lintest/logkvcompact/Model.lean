/- Lean-first (no Rocq counterpart).

`Model()` (logkvcompact.go): the register's porcupine model, as `regS` specifies it
(`Proof/.../lintest/logkvcompact/Defs.lean`): `Partition`, `StepContext` and `Hash` are `nil`,
`Init`, `Step` and `Equal` are the closures of the model.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvcompact

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Model)) (Val #()))
  {{ (m : Model), RET #m; isModel (regS (GF := GF)) m }}

end spec

end logkvcompact
end lintest
end EtcdGrove
end Perennial
