/- Lean-first (no Rocq counterpart).

`Model()` (check.go): the store's porcupine model, as `kvS` specifies it (`ModelDefs.lean`):
`Partition` and `StepContext` are `nil`; `Init`, `Step`, `Equal` and `Hash` are the closures of
the model.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.ModelDefs
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.Model)) (Val #()))
  {{ (m : Model), RET #m; isModel (kvS (GF := GF)) m }}

end spec

end kvwitness
end EtcdGrove
end Perennial
