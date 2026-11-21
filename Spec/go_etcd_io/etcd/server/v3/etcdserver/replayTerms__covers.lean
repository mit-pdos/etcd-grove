/- Checking the bounds in a Ready batch's immutable replay log. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayLookup

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev replayTerms.covers.spec : Prop :=
  ∀ (r : GoSlice) (runs : List replayTermRun) (index : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ r ↦*□ runs }}
    (App (Val (r @!! replayTerms.ty @!! go!"covers")) (Val #index))
  {{ RET #(replayRunCovers runs index); True }}

end EtcdGrove
end Perennial
