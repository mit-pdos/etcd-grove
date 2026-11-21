/- Looking up the term of an index in a Ready batch's immutable replay log. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev replayTerms.termAt.spec : Prop :=
  ∀ (r : GoSlice) (runs : List replayTermRun) (index : w64) (j : Nat) (run : replayTermRun),
  runs[j]? = some run → uint.nat index ≤ uint.nat run.last' →
  (∀ i < j, ∀ earlier, runs[i]? = some earlier → uint.nat earlier.last' < uint.nat index) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ r ↦*□ runs }}
    (App (Val (r @!! replayTerms.ty @!! go!"termAt")) (Val #index))
  {{ RET #run.term'; True }}

end EtcdGrove
end Perennial
