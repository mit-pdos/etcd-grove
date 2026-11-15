/-
The trust boundary of `metrics.RecordStorageListMetrics` (see its spec).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordStorageListMetrics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom metrics.RecordStorageListMetrics.wp_proof : metrics.RecordStorageListMetrics.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
