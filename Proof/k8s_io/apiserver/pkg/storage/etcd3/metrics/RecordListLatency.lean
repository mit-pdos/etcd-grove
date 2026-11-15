/-
The trust boundary of `metrics.RecordListLatency` (see its spec).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordListLatency

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

axiom metrics.RecordListLatency.wp_proof : metrics.RecordListLatency.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
