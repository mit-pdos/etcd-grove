/-
The trust boundary of `metrics.RecordEtcdEvent` (see its spec; T5-f, approved by etcd-grove-81 with D7).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom metrics.RecordEtcdEvent.wp_proof : metrics.RecordEtcdEvent.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
