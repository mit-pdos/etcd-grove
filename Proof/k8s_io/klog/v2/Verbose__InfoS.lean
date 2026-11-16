/-
The trust boundary of `klog.Verbose.InfoS` (see its spec; T5-g, decided by etcd-grove-81 2026-11-15:
an axiom at k8s 7f-5a-P step 7, with the Go test `examples/premisefix/watcherctx/infos_test.go`).
-/
module

public import Spec.k8s_io.klog.v2.Verbose__InfoS

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
axiom klog.Verbose.InfoS.wp_proof : klog.Verbose.InfoS.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
