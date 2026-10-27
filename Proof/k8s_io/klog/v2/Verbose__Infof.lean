/-
The trust boundary of `klog.Verbose.Infof` (see its spec).
-/
module

public import Spec.k8s_io.klog.v2.Verbose__Infof

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
axiom klog.Verbose.Infof.wp_proof : klog.Verbose.Infof.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
