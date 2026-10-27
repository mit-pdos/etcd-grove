/-
`klog.Background()` (names-only: the trust boundary): some logger. Lean-first; for client-go's
delaying queue.
-/
module

public import Proof.k8s_io.klog.v2.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `klog.Background()`: some `Logger`. -/
abbrev klog.Background.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }}
    (App (Val (@! k8s_io.klog.v2.Background)) (Val #()))
  {{ (l : github_com.go_logr.logr.Logger), RET #l; True }}

end spec

end EtcdGrove
end Perennial
