/-
`v.Infof(format, args...)` (names-only): logging, a no-op for the store's results. The trust boundary: an axiom, `Proof/k8s_io/klog/v2/Verbose__Infof.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

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

/-- See the file header. -/
abbrev klog.Verbose.Infof.spec : Prop :=
  ∀ (v : k8s_io.klog.v2.Verbose) (f : GoString) (args : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }}
    (App (App (Val (v @!! k8s_io.klog.v2.Verbose.ty @!! go!"Infof")) (Val #f)) (Val #args))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
