/-
`klog.V(level)` (names-only): some `Verbose`. The trust boundary: an axiom, `Proof/k8s_io/klog/v2/V.lean`. Lean-first (no Rocq
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev klog.V.spec : Prop :=
  ∀ (l : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }}
    (App (Val (@! k8s_io.klog.v2.V)) (Val #l))
  {{ (v : k8s_io.klog.v2.Verbose), RET #v; True }}

end spec

end EtcdGrove
end Perennial
