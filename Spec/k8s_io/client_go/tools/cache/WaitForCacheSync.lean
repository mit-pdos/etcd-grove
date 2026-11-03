/-
`cache.WaitForCacheSync(stopCh, cacheSyncs...)` (`shared_informer.go`): polls the
`InformerSynced` functions until all return `true` (`wait.PollImmediateUntil`) or `stopCh` is
closed: `true` only once every function returned `true` (each `syncedFn`'s facts). Lean-first; the
DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`WaitForCacheSync(stopCh, fs...)`**: see the file header. -/
abbrev WaitForCacheSync.spec : Prop :=
  ∀ (ch : GoChan) (sl : GoSlice) (dq : DFrac) (fs : List GoFunc) (γis : List InfNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ sl ↦*{dq} fs ∗ ⌜fs.length = γis.length⌝ ∗
      [∗list] f;γi ∈ fs;γis, syncedFn f γi }}
    (App (App (Val (@! WaitForCacheSync)) (Val #ch)) (Val #sl))
  {{ (b : Bool), RET #b; sl ↦*{dq} fs ∗ (if b then [∗list] γi ∈ γis, syncedFacts γi true
      else iprop(True)) }}

end spec

end cache
end EtcdGrove
end Perennial
