/-
`cache.WaitForNamedCacheSyncWithContext(ctx, cacheSyncs...)` (`shared_informer.go`): logs, then
`WaitForCacheSync(ctx.Done(), cacheSyncs...)`: **`true` only once every informer has synced**: for
each, the first list's version `v` and the store's version at least `v` for good
(`syncedFacts γi true`: `infFirst γi v ∗ infRvLb γi v`, which a later store read turns into "the
store is the server's table at a version at least the first list's", `infInv_readLbAU`); `false`
(the context done) with nothing. Lean-first; the DaemonSet run's track A.
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

/-- **`WaitForNamedCacheSyncWithContext(ctx, fs...)`**: see the file header. -/
abbrev WaitForNamedCacheSyncWithContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (sl : GoSlice) (dq : DFrac)
    (fs : List GoFunc) (γis : List InfNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ context.isContext ctx cs ∗ sl ↦*{dq} fs ∗ ⌜fs.length = γis.length⌝ ∗
      [∗list] f;γi ∈ fs;γis, syncedFn f γi }}
    (App (App (Val (@! WaitForNamedCacheSyncWithContext)) (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (b : Bool), RET #b; sl ↦*{dq} fs ∗ (if b then [∗list] γi ∈ γis, syncedFacts γi true
      else iprop(True)) }}

end spec

end cache
end EtcdGrove
end Perennial
