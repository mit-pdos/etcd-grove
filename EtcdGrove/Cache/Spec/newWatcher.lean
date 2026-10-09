/-
`newWatcher(bufSize, pred)`. Lean-first (no Rocq counterpart); see `InvWatcher.lean`.
-/
import EtcdGrove.Cache.InvWatcher

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newWatcher(bufSize, pred)`: an open watcher with nothing sent or received, for a
channel capacity `bufSize ≥ 0` (`make` panics on a negative one) and a `keyPred` closure `f`
implementing the filter `pred` (nil for `none`). -/
abbrev newWatcher.spec : Prop :=
  ∀ (bufSize : w64) (f : GoFunc) (pred : Option (GoString → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ⌜0 ≤ sint.Z bufSize⌝ ∗ keyPredOk f pred }}
    (App (App (Val (@! newWatcher)) (Val #bufSize)) (Val #f))
  {{ (w : Loc) (γ : WatcherNames), RET #w;
      isWatcher w γ pred ∗ watcherOpen γ [] ∗ watcherConsumer γ [] }}

end spec

end EtcdGrove
end Perennial
