/-
Proof of `Spec/Cache__watch.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the demux's writer at a state `cc` whose stream continues the watch at
`rev - 1` (`CursorOk`, from `Init(rev)`: `initCore_ok`), and the store's writer at a synced state
whose latest map is etcd's state at `Y`, with `rev ≤ Y + 1` and `Y` at most the latest revision.
Each iteration's `applyErr` is a handoff channel (`Handoff.lean`): the goroutine sends
`applyStorage`'s error with the store's writer (`watchWs`), or closes it with the writer and its
certificate (`watchWc`); the loop takes them at its first receive, in `watchEvents` or in the
wait. It continues only after `nil` from both, so with `watchWc`.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__watch
public import Spec.go_etcd_io.etcd.cache.v3.demux__Init
public import Spec.go_etcd_io.etcd.cache.v3.newWatcher
public import Spec.go_etcd_io.etcd.cache.v3.demux__Register
public import Spec.go_etcd_io.etcd.cache.v3.demux__Unregister
public import Spec.go_etcd_io.etcd.cache.v3.Cache__applyStorage
public import Spec.go_etcd_io.etcd.cache.v3.Cache__watchEvents

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.watch.wp_proof
    (wp_Init : demux.Init.spec (GF := GF) (hG := hG))
    (wp_newWatcher : newWatcher.spec (GF := GF) (hG := hG))
    (wp_Register : demux.Register.spec (GF := GF) (hG := hG))
    (wp_applyStorage : Cache.applyStorage.spec (GF := GF) (hG := hG))
    (wp_watchEvents : Cache.watchEvents.spec (GF := GF) (hG := hG))
    (wp_Unregister : demux.Unregister.spec (GF := GF) (hG := hG)) :
    Cache.watch.spec (GF := GF) (hG := hG) := by
  -- The shipped `watch` does not wait for an iteration's `applyStorage` goroutine: the store has
  -- shared writers, which the next commits' store specs support; until then, not proved.
  sorry

end proof

end EtcdGrove
end Perennial
