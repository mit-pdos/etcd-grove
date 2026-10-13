/-
`newWatcher(bufSize, pred)`. Lean-first (no Rocq counterpart); see `InvWatcher.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvWatcher

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newWatcher(bufSize, pred)`: an open watcher with nothing sent or received, for a
channel capacity `0 ≤ bufSize < 2^32` (`make` panics on a negative one; Perennial's
`make(chan T, n)` is defined below `2^32`) and a `keyPred` closure `f`
implementing the filter `pred` (nil for `none`), publishing `Pb` (the caller's choice; it must
hold of the empty log); and it is fresh (`watcherUnique`). -/
abbrev newWatcher.spec : Prop :=
  ∀ (bufSize : w64) (f : GoFunc) (pred : Option (GoString → Bool)) (Pb : WatcherPub GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ⌜0 ≤ sint.Z bufSize ∧ sint.Z bufSize < 2 ^ 32⌝ ∗ keyPredOk f pred ∗ □ Pb.pub none [] }}
    (App (App (Val (@! newWatcher)) (Val #bufSize)) (Val #f))
  {{ (w : Loc) (γ : WatcherNames), RET #w;
      isWatcher w γ pred Pb ∗ watcherOpen γ [] ∗ watcherConsumer γ [] ∗ watcherUnique w }}

end spec

end EtcdGrove
end Perennial
