/-
`watcher.Compact(compactRev)`. Lean-first (no Rocq counterpart); see `InvWatcher.lean`.
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

/-- `w.Compact(compactRev)`: closed afterwards; with cancel `some compactRev` (`cancelResp`
the compaction response, `cancelModel`) if this call closed it (it was open), the earlier one
otherwise. -/
abbrev watcher.Compact.spec : Prop :=
  ∀ (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool)) (Pb : WatcherPub GF)
    (sent : List RespModel) (ph : WatcherPhase) (compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isWatcher w γ pred Pb ∗ watcherAt γ sent ph ∗
      watcherClosePub Pb sent (some compactRev) ph }}
    (App (Val (w @!! go.GoType.PointerType watcher.ty @!! go!"Compact")) (Val #compactRev))
  {{ RET #(); watcherClosed γ sent (ph.cancelAfter (some compactRev)) }}

end spec

end EtcdGrove
end Perennial
