/-
`watchableStore.addVictim` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.addVictim(victim)` under `s.mu`: a non-empty batch map is appended to `s.victims` and the
victims' loop woken (a non-blocking send on `victimc`); an empty one changes nothing. -/
abbrev mvcc.watchableStore.addVictim.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (vs : GoSlice) (vbs : List GoMap) (wb : GoMap) (dq : DFrac)
    (Mw : GMap Loc Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ typedPointsto (mvcc.victimsAddr s) vs (DFrac.own 1) ∗
      vs ↦* vbs ∗ ownSliceCap GoMap vs (DFrac.own 1) ∗ ownMap wb dq Mw }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"addVictim")) (Val #wb))
  {{ RET #(); ownMap wb dq Mw ∗ ∃ vs' : GoSlice, typedPointsto (mvcc.victimsAddr s) vs' (DFrac.own 1) ∗
      vs' ↦* (if Mw.size = 0 then vbs else vbs ++ [wb]) ∗ ownSliceCap GoMap vs' (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
