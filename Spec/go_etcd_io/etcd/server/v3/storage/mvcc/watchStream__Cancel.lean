/-
`watchStream.Cancel` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`ws.Cancel(id)`**: `nil` (the watcher of `id` cancelled) or `ErrWatcherNotExist` (no
watcher of that id, or the stream closed). Unit W-K (K1b): with the cancellation's reason for
`id` (`rsnFor`: the stream's creator's predicate), which the channel then has for the watcher
(a progress response of id `-1` covers every registered watcher not cancelled for its reason). -/
abbrev mvcc.watchStream.Cancel.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : mvcc.WsStreamNames) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchStream ws wa P γ ∗ mvcc.rsnFor γ.rsn id }}
    (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"Cancel")) (Val #id))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ globalAddr ErrWatcherNotExist ↦□ err }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `st.Cancel(id)`: by the caller's update at the registrar's view, the watcher `id` no
longer live (no change for an id never registered or already cancelled: the stream never reuses an
id); `nil` or `ErrWatcherNotExist`. Responses sent before may still arrive. -/
abbrev mvcc.watchStream.Cancel.specC : Prop :=
  ∀ (st : Loc) (γ : mvcc.MvccName) (ι : mvcc.WsName) (id : w64) (Q : List mvcc.WInfo → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isMvccWatchStream st γ ι ∗ threadTok ∗
      AU <{ ∃∃ (W : List mvcc.WInfo), mvcc.wsWatchers ι W }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.wsWatchers ι (W.modify (sint.nat id) (fun w => { w with live := false })), COMM Q W }> }}
    (App (Val (st @!! go.GoType.PointerType watchStream.ty @!! go!"Cancel")) (Val #id))
  {{ (err : GoInterface), RET #err; threadTok ∗ (∃ W : List mvcc.WInfo, Q W) ∗
      (⌜err = GoInterface.nil⌝ ∨ globalAddr ErrWatcherNotExist ↦□ err) }}

end spec

end EtcdGrove
end Perennial
