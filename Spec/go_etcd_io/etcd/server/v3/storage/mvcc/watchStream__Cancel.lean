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

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `st.Cancel(id)`, by what the caller knows of `id` (`by`):
* `live`: it holds the watcher's live token; the watcher is cancelled for good (`wsCanceled`, no
  longer covered by the stream's progress);
* `unknown`: the id is not in its registrar's view (lent, given back): no watcher has it (the
  stream never reuses an id, `nextID` only grows), nothing changes;
* `dead`: the watcher was cancelled already; nothing changes.
v3rpc's receive loop, the registrar, cancels each id its client sends in one of the three ways.
`nil` or `ErrWatcherNotExist`. (Round 2 cancelled without anything, so a watcher whose live token
another holder kept could be cancelled, falsifying the stream's progress law; round 3 merged the
last two cases, so a caller could lose its view: round 4.) -/
abbrev mvcc.watchStream.Cancel.specC : Prop :=
  ∀ (st : Loc) (γ : mvcc.MvccName) (ι : mvcc.WsName) (id : w64) (by_ : mvcc.CancelBy) (S : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isMvccWatchStream st γ ι ∗ threadTok ∗
      (match by_ with
       | .live => mvcc.wsLive ι id
       | .unknown => iprop(mvcc.wsWatchers ι S ∗ ⌜id ∉ S⌝)
       | .dead => mvcc.wsCanceled ι id) }}
    (App (Val (st @!! go.GoType.PointerType watchStream.ty @!! go!"Cancel")) (Val #id))
  {{ (err : GoInterface), RET #err; threadTok ∗
      (match by_ with
       | .live => mvcc.wsCanceled ι id
       | .unknown => mvcc.wsWatchers ι S
       | .dead => iprop(True)) ∗
      (⌜err = GoInterface.nil⌝ ∨ globalAddr ErrWatcherNotExist ↦□ err) }}

end spec

end EtcdGrove
end Perennial
