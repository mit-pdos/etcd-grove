/-
`watchStream.RequestProgress` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
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

/-- **`ws.RequestProgress(id)`**: asks the store for the progress of `id`'s watcher, if any. -/
abbrev mvcc.watchStream.RequestProgress.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : mvcc.WsStreamNames) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchStream ws wa P γ ∗ P.R }}
    (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"RequestProgress")) (Val #id))
  {{ RET #(); P.R }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `st.RequestProgress(id)`: asks for the progress of `id`'s watcher (a response without
events, if it is synced: `wsRecv_progress`). -/
abbrev mvcc.watchStream.RequestProgress.specC : Prop :=
  ∀ (st : Loc) (γ : mvcc.MvccName) (ι : mvcc.WsName) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isMvccWatchStream st γ ι ∗ threadTok }}
    (App (Val (st @!! go.GoType.PointerType watchStream.ty @!! go!"RequestProgress")) (Val #id))
  {{ RET #(); threadTok }}

end spec

end EtcdGrove
end Perennial
