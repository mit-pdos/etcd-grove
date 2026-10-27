/-
`watchStream.Chan` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream

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

/-- **`ws.Chan()`**: the stream's channel (receive-only), with the store's facts of it: the
channel in the stream's `ch` field (read-only for good). -/
abbrev mvcc.watchStream.Chan.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : mvcc.WsStreamNames),
  {{ mvcc.isWatchStream ws wa P γ }}
    (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"Chan")) (Val #()))
  {{ (ch : GoChan), RET #ch; P.C ch ∗ ws.[watchStream, go!"ch"] ↦□ ch }}

end spec

end EtcdGrove
end Perennial
