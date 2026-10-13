/-
`watchableStore.NewWatchStream` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`, `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `s.NewWatchStream()`: a fresh stream (`isWatchStream`) over the store as its `watchable`
(`storeWatchParams`), open (`watchStreamOpen`, for its one `Close`), with a fresh channel of
`chanBufLen` responses, its invariant (`watchChanInv`, no response sent) and the consumer's view
(`watchConsumer`, nothing received). -/
abbrev mvcc.watchableStore.NewWatchStream.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"NewWatchStream")) (Val #()))
  {{ (ws : Loc), RET #(interface.mkOk (go.GoType.PointerType watchStream.ty) #ws);
      ∃ (γo : GName) (ch : Loc) (γc : mvcc.WatchChanNames),
        mvcc.isWatchStream ws (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
          (mvcc.storeWatchParams s st γ) γo ∗
        ws.[watchStream, go!"ch"] ↦□ ch ∗ isChan ch γc.ch WatchResponse ∗
        inv mvcc.watchN (mvcc.watchChanInv γ ch γc) ∗
        mvcc.watchStreamOpen γo ∗ mvcc.watchConsumer γc [] }}

end spec

end EtcdGrove
end Perennial
