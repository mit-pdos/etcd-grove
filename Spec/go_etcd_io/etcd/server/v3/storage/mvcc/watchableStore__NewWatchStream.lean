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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.NewWatchStream()`: a fresh stream (`isWatchStream`) over the store as its `watchable`
(`storeWatchParams`), open (`watchStreamOpen`, for its one `Close`), with a fresh channel of
names `γc` (its invariant, the consumer's view at nothing received). Unit W-M2: the stream's id
map and progress fact are the channel's (`γo.ids = γc.ids`, `γo.prog = γc.prog`), and the
progress fact is the caller's `Q` (saved at `γo.prog`: a response of id `-1` on the channel
carries `progFact γc.prog`, so `Q`). Unit W-K: the channel is buffered (`0 < γc.ch.chanCap`), and
its sent list is named through the stream (`γo.sentl = γc.sentl`). K1b: the cancellation reason
is the caller's `Ψ` (saved at `γo.rsn = γc.rsn`: `Cancel id` takes `rsnFor γo.rsn id`). -/
abbrev mvcc.watchableStore.NewWatchStream.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (Q : IProp GF) (Ψ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"NewWatchStream")) (Val #()))
  {{ (ws : Loc), RET #(interface.mkOk (go.GoType.PointerType watchStream.ty) #ws);
      ∃ (γo : mvcc.WsStreamNames) (ch : Loc) (γc : mvcc.WatchChanNames),
        mvcc.isWatchStream ws (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
          (mvcc.storeWatchParams s st γ) γo ∗
        ws.[watchStream, go!"ch"] ↦□ ch ∗ isChan ch γc.ch WatchResponse ∗
        inv mvcc.watchN (mvcc.watchChanInv γ ch γc) ∗
        mvcc.watchStreamOpen γo ∗ mvcc.watchConsumer γc [] ∗
        ⌜γo.ids = γc.ids ∧ γo.prog = γc.prog ∧ γo.sentl = γc.sentl ∧ γo.rsn = γc.rsn ∧
          γo.regi = γc.regi ∧ 0 < sint.Z γc.ch.chanCap⌝ ∗ savedPropOwn γo.prog DFrac.discard Q ∗
        savedPredOwn γo.rsn DFrac.discard Ψ }}

end spec

end EtcdGrove
end Perennial
