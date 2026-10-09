/-
`Cache.watchEvents(rev, applyErr, readyOnce)` (`cache/cache.go`): the demux's side of the watch
loop. Lean-first (no Rocq counterpart); see `InvCache.lean`, `InvEtcd.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache
public import Proof.go_etcd_io.etcd.cache.v3.Handoff

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.watchEvents(rev, applyErr, readyOnce)`, by the demux's writer (`cacheWriter`, state
`c0`, initialized by the caller's `Init(rev)`: the stream continues a watch at `rev - 1`,
`CursorOk`): it watches the prefix from `rev > 0` (`isEtcdWatcher`: the watch starts at
`rev - 1`) in a child context of the internal context (`context.WithCancel`, canceled on return)
and, for each response, sets `ready` once (`readyOnce.Do(c.ready.Set)`), returns `resp.Err()` if it
is not nil, and broadcasts it (`demux.Broadcast`) — certifying its batches (`respCert`: etcd's
steps from the watch, chained from the stream's last batch through the writer's knowledge
`TailOk`) — until the internal context is done (its error), the watch channel is closed (`nil`),
`Broadcast` fails, or something arrives on `applyErr` (that error); `ready` is reset in the last
three cases.

`applyErr` is a handoff channel (`isHandoff`: values `P v` and `Ws` handed over with a send, `Wc`
with a close that follows none) of which the caller is the consumer and has taken nothing. The
writer's state afterwards is again a `cacheWriter` whose stream continues the watch at
`rev - 1`; and the consumer has still taken nothing, or has taken what `applyErr` handed over: the
value it returns and `P` of it with `Ws`, or (the close) `nil` with `Wc`. -/
abbrev Cache.watchEvents.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (rev : w64) (aec : Loc) (γa : HandoffNames) (P : GoError → IProp GF) (Ws Wc : IProp GF)
    (ro : Loc) (c0 : DemuxCore),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗
      isHandoff γa aec P Ws Wc ∗ handoffConsumer γa false ∗
      sync.isOnce ro iprop(True) iprop(True) ∗
      cacheWriter cf γd cap c0 ∗ ⌜0 < sint.Z rev ∧ CursorOk cf.pfx c0 (rev - W64 1)⌝ }}
    (App (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"watchEvents")) (Val #rev))
      (Val #aec)) (Val #ro))
  {{ (err : GoInterface), RET #err; ∃ c1 : DemuxCore, cacheWriter cf γd cap c1 ∗
      ⌜CursorOk cf.pfx c1 (rev - W64 1)⌝ ∗
      (handoffConsumer γa false ∨
        (handoffConsumer γa true ∗ ((P err ∗ Ws) ∨ (⌜err = GoInterface.nil⌝ ∗ Wc)))) }}

end spec

end EtcdGrove
end Perennial
