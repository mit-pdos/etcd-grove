/-
`Cache.watchEvents(rev, applyErr, readyOnce)` (`cache/cache.go`): the demux's side of the watch
loop. Lean-first (no Rocq counterpart); see `InvCache.lean`, `InvEtcd.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

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
`c0`): it watches the prefix from `rev > 0` (`isEtcdWatcher`: the watch starts at `rev - 1`) and,
for each response, initializes the demux at `rev` once (`readyOnce.Do(Init(rev); ready.Set())`,
the framed `Once`: the `Once`'s one-shot resource and the caller's half of `γo`, both
`false`, become the persistent `true`), returns `resp.Err()` if it is not nil, and broadcasts
it (`demux.Broadcast`) — certifying its batches (`respCert`: etcd's steps from the watch,
chained from the stream's last batch through the writer's knowledge `TailOk`) — until the
internal context is done (its error), the watch channel is closed (`nil`), `Broadcast` fails, or
something arrives on `applyErr` (that error); `ready` is reset in the last three cases.

The `Once` is armed (the caller's half of `γo` is `false`: `Init` has not run) or has run, the
stream then continuing the watch at `rev - 1` (`CursorOk`). The writer's state afterwards is
again a `cacheWriter`, and if the `Once` has run the stream still continues a watch from `rev`. -/
abbrev Cache.watchEvents.spec : Prop :=
  ∀ (c : Loc) (cf : CacheFields) (γr : ReadyNames) (γd : DemuxNames) (cap : Nat)
    (rev : w64) (aec : Loc) (γa : SpscNames) (Pa : Int → GoError → IProp GF)
    (Ra : List GoError → IProp GF) (arcv : List GoError) (ro : Loc) (γo : GName)
    (c0 : DemuxCore),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isCacheFields c cf γr γd cap ∗
      isSpsc γa aec Pa Ra ∗ spscConsumer γa arcv ∗
      sync.isOnce ro (dghostVar γo (DFrac.own (1 : Qp).half) false)
        (dghostVar γo DFrac.discard true) ∗
      cacheWriter cf γd cap c0 ∗ ⌜0 < sint.Z rev⌝ ∗
      (dghostVar γo (DFrac.own (1 : Qp).half) false ∨
        (dghostVar γo DFrac.discard true ∗ ⌜CursorOk cf.pfx c0 (rev - W64 1)⌝)) }}
    (App (App (App (Val (c @!! go.GoType.PointerType Cache.ty @!! go!"watchEvents")) (Val #rev))
      (Val #aec)) (Val #ro))
  {{ (err : GoInterface), RET #err; ∃ c1 : DemuxCore, cacheWriter cf γd cap c1 ∗
      (dghostVar γo (DFrac.own (1 : Qp).half) false ∨
        (dghostVar γo DFrac.discard true ∗ ⌜CursorOk cf.pfx c1 (rev - W64 1)⌝)) }}

end spec

end EtcdGrove
end Perennial
