/-
**The watch store `NewServer` builds** (2026-10-18; the watch-token pool's allocation, D19b's
method). Lean-first (no Rocq counterpart).

`srvWatchBuilt s E`: the server's `kv` field is the watchable store `wsl` (`mvcc.New`'s), over
the apply environment's store `E.s` at names `γw` whose store names are `E.γ`, with the watch-token
pool (`mvcc.watchTokPool γw`, allocated by `NewServer` from `New`'s tokens). `srvKVCloser s E`: the
right to close that watchable store (`mvcc.wsCloser`, with the inner store's `storeCloser`: its
scheduler's stop token), which `NewServer` keeps for the snapshot path (D22 S-g, D22d (A)). The part of the watch
server's contract (`v3rpc.watchSrvOk`) the construction gives; the rest (`raftStatusOk`, the auth
store's, `watchVars`) is item 9's point 7. Both hold the auth mode's tag at the store's names
(`auth.modeTag γw.tag E.authMode`, the auth plan's A4, 2026-10-24: `mvcc.New` takes the name,
`NewServer` tags it with its mode).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.auth.ModeTag

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The watch store `NewServer` builds** (persistent; see the file header). -/
def srvWatchBuilt (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ (wsl : Loc) (γw : mvcc.WsNames),
    srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
    mvcc.isWatchableStore wsl E.s γw ∗ ⌜γw.st = E.γ⌝ ∗ mvcc.watchTokPool γw ∗
    auth.modeTag γw.tag E.authMode)

instance srvWatchBuilt_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvWatchBuilt (GF := GF) s E) := by
  unfold srvWatchBuilt; infer_instance

/-- **The watch store `NewServer` builds, with `n` of its reader slots** (watch.txt's run slots,
2026-10-20, watchkv: `v3rpc.watchRunSlot` takes two of them per watch stream; until then
`NewServer` dropped them): `srvWatchBuilt`'s facts at some `wsl`, `γw`, and `n` reader slots of
the watchable store's two locks (`mvcc.watchReader`) at the same names. -/
def srvWatchReaders (s : Loc) (E : apply.AEnv GF) (n : Nat) : IProp GF :=
  iprop(∃ (wsl : Loc) (γw : mvcc.WsNames),
    srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
    mvcc.isWatchableStore wsl E.s γw ∗ ⌜γw.st = E.γ⌝ ∗ mvcc.watchTokPool γw ∗
    auth.modeTag γw.tag E.authMode ∗
    [∗list] _x ∈ List.replicate n (), mvcc.watchReader wsl E.s γw)

/-- **The KV's closer, kept** (D22 S-g, 2026-10-19, D22d (A); until then `NewServer` dropped it, D19m
(C)): the right to close the server's watchable store (`mvcc.wsCloser`: its stop channel's close,
the wait for its loops, and the inner store's `storeCloser`, the stop channel's close, the
scheduler's stop token and the compaction jobs' queue). `store.Restore` (`applySnapshot`'s
`s.kv.Restore(newbe)`, D22 S-j) closes the inner store's `stopc` and stops its scheduler with
it; the server's `Stop` path would close the store with it. -/
def srvKVCloser (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ wsl : Loc,
    srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
    mvcc.wsCloser wsl E.s E.γ)

/-- **The KV's closer without the compaction right** (M2's apply side, item 20; review round 1's
F-6): off, `srvKVCloser`; on, the watchable store's own parts (its stop channel's close and its
waiter), the inner store's compaction right being the apply thread's (`apply.cmpOwn` in
`apply.applyKV`, A1). What `NewServer` hands out (in compaction mode after giving the right to the
boot state). -/
def srvKVCloserW (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  if mvcc.kbCmpM E.γ.kb then
    iprop(∃ wsl : Loc,
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      ∃ stc : Loc, wsl.[go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore, go!"stopc"] ↦□ stc ∗
        mvcc.stopCloser stc ∗ mvcc.wsWaiter wsl)
  else srvKVCloser s E

/-- Off, the closer. -/
theorem srvKVCloserW_off (s : Loc) (E : apply.AEnv GF) (h : ¬ mvcc.kbCmpM E.γ.kb) :
    srvKVCloserW (GF := GF) s E = srvKVCloser s E := by
  unfold srvKVCloserW; simp only [h, ↓reduceIte]

end defs

end EtcdGrove
end Perennial
