/-
**The watch store `NewServer` builds** (2026-10-18; the watch-token pool's allocation, D19b's
method). Lean-first (no Rocq counterpart).

`srvWatchBuilt s E`: the server's `kv` field is the watchable store `wsl` (`mvcc.New`'s), the apply
environment's KV handle `E.kv`, with the API's handle facts (`□ isMvcc E.kv E.γ`); strict M1
(2026-11-06): until then over mvcc's internals (`isWatchableStore`, the watch-token pool, the auth
mode's tag at the store's names). `srvKVCloser` moved to `SnapRO.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

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

/-- **The watch store `NewServer` builds** (persistent; see the file header): the server's `kv`
field is a watchable store `wsl` (`mvcc.New`'s), the apply environment's KV handle (`E.kv`), with
the API's handle facts at the environment's names (`□ isMvcc E.kv E.γ`). (Strict M1, 2026-11-06:
over mvcc's API; until then `mvcc.isWatchableStore wsl E.s γw` at names `γw` with `γw.st = E.γ`,
the watch-token pool `mvcc.watchTokPool γw` and the mode tag `auth.modeTag γw.tag E.authMode`. The
API's `WatchableKV.NewWatchStream.contract` needs only `isMvcc` (at the watchable store's type,
`shapes.law`'s second conjunct), a watch stream's thread its `threadTok`; the API's names carry no
tag. `srvWatchReaders`, its reader slots of mvcc's locks, is gone with them.) -/
def srvWatchBuilt (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ wsl : Loc, srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
    ⌜E.kv = interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl⌝ ∗
    □ mvcc.api.isMvcc E.kv E.γ)

instance srvWatchBuilt_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvWatchBuilt (GF := GF) s E) := by
  unfold srvWatchBuilt; infer_instance

/-- **The watch store `NewServer` builds, with `n` of the store's reader tokens** (watch.txt's run
slots, 2026-10-20, watchkv: `v3rpc.watchRunSlot` takes reader slots per watch stream; until then
`NewServer` dropped them): `srvWatchBuilt`'s facts and `n` reader tokens of the store
(`mvcc.api.mvccReaders E.γ n`: a watch stream's `Watch`, `RequestProgress`, `Rev` each borrow one).
(The `lean` merge, 2026-11-06, the reader tokens: until then `n` reader slots of the watchable
store's locks, `mvcc.watchReader`, at internal names `γw` with the watch-token pool and the mode tag;
the API's reader tokens are what a stop hands `backend.Close` back, `srvWatchReaders_readers`.) -/
def srvWatchReaders (s : Loc) (E : apply.AEnv GF) (n : Nat) : IProp GF :=
  iprop(srvWatchBuilt s E ∗ mvcc.api.mvccReaders E.γ n)

/-- **The watch service's reader tokens** (R2c review round 2's N3): what a stop hands the backend's
`Close` (`srvStopReaders_intro`). -/
theorem srvWatchReaders_readers (s : Loc) (E : apply.AEnv GF) (n : Nat) :
    srvWatchReaders s E n ⊢ mvcc.api.mvccReaders E.γ n := by
  iintro HWR
  iunfold srvWatchReaders at HWR
  icases HWR with ⟨-, Hr⟩
  iexact Hr

-- (D22 J1b, 2026-11-01) `srvKVCloser` moved to `SnapRO.lean` (`srvSnapRes` holds it).

-- (2026-11-01, the merge of `lean`) `srvKVCloserW` moved to `SnapRO.lean` with `srvKVCloser`
-- (`srvSnapRes` holds it).

end defs

end EtcdGrove
end Perennial
