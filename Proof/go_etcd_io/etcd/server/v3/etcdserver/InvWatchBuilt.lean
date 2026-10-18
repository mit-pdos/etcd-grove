/-
**The watch store `NewServer` builds** (2026-10-18; the watch-token pool's allocation, D19b's
method). Lean-first (no Rocq counterpart).

`srvWatchBuilt s E`: the server's `kv` field is the watchable store `wsl` (`mvcc.New`'s), over
the apply environment's store `E.s` at names `γw` whose store names are `E.γ`, with the watch-token
pool (`mvcc.watchTokPool γw`, allocated by `NewServer` from `New`'s tokens). The part of the watch
server's contract (`v3rpc.watchSrvOk`) the construction gives; the rest (`raftStatusOk`, the auth
store's, `watchVars`) is item 9's point 7.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The watch store `NewServer` builds** (persistent; see the file header). -/
def srvWatchBuilt (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ (wsl : Loc) (γw : mvcc.WsNames),
    srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
    mvcc.isWatchableStore wsl E.s γw ∗ ⌜γw.st = E.γ⌝ ∗ mvcc.watchTokPool γw)

instance srvWatchBuilt_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvWatchBuilt (GF := GF) s E) := by
  unfold srvWatchBuilt; infer_instance

end defs

end EtcdGrove
end Perennial
