/-
# The Lock service (`etcdserver/api/v3lock`): vocabulary (batch 2e)

etcd serves `v3lockpb.Lock` with an in-process client: `Lock` makes a session over the request's
lease (orphaned) and runs 1d's `Mutex.Lock`; `Unlock` deletes the request's key. Its specs are 1d's
facts read off the request.

* `isLockServer ls c` (persistent): `ls` is an `*lockServer` over the client `c`.
* The messages: 3h's `V3lockpb.lockReq` (name, lease), `unlockReq` (key), read-only;
  `lockResp` (the key), `unlockResp`, fresh (verify-round, A8 completeness F4: the provisional
  opaque names are now abbreviations of 3h's, so the gRPC handler's decoded request and 3h's field
  and reply laws apply).

**The prefix.** `concurrency.NewMutex(s, name)` locks under `name + "/"` (1d's `NewMutex.spec`):
the facts these specs state are about `name ++ "/"` (verify-round, A3 completeness F1, A8
provability F6: a key `name ++ "z"` created earlier is not under the lock's prefix).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3lock

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `ls` is a `*lockServer` over the client `c` (persistent). -/
opaque isLockServer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ls : Loc) (c : Loc) : IProp GF := iprop(True)

/-- A read-only `*LockRequest` (persistent): 3h's. -/
abbrev lockReq (p : Loc) (name : GoString) (lease : w64) : IProp GF := V3lockpb.lockReq p name lease
/-- A read-only `*UnlockRequest` (persistent): 3h's. -/
abbrev unlockReq (p : Loc) (key : GoString) : IProp GF := V3lockpb.unlockReq p key
/-- A fresh `*LockResponse` holding the key: 3h's. -/
abbrev lockResp (p : Loc) (key : GoString) : IProp GF := V3lockpb.lockResp p key
/-- A fresh `*UnlockResponse`: 3h's. -/
abbrev unlockResp (p : Loc) : IProp GF := V3lockpb.unlockResp p

def isLockServer_persistent.spec : Prop := ∀ ls c, Persistent (isLockServer (GF := GF) ls c)

end res

end V3lock
end EtcdGrove
end Perennial
