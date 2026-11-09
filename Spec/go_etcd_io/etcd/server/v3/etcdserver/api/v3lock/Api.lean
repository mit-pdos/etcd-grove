/-
# The Lock service (`etcdserver/api/v3lock`): vocabulary (batch 2e)

etcd serves `v3lockpb.Lock` with an in-process client: `Lock` makes a session over the request's
lease (orphaned) and runs 1d's `Mutex.Lock`; `Unlock` deletes the request's key. Its specs are 1d's
facts read off the request.

* `isLockServer ls c` (persistent): `ls` is an `*lockServer` over the client `c`.
* The messages (opaque, **provisional: 3h's**): `lockReq` (name, lease), `unlockReq` (key),
  read-only; `lockResp` (the key), `unlockResp`, fresh.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api
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
variable [go_gctx : GoGlobalContext]

/-- `ls` is a `*lockServer` over the client `c` (persistent). -/
opaque isLockServer (ls : Loc) (c : Loc) : IProp GF := iprop(True)

/-- A read-only `*LockRequest` (persistent). -/
opaque lockReq (p : Loc) (name : GoString) (lease : w64) : IProp GF := iprop(True)
/-- A read-only `*UnlockRequest` (persistent). -/
opaque unlockReq (p : Loc) (key : GoString) : IProp GF := iprop(True)
/-- A fresh `*LockResponse` holding the key. -/
opaque lockResp (p : Loc) (key : GoString) : IProp GF := iprop(True)
/-- A fresh `*UnlockResponse`. -/
opaque unlockResp (p : Loc) : IProp GF := iprop(True)

def isLockServer_persistent.spec : Prop := ∀ ls c, Persistent (isLockServer (GF := GF) ls c)

end res

end V3lock
end EtcdGrove
end Perennial
