/-
**The Lock service's server's contracts** (the auth plan's A3c, 2026-10-24; `notes/decisions.md`,
"A3c of the auth plan: Lock and Election"). Lean-first (no Rocq counterpart).

The server (`v3lock.lockServer`, `lock.go`) holds a `*clientv3.Client`, in etcd the in-process
client `v3client.New(s)` over the server's own gRPC handlers (untranslated here). Its handlers make
only client calls: `Lock` a session over the request's lease and a mutex on the request's name
(the client's `concurrency` package, proved), `Unlock` one delete of the request's key. So the
server's specs are stated over what they need of that client, as hypotheses (axiom-free):
`lockClientOk` (the session's client contract and, for every prefix, the mutex's client
contracts, `concurrency.isEtcdSessionClient`/`isEtcdMutexClient`) and `unlockKVOk` (the client's
`Delete` on one key returns a response whose header is readable, and on success the delete's
result `deleteResult`). Each handler's class is the requests those calls send: the KV requests on
keys under `name/` and the lease's (`Lock`), the delete of the request's key (`Unlock`), as the
context's principal (the in-process client passes the request's context to the server's handlers,
whose A1/A2 statements check it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Base
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3lock

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency concurrency

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

/-- A session option's spec is persistent (it is `□ ...`; the instance is missing upstream, in
`concurrency/InvSession.lean`). -/
instance sessionOptSpec_persistent' (f : GoFunc) (g : SessionOpts → SessionOpts) :
    Persistent (sessionOptSpec (GF := GF) f g) := by
  unfold sessionOptSpec; infer_instance

/-- **The server's client, for `Lock`**: `NewSession`'s client contract and, for every prefix, the
mutex's (persistent). -/
def lockClientOk (c : Loc) : IProp GF :=
  iprop(∃ cctx : GoInterface, isEtcdSessionClient c cctx ∗
    □ ∀ pfx : GoString, isEtcdMutexClient c pfx)

instance lockClientOk_persistent (c : Loc) : Persistent (lockClientOk (GF := GF) c) := by
  unfold lockClientOk; infer_instance

/-- **The server's client, for `Unlock`**: its `KV`'s `Delete(ctx, key)` (no options) returns an
error, or a response whose header is readable, with the delete's result (`deleteResult` over every
key, of the one key) (persistent). -/
def unlockKVOk (c : Loc) : IProp GF :=
  iprop(∃ kv : GoInterfaceOk, clientKVAddr c ↦□ GoInterface.ok kv ∗
    □ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString),
      {{ context.isContext ctx cs }}
        (App (App (App (Val #(methods kv.ty go!"Delete" kv.v)) (Val #(GoInterface.ok ctx)))
          (Val #key)) (Val #slice.nil))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          ⌜err ≠ GoInterface.nil⌝ ∨
          (⌜err = GoInterface.nil⌝ ∗ ∃ hdr : Loc,
            structFieldRef go_etcd_io.etcd.client.v3.DeleteResponse go!"Header" resp ↦□ hdr ∗
            deleteResult [] (W64 0) (opDeleteModel key []) GoInterface.nil) }})

instance unlockKVOk_persistent (c : Loc) : Persistent (unlockKVOk (GF := GF) c) := by
  unfold unlockKVOk; infer_instance

/-- **A lock server** `ls` over the client `c` (read-only). -/
def isLockServer (ls c : Loc) : IProp GF :=
  iprop(structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer
    go!"c" ls ↦□ c)

instance isLockServer_persistent (ls c : Loc) : Persistent (isLockServer (GF := GF) ls c) := by
  unfold isLockServer; infer_instance

end defs

end v3lock
end EtcdGrove
end Perennial
