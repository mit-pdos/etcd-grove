/-
`concurrency.ResumeMutex(s, pfx, myKey, myRev)` (`client/v3/concurrency/mutex.go`, added by
etcd-io/etcd#22384). Lean-first (no Rocq counterpart); see `InvMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`ResumeMutex(s, pfx, myKey, myRev)`**, for a session `s` whose client answers for the prefix
`pfx + "/"` (`isEtcdMutexClient`, as `NewMutex`): a mutex on that prefix (the same `/` as
`NewMutex`, unlike `ResumeElection`, which adds none) whose state is the given key and create
revision, with no header (`hdr = nil`). Nothing is checked: the key and revision are the caller's,
and the mutex gets no ownership fact (`lockedAt`); the methods' specs, which run from any state,
say what each does from it (`IsOwner` compares `myKey`'s create revision with `myRev`; `Unlock`
deletes `myKey` if it is under the prefix and `myRev > 0`). -/
abbrev ResumeMutex.spec : Prop :=
  ∀ (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx myKey : GoString) (myRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s γ client id ∗
      isEtcdMutexClient client (pfx ++ go!"/") }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.ResumeMutex)) (Val #s))
      (Val #pfx)) (Val #myKey)) (Val #myRev))
  {{ (m : Loc), RET #m; isMutex m s γ client id (pfx ++ go!"/") ∗
      mutexState m { key := myKey, rev := myRev, hdr := null } }}

end spec

end concurrency
end EtcdGrove
end Perennial
