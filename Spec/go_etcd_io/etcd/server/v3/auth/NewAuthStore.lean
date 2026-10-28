/-
`auth.NewAuthStore(lg, be, tp, cost)` (`store.go`): names-only. Lean-first (no Rocq counterpart);
the server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`;
an axiom at the trust boundary since unit N4 (2026-10-17, D14d/D14f/D14g), why it is true of the
Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewAuthStore(lg, ab, tp, cost)`** over schema's auth backend `ab` wrapping the real
backend `d` (`NewAuthBackend`'s result), its auth data fresh: an auth store, disabled, with its
reader resource `RD`: the request path's contract (`isReqAuth`) and the apply contract with auth
off (`isAuthStore … false`) at the backend's batch lock `Pk` and any frozen post-lock hook `f`
(D14d), one write-back token per write, the reader's open share lent (D14f).

Why it is true of the Go code (`NewAuthStore`, `authStore`'s methods, `schema`'s `authBackend`,
at the etcd pin):
* `CreateAuthBuckets` (`LockOutsideApply`, the buckets created, `Unlock`: one write-back), then
  `be.BatchTx()`'s `Lock` (`authBatchTx.Lock` is `LockInsideApply`: the post-lock hook not yet
  installed, nil, `plHook d.γB func.nil` borrowed), `UnsafeReadAuthEnabled` (false: the auth
  buckets are empty, the tracked buckets' half `backend.rbOwn d.γB r` says so, D22, 2026-10-23;
  until then the opaque token `bkFresh d.γB "auth"`), the revision (0: `commitRevision` puts the
  revision `1`, so the half is given back with the auth buckets present, `auth` holding it:
  `authBoot`),
  `refreshRangePermCache` (no user to decode: no panic), `Unlock` (`authBatchTx.Unlock` is the
  batch `Unlock`, one write-back, then `Commit`, which commits first and does not write back),
  `ForceCommit` (likewise none): two tokens. `setupMetricsReporter` registers gauge functions
  that read the revision under its lock.
* Auth disabled: the permission checks return `nil` (`IsPutPermitted` etc. return early when
  `!isAuthEnabled()`), `IsAdminPermitted` too; only `AuthEnable` enables it, which the contract
  takes only at `on = true`: with `on = false` it stays disabled.
* Each write method (the admin requests, `AuthDisable`) takes the batch lock inside the apply
  (`Lock` = `LockInsideApply`: the backend open, a share lent in `mvcc.bkRTx`, and the frozen hook
  run under `Pk`, `csContract Pk f`), puts into the auth buckets (hook buckets for the readers'
  view: unchanged), and unlocks with one write-back (its `Commit` and `AuthEnable`'s
  `ForceCommit` write none back; the backend's specs of `Commit`/`ForceCommit` charge a token, a
  coarser accounting than the code's). Its puts are into tracked buckets (D22, 2026-10-23): each
  write method takes and gives back the tracked buckets' client half (`srvRestRW d.γB`, the
  contract's `RW`), which the server's apply thread never lends (no auth request is admitted). Its keys: a new user's or role's name, bounded by the
  contract (`authReqContractN`, `issues/etcd-auth-useradd-long-name-fatal.md`); its values:
  within bbolt's value bound (`authRecordsFit`, a named workload premise).
* The reader resource `RD` is a reader slot of the store's `enabledMu` (a `sync.RWMutex`, made by
  `NewAuthStore`): the lock's slots, one per reader (D14i, 2026-10-17: the request path's and the
  apply thread's each hold one; the Go `RWMutex` panics only beyond `2 ^ 30` readers); likewise of
  `rangePermCacheMu` and (the fork's d52eec43e, D22k (A)) of `beMu`, under which the permission
  checks take their read transaction (`lockedReadTx`) and `Recover` replaces `be`.
* (D22 receiver epochs, S7c, 2026-10-23) `beMu`'s lock holds half of `as.be` (`auth.beP`), the
  caller gets the other (`authBeOn stl d.be`: `ab` wraps `d.be`); the writes read `as.be` (through
  the auth backend's batch transaction), so they write to the backend the caller's half names: the
  apply contract (`authApplyOk`) is for whichever backend that is, given a write right lending that
  half; `Recover` (names-only) needs both halves, the write lock's and the caller's. Until S7c the
  contract was for `d` only, which `Recover` falsifies. 
* (D22 J1a, 2026-10-26; `notes/decisions.md`, "D22 J1a"; until then S8d's named premise
  `srvAuthRecoverOk` of `applySnapshot.specSnap`) **`Recover` on a later backend**
  (`authRecoverOk stl`): `Recover(ab)` (`store.go:399-418`) takes `beMu`'s write lock to set
  `as.be` (the lock's half of `as.be` and the caller's, `authBeOn stl oldbe`, become the new
  backend's), then a read transaction of the new backend (`ReadTx`'s `RLock`/`RUnlock`: the
  reader's token `bkRTx` and an open share lent, given back) reading `authEnabled` (absent in an
  image whose auth bucket is `authBoot`: false) and the revision (`setRevision` under its lock), and
  `refreshRangePermCache` over the image's users (none: `authUsers` empty, no decoding, no panic),
  then `enabledMu`'s write lock to set `enabled = false` (the token provider's `enable` not
  called). The store stays disabled, so its contracts above (stated for auth off) hold after it,
  and `RD` names no backend's read right (the checks return before reading the backend).
-/
abbrev auth.NewAuthStore.spec : Prop :=
  ∀ (lg : Loc) (ab tp : GoInterface) (cost : w64) (abl : Loc) (d : mvcc.KBReal)
    (W Pk : IProp GF) (qo : Qp) (r : GMap GoString backend.BktData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ ∗
      ⌜tp ≠ GoInterface.nil⌝ ∗ ⌜authRecordsFit⌝ ∗
      ⌜ab = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) #abl⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗
      backend.plHook d.γB func.nil ∗ ownToks d.γB.wb 2 ∗ backend.rbOwn d.γB r ∗
      ⌜(r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
        (r.lookup go!"authRoles").getD ∅ = ∅⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
      (Val #ab)) (Val #tp)) (Val #cost))
  {{ (st : GoInterface), RET #st; backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
      backend.rbOwn d.γB (((r.insert go!"auth" authBoot).insert go!"authUsers" ∅).insert
        go!"authRoles" ∅) ∗
      ∃ (RD : IProp GF) (stl : Loc), ⌜st = auth.authIface stl⌝ ∗ authBeOn stl d.be ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), RD) ∗
      isReqAuth st RD ∗ authApplyOk stl RD ∗
      -- (D22 J1a, 2026-10-26) `Recover` on a new backend, in the server's terms (see above)
      authRecoverOk stl }}

end spec

end EtcdGrove
end Perennial
