/-
`concurrency.Mutex.Unlock(ctx)` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
`InvMutex.lean`.
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

/-- **`m.Unlock(ctx)`**, from any state, knowing etcd has reached `lo`:
* `nil`: the mutex had a key (under the prefix) and is released (`myKey = "\x00"`,
  `myRev = -1`), and at some `R ≥ lo` the incarnation it acquired, `(myKey, myRev)`, is gone
  (`unlockedAt`): the key is absent, or a later incarnation of it is there, which the fenced
  delete (etcd-io/etcd#22115) leaves in place;
* `ErrLockReleased`: it had no key (`MutexSt.noKey`), unchanged;
* any other error (the transaction failed, or the key is not under the prefix), unchanged.

What the fence prevents, deleting a later incarnation, is not a property of this triple: the
client's model records knowledge only, and the unfenced delete meets it too
(`etcdAbsent_unlockedAt`). It is a property of the transaction committed, `unlockTxn`
(`unlockTxn_keeps_later`; `Proof/.../Mutex__Unlock.lean`). -/
abbrev Mutex.Unlock.spec : Prop :=
  ∀ (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : MutexSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s γ client id pfx ∗ mutexState m st ∗
      context.isContext ctx cs ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Unlock")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ R : w64, mutexState m (MutexSt.released st.hdr) ∗
        etcdReached R ∗ unlockedAt pfx st.key st.rev R ∗
        ⌜¬ st.noKey ∧ pfx <+: st.key ∧ sint.Z lo ≤ sint.Z R⌝) ∨
      (isPkgErr ErrLockReleased err ∗ mutexState m st ∗ ⌜st.noKey⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ mutexState m st) }}

/-- **The spec before etcd-io/etcd#22115** (an unfenced `Delete(myKey)`), kept for comparison: a
`nil` return meant `myKey` absent at `R`, whatever incarnation was there. It implies the new spec
(`etcdAbsent_unlockedAt`; the other cases are the same), but the fenced code does not meet it: a
failed guard leaves a later incarnation of `myKey` present. The `nil` case is weaker now, so the
callers were re-checked (`notes/pr-verify/etcd-22115.md`). -/
abbrev Mutex.Unlock.spec_old : Prop :=
  ∀ (m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : MutexSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s γ client id pfx ∗ mutexState m st ∗
      context.isContext ctx cs ∗ etcdReached lo }}
    (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Unlock")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ R : w64, mutexState m (MutexSt.released st.hdr) ∗
        etcdReached R ∗ etcdAbsent pfx st.key R ∗
        ⌜¬ st.noKey ∧ pfx <+: st.key ∧ sint.Z lo ≤ sint.Z R⌝) ∨
      (isPkgErr ErrLockReleased err ∗ mutexState m st ∗ ⌜st.noKey⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ mutexState m st) }}

end spec

end concurrency
end EtcdGrove
end Perennial
