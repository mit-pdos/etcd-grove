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
  `myRev = -1`); its delete was fenced by the create revision (etcd-io/etcd#22115): at some
  `R ≥ lo` it either deleted exactly the incarnation `(myKey, myRev)` or, that incarnation being
  gone already, deleted nothing (`unlockedAt`) — never a later incarnation of `myKey`;
* `ErrLockReleased`: it had no key (`MutexSt.noKey`), unchanged;
* any other error (the transaction failed, or the key is not under the prefix), unchanged.

Before etcd-io/etcd#22115 (`Mutex.Unlock.spec_old`) the `nil` case was `etcdAbsent pfx myKey R`:
the key, whatever its create revision, absent at `R`, since the delete was by name only. -/
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
`nil` return means `myKey` is absent at `R`, whatever incarnation was there. The new spec does not
imply it (a failed guard leaves a later incarnation of `myKey` present), nor it the new one (it
allows deleting a later incarnation): the change is incompatible, on purpose. -/
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
