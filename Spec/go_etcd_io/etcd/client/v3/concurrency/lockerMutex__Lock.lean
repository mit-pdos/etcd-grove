/-
`concurrency.lockerMutex.Lock()` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`lm.Lock()`** (`NewLocker`'s `sync.Locker`): `Mutex.Lock(client.Ctx())` on the wrapped
mutex `m`, for a client whose context is cancelable (`Mutex.Lock` takes one), knowing etcd has
reached `lo`: `Mutex.Lock`'s `nil` case (the lock held, or the key re-created). On any error
(which every client call allows) `Lock` calls `panic(err)`, which nothing recovers: in Perennial
an unrecovered panic is stuck at the end of the function body (`exceptionDo (panicVal #err)`,
`wp_exceptionDo_panic`). As for Perennial's `shouldPanic`, the spec states where it gets stuck:
the precondition assumes a WP of that stuck expression for every error (which only `▷ False`
provides), so the triple says what it does when it returns. -/
abbrev lockerMutex.Lock.spec : Prop :=
  ∀ (lm m s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : MutexSt)
    (cctx : GoInterfaceOk) (ccs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗
      structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗ isMutex m s γ client id pfx ∗ mutexState m st ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" client ↦□ GoInterface.ok cctx ∗
      context.isContext cctx ccs ∗ context.isCancelCtxCtx cctx ccs ∗ etcdReached lo ∗
      (∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ ∀ Ψ : val → IProp GF,
        WP (App (Val exceptionDo) (Val (panicVal #err))) {{ Ψ }}) }}
    (App (Val (lm @!! go.GoType.PointerType lockerMutex.ty @!! go!"Lock")) (Val #()))
  {{ RET #(); structFieldRef lockerMutex go!"Mutex" lm ↦ m ∗
      ∃ (key : GoString) (rev R : w64) (hdr : Loc),
        mutexState m ⟨key, rev, hdr⟩ ∗ hdrRevAt hdr R ∗ etcdReached R ∗
        (lockedAt pfx key rev R ∨ keyRecreated pfx key rev R) ∗
        ⌜pfx <+: key ∧ sint.Z lo ≤ sint.Z R⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
