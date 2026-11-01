/-
**A critical section of the batch lock by the post-lock hook's state** (M2, the storage side, item
31, 2026-10-30): `SetScheduledCompact`'s `LockInsideApply` runs the hook if one is set
(`batch_tx.go:111-122`). The hook is set on every backend the server applies to, but not yet on the
new backend `kv.Restore` installs while `restore()` resumes a scheduled compaction (the server sets
it after `Restore` returns, `server.go:1089-1093`): there the lock runs nothing.

- `lockNilSpec` (`InvStore.lean`, since 2026-10-30 `batchTxSpecG`'s clause): `LockInsideApply` with
  no hook set, from the session's tokens and the unset hook `HN`, gives the lock, its resource `W`
  and the batch lock's invariant `P` itself. The real backend gives it (`bt_lockInNil`,
  `BackendBridge.lean`, from the backend spec's nil arm).
- `lockArmS`: what a caller of `SetScheduledCompact` brings for the critical section, by the hook's
  state: set to `f` (the hook's `HF f`, its triple and the caller's update with the hook's `Q`), or
  unset (`HN`, `lockNilSpec` and the caller's update from `Pre`, `P` passing through).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section arm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The critical section's context, by the hook's state** (`SetScheduledCompact`'s): set to `f`,
the hook's `HF f`, its triple `{P ∗ Pre} f() {Q}` and the caller's update `Q ∗ W ={⊤}=∗ P ∗ W ∗
Post`; unset, the unset hook `HN` with `LockInsideApply`'s nil arm (`lockNilSpec`), and the caller's
update `Pre ∗ HN ={⊤}=∗ Post` (the hook given back through it). -/
def lockArmS (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    IProp GF :=
  match hk with
  | some f => iprop(HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
      (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post))
  | none => iprop(HN ∗ lockNilSpec bt RT WT W P HN Locked ∗ (Pre ∗ HN ={⊤}=∗ Post))

theorem lockArmS_some (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    lockArmS bt RT WT W P HF Locked HN (some f) Pre Q Post =
      iprop(HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
        (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post)) := rfl

theorem lockArmS_none (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (Pre Q Post : IProp GF) :
    lockArmS bt RT WT W P HF Locked HN none Pre Q Post =
      iprop(HN ∗ lockNilSpec bt RT WT W P HN Locked ∗ (Pre ∗ HN ={⊤}=∗ Post)) := rfl

/-- **The critical section's context, by the hook's state at the store** (item 31, switched
2026-10-30; the restore Draft's A2): the hook set to `f` (the writer's hook and the caller's
contract for it), or unset (`none`: the batch lock's invariant `P` named, the writer's fragment, the
new backend's unset hook lent, and the caller's update from `Pre` to `Post`, `LockInsideApply`
running nothing: `lockNilSpec`). -/
def lockCtxM (γ : StoreNames) (P : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    IProp GF :=
  match hk with
  | some f => iprop(hookIs γ P f ∗ csContract P f Pre Q Post)
  | none => iprop(hookP γ P ∗ writerFrag γ ∗ kbHookNil γ.kb ∗ Pre ∗ (Pre ={⊤}=∗ Post))

/-- What the call gives back of the context (with `Post` or `Pre` beside it). -/
def lockBackM (γ : StoreNames) (P : IProp GF) (hk : Option val) : IProp GF :=
  match hk with
  | some f => hookIs γ P f
  | none => iprop(hookP γ P ∗ writerFrag γ ∗ kbHookNil γ.kb)

theorem lockCtxM_some (γ : StoreNames) (P : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    lockCtxM γ P (some f) Pre Q Post = iprop(hookIs γ P f ∗ csContract P f Pre Q Post) := rfl

theorem lockBackM_some (γ : StoreNames) (P : IProp GF) (f : val) :
    lockBackM γ P (some f) = hookIs γ P f := rfl

theorem lockCtxM_none (γ : StoreNames) (P : IProp GF) (Pre Q Post : IProp GF) :
    lockCtxM γ P none Pre Q Post =
      iprop(hookP γ P ∗ writerFrag γ ∗ kbHookNil γ.kb ∗ Pre ∗ (Pre ={⊤}=∗ Post)) := rfl

theorem lockBackM_none (γ : StoreNames) (P : IProp GF) :
    lockBackM γ P none = iprop(hookP γ P ∗ writerFrag γ ∗ kbHookNil γ.kb) := rfl

/-- The caller's `Pre`, out of the context (the error paths give it back). -/
theorem lockCtxM_pre (γ : StoreNames) (P : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    lockCtxM (GF := GF) γ P hk Pre Q Post ⊢ lockBackM γ P hk ∗ Pre := by
  cases hk with
  | some f =>
    unfold lockCtxM lockBackM csContract
    iintro ⟨Hh, Hpre, -, -⟩
    iframe Hh Hpre
  | none =>
    unfold lockCtxM lockBackM
    iintro ⟨Hh, Hw, Hn, Hpre, -⟩
    iframe Hpre
    isplitl [Hh]
    · iexact Hh
    isplitl [Hw]
    · iexact Hw
    iexact Hn

end arm

end mvcc
end EtcdGrove
end Perennial
