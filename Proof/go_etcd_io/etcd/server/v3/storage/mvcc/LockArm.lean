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
update `P ∗ Pre ∗ HN ={⊤}=∗ P ∗ Post` (the hook given back through it; `P` seen since `KV.Compact.contract`,
2026-11-06: an API compactor's nil-hook contract updates `P ∗ Pre`). -/
def lockArmS (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    IProp GF :=
  match hk with
  | some f => iprop(HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
      (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post))
  | none => iprop(HN ∗ lockNilSpec bt RT WT W P HN Locked ∗ (P ∗ Pre ∗ HN ={⊤}=∗ P ∗ Post))

theorem lockArmS_some (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    lockArmS bt RT WT W P HF Locked HN (some f) Pre Q Post =
      iprop(HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
        (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post)) := rfl

theorem lockArmS_none (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (Pre Q Post : IProp GF) :
    lockArmS bt RT WT W P HF Locked HN none Pre Q Post =
      iprop(HN ∗ lockNilSpec bt RT WT W P HN Locked ∗ (P ∗ Pre ∗ HN ={⊤}=∗ P ∗ Post)) := rfl

/-- **The critical section's context, by the hook's state at the store** (item 31, switched
2026-10-30; the restore Draft's A2): the hook set to `f` (the hook's facts and the caller's
contract for it), or unset (`none`: the batch lock's invariant `P` named, the new backend's unset
hook lent, and the caller's update from `Pre` to `Post` with `P` passing through, `LockInsideApply`
running nothing: `lockNilSpec`). (`KV.Compact.contract`, 2026-11-06: the writer's fragment is no
longer lent, the hook's facts `hookOk` in place of the writer's `hookIs`, and the unset arm's update
sees `P`: an API compactor holds a share of the backend, not the writer's fragment, and its hook
contract's nil arm, `hookRun`, updates `P ∗ Pre`.) (§4.8, a store without a hook, 2026-11-06) The
unset arm lends the share `dq` of the hook at `nil` (`kbHookNilAt`): the client's half (the default,
`restore()`'s resumed compaction), or the hook frozen at `nil` (`DFrac.discard`: the API's compactor
on a store the server never sets a hook on). -/
def lockCtxM (γ : StoreNames) (P : IProp GF) (hk : Option val) (Pre Q Post : IProp GF)
    (dq : DFrac := DFrac.own (1 : Qp).half) : IProp GF :=
  match hk with
  | some f => iprop(hookOk γ P f ∗ csContract P f Pre Q Post)
  | none => iprop(hookP γ P ∗ kbHookNilAt γ.kb dq ∗ Pre ∗ (P ∗ Pre ={⊤}=∗ P ∗ Post))

/-- What the call gives back of the context (with `Post` or `Pre` beside it). -/
def lockBackM (γ : StoreNames) (P : IProp GF) (hk : Option val)
    (dq : DFrac := DFrac.own (1 : Qp).half) : IProp GF :=
  match hk with
  | some f => hookOk γ P f
  | none => iprop(hookP γ P ∗ kbHookNilAt γ.kb dq)

theorem lockCtxM_some (γ : StoreNames) (P : IProp GF) (f : val) (Pre Q Post : IProp GF)
    (dq : DFrac) :
    lockCtxM γ P (some f) Pre Q Post dq = iprop(hookOk γ P f ∗ csContract P f Pre Q Post) := rfl

theorem lockBackM_some (γ : StoreNames) (P : IProp GF) (f : val)
    (dq : DFrac) :
    lockBackM γ P (some f) dq = hookOk γ P f := rfl

theorem lockCtxM_none (γ : StoreNames) (P : IProp GF) (Pre Q Post : IProp GF)
    (dq : DFrac) :
    lockCtxM γ P none Pre Q Post dq =
      iprop(hookP γ P ∗ kbHookNilAt γ.kb dq ∗ Pre ∗ (P ∗ Pre ={⊤}=∗ P ∗ Post)) := rfl

theorem lockBackM_none (γ : StoreNames) (P : IProp GF) (dq : DFrac) :
    lockBackM γ P none dq = iprop(hookP γ P ∗ kbHookNilAt γ.kb dq) := rfl

/-- The caller's `Pre`, out of the context (the error paths give it back). -/
theorem lockCtxM_pre (γ : StoreNames) (P : IProp GF) (hk : Option val) (Pre Q Post : IProp GF)
    (dq : DFrac) :
    lockCtxM (GF := GF) γ P hk Pre Q Post dq ⊢ lockBackM γ P hk dq ∗ Pre := by
  cases hk with
  | some f =>
    unfold lockCtxM lockBackM csContract
    iintro ⟨Hh, Hpre, -, -⟩
    iframe Hh Hpre
  | none =>
    unfold lockCtxM lockBackM
    iintro ⟨Hh, Hn, Hpre, -⟩
    iframe Hpre
    isplitl [Hh]
    · iexact Hh
    iexact Hn

/-- **The compaction's ghost step, by its caller** (`KV.Compact.contract`, 2026-11-06; in place of the
placeholders `rcvSched_M1`, `slotX_step_M1`'s and `regLent_excl_M1`'s uses by `updateCompactRev`):
what `updateCompactRev` fires, at the compaction revision `c` (`compactMainRev` at `cp`) and the
revision `rev`. Success (fired inside `SetScheduledCompact`'s loan, under both locks, the batch lock
held, the writer's state found checked in: mask `⊤ ∖ writerN`): `s.revMu`'s slot and the writer's
quarter of the view, with its part of the pending revision, at the committed log `L`, moved to
`rev`, giving `Fok`; `ErrCompacted` (under `s.revMu`): the lock's slot read, `Fce`; `ErrFutureRev`
(under `s.revMu`): likewise, `Ffr`. The API's compactor gives it from its atomic update and the
compaction right's quarter of the authority (`Api/CmpCb.lean`); `restore()`'s resumed compaction,
at `c = rev`, the identity (`cmpCb_refl`). -/
def cmpCb (γ : StoreNames) (c cp rev : Int) (Fok Fce Ffr : IProp GF) : IProp GF :=
  iprop((∀ L : Log, ⌜cp < rev ∧ c ≤ rev ∧ rev < L.length⌝ -∗
      slotX γ 1 L c ∗ api.absPart γ.api (1 : Qp).half.half L c ∗ api.pndPart γ.api (pndW γ) none
        ={⊤ \ ↑writerN}=∗
      slotX γ 1 L rev ∗ api.absPart γ.api (1 : Qp).half.half L rev ∗
        api.pndPart γ.api (pndW γ) none ∗ Fok) ∧
    (∀ L : Log, ⌜rev ≤ c⌝ -∗ slotX γ 1 L c ={⊤}=∗ slotX γ 1 L c ∗ Fce) ∧
    (∀ L : Log, ⌜(L.length : Int) - 1 < rev ∧ c < L.length⌝ -∗ slotX γ 1 L c ={⊤}=∗
      slotX γ 1 L c ∗ Ffr))

/-- **The identity step** (`restore()`'s resumed compaction: at `c = rev`, the slots already at the
records' revision). -/
theorem cmpCb_refl (γ : StoreNames) (rev cp : Int) :
    ⊢ cmpCb (GF := GF) γ rev cp rev iprop(True) iprop(True) iprop(False) := by
  unfold cmpCb
  isplit
  · iintro %L %_ ⟨HX, Ha, Hp⟩
    imodintro; iframe HX Ha Hp
  isplit
  · iintro %L %_ HX
    imodintro; iframe HX
  · iintro %L %h -
    exfalso; omega

end arm

section lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Two names of the batch lock's invariant agree, a step later (`hookP_agree_lc` without the hook:
the unset arm's, `updateCompactRev`'s). -/
theorem hookP_agree_lc2 (E : CoPset) (γ : StoreNames) (P P' : IProp GF) :
    £ 1 ∗ hookP γ P ∗ hookP γ P' ⊢ |={E}=> □ (P -∗ P') ∗ □ (P' -∗ P) := by
  iintro ⟨Hlc, #H1, #H2⟩
  iunfold hookP at H1 H2
  ihave Heq := saved_prop_agree γ.hook DFrac.discard DFrac.discard P P' $$ H1 H2
  imod lc_fupd_elim_later $$ Hlc Heq with #Heq
  ihave #Hiff := internalEq_iff P P' $$ Heq
  imodintro
  isplitl []
  · iintro !> HP
    icases Hiff with ⟨#H, -⟩
    iapply H
    iexact HP
  · iintro !> HP
    icases Hiff with ⟨-, #H⟩
    iapply H
    iexact HP

end lc

end mvcc
end EtcdGrove
end Perennial
