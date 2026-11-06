/-
**`store.Write`'s critical section, by the hook's state** (M4, track B, 2026-11-06: request 4,
`notes/mvcc-api-invariants.md`, "M4, track B"). Lean-first (no Rocq counterpart).

`store.Write`'s `LockInsideApply` runs the post-lock hook if one is set (`batch_tx.go:111-122`). The
API's `KV.Write.contract` takes the hook's contract `hookRun P f Pre Q` at the storage's frozen hook
`f` (`hookIs B f`): set, the hook's triple from `P ∗ Pre` to `Q`; `nil` (a store the server never
sets a hook on, the tester's), the caller's view shift `P ∗ Pre ={⊤}=∗ Q`, run on the batch lock's
invariant itself (`LockInsideApply`'s nil arm, `batchTxSpecG`'s `lockNilSpec`). As
`updateCompactRev`'s `lockCtxM` (`LockArm.lean`), but the hook's `Q` is the caller's (a write
transaction holds the lock until its `End`, which takes `P` back).

* `writeCtxM γ P hk Pre Q dq`: set (`some f`), the hook's facts at the store's names, the caller's
  `Pre` and the hook's triple; unset (`none`), the store's name of the invariant, the share `dq` of the
  hook at `nil` (lent to `LockInsideApply`), `Pre` and the caller's view shift.
* What comes back is `lockBackM γ P hk dq` (`LockArm.lean`), with `Q`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section ctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`store.Write`'s critical section, by the hook's state** (see the header). -/
def writeCtxM (γ : StoreNames) (P : IProp GF) (hk : Option val) (Pre Q : IProp GF) (dq : DFrac) :
    IProp GF :=
  match hk with
  | some f => iprop(hookOk γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}))
  | none => iprop(hookP γ P ∗ kbHookNilAt γ.kb dq ∗ Pre ∗ (P ∗ Pre ={⊤}=∗ Q))

theorem writeCtxM_some (γ : StoreNames) (P : IProp GF) (f : val) (Pre Q : IProp GF) (dq : DFrac) :
    writeCtxM γ P (some f) Pre Q dq =
      iprop(hookOk γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }})) := rfl

theorem writeCtxM_none (γ : StoreNames) (P : IProp GF) (Pre Q : IProp GF) (dq : DFrac) :
    writeCtxM γ P none Pre Q dq =
      iprop(hookP γ P ∗ kbHookNilAt γ.kb dq ∗ Pre ∗ (P ∗ Pre ={⊤}=∗ Q)) := rfl

/-- **The write's begin callback** (§3, "`Write`'s begin": after the writer's checkout, at mask `⊤`):
run once by `store.Write` with the writer's quarter of the view and its part of the pending revision
(`slotY`'s, at the committed log `L` and the writer slot's compaction revision `c`, which is the
transaction's), giving `F L c` and the parts back. The API's `Write` fires its client's update by
agreement there; a caller with no update passes `writeCb_true`. -/
def writeCb (γ : StoreNames) (F : Log → Int → IProp GF) : IProp GF :=
  iprop(∀ (L : Log) (c : Int),
    api.absPart γ.api (1 : Qp).half.half L c ∗ api.pndPart γ.api (pndW γ) none ={⊤}=∗
      api.absPart γ.api (1 : Qp).half.half L c ∗ api.pndPart γ.api (pndW γ) none ∗ F L c)

open Iris.ProofMode in
theorem writeCb_true (γ : StoreNames) : ⊢ writeCb (GF := GF) γ (fun _ _ => iprop(True)) := by
  unfold writeCb
  iintro %L %c ⟨Ha, Hp⟩
  imodintro; iframe Ha Hp

open Iris.ProofMode in
/-- **A transaction's compaction revision is the writer slot's** (the two shares of `wcr` agree:
`s.mu`'s part, the transaction's `muHeld`, and the writer slot's half). -/
theorem muHeld_wcr (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) (q : Qp) (c' : Int) :
    muHeld (GF := GF) s γ c ti ∗ api.wcrPart γ.api q c' ⊢
      muHeld s γ c ti ∗ api.wcrPart γ.api q c' ∗ ⌜c = c'⌝ := by
  iintro ⟨Hm, Hw⟩
  iunfold muHeld at Hm
  icases Hm with ⟨Hl, Ha, Hrest⟩
  iunfold muInvAt at Ha
  iNamed Ha
  ihave %Hcc := api.wcrPart_agree γ.api _ _ c c' $$ [HwcM Hw]
  · iframe HwcM Hw
  iframe Hw
  isplitl
  · iunfold muHeld; iframe Hl Hrest
    iunfold muInvAt; iframe HcmpM HcrevM HwcM; iframe #; ipureintro; exact HcM
  ipureintro; exact Hcc

end ctx

end mvcc
end EtcdGrove
end Perennial
