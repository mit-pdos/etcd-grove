/-
Lemmas for the watchable store's constructors over a restored image (B3; mvccfull's Freeze,
2026-11-10): the lock invariant's initial state at the notified log `L` (`wsInitAt`, `wsInit` at
any log), the frozen fact by the mode from `NewStore`'s post, and the right to close by the mode
from the inner store's. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- The lock invariant's initial state at the notified log `L`: no watcher, no victim. -/
def wsInitAt [GooseExts] (L : Log) : WsState :=
  { Lmu := L, Ws := ∅, Wu := ∅, ST := ∅, Wo := ∅, M := ∅, E := ∅, vs := slice.nil,
    vbs := [], VB := [] }

theorem wsInitAt_ok [GooseExts] (L : Log) : WsOk (wsInitAt L) := by
  have hv : ∀ w, (wsInitAt L).victimOf w = none := fun w => rfl
  have hl : ∀ w, ¬ (wsInitAt L).live w := by
    intro w h
    unfold WsState.live at h
    rw [hv w] at h
    simp [wsInitAt, GMap.lookup_empty] at h
  constructor <;> intros <;> simp_all [wsInitAt, GMap.lookup_empty, WsState.victimOf]

theorem wsInitAt_settled [GooseExts] (L : Log) : (wsInitAt L).settled := by
  constructor
  · intro w γw ed h; simp [wsInitAt, GMap.lookup_empty] at h
  · exact ⟨fun w st h => by simp [wsInitAt, WsState.victimOf] at h,
      fun w st h => by simp [wsInitAt, GMap.lookup_empty] at h⟩

theorem wsInitAt_srBelow [GooseExts] (L : Log) : (wsInitAt L).srBelow (wsInitAt L).Lmu.length := by
  intro w γw h; simp [wsInitAt, GMap.lookup_empty] at h

theorem wsInitAt_unsRst [GooseExts] (L : Log) : (wsInitAt L).unsRst := by
  intro w st h; simp [wsInitAt, GMap.lookup_empty] at h

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The frozen fact by the mode, from `NewStore`'s post**: off, the compaction revision's half
frozen (`crevFrozen_alloc`); on, nothing to do. -/
theorem wsFrozenM_of_new (γs : StoreNames) (b : Bool) (h : γs.cm = b) :
    (if b then iprop(True) else crevUB (GF := GF) γs.idx (1 : Qp).half (-1)) ⊢
      |={⊤}=> wsFrozenM γs := by
  subst h
  unfold wsFrozenM
  by_cases hc : γs.cm = true
  · simp only [hc, ↓reduceIte]
    iintro -; imodintro; itrivial
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    iintro H
    imod crevFrozen_alloc γs ⊤ $$ H with #Hf
    imodintro; iexact Hf

/-- **The watchable store's right to close by the mode**, from its stop channel's close, its waiter
and the inner store's right to close by the mode (`New`'s last step). -/
theorem wsCloserM_of (s st : Loc) (γs : StoreNames) (c : Int) (stc : Loc) :
    s.[watchableStore, go!"stopc"] ↦□ stc ∗ stopCloser (GF := GF) stc ∗ wsWaiter s st γs ∗
      storeCloserM st γs c ⊢ wsCloserM s st γs c := by
  iintro ⟨#Hstc, Hsc, Hw, Hcl⟩
  by_cases hm : kbCmpM γs.kb
  · iapply (wsCloserM_on s st γs c hm).2
    iapply (wsCloserR_iff s st γs c).2
    iexists stc
    iframe Hstc Hsc Hw
    iapply (storeCloserM_on st γs c hm).1
    iexact Hcl
  · iapply (wsCloserM_off s st γs c hm).2
    iunfold wsCloser
    iexists stc
    iframe Hstc Hsc Hw
    iapply (storeCloserM_off st γs c hm).1
    iexact Hcl

end lemmas

end mvcc
end EtcdGrove
end Perennial
