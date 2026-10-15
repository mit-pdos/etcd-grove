/-
Lemmas for the watchable store's constructors and `Close` (`New`, `newWatchableStore`, `Close`):
the wait group's counter invariant is timeless, its masks. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- The lock invariant's initial state: the initial log, no watcher, no victim. -/
def wsInit [FfiSyntax] : WsState :=
  { Lmu := [[], []], Ws := ∅, Wu := ∅, ST := ∅, Wo := ∅, M := ∅, E := ∅, vs := slice.nil,
    vbs := [], VB := [] }

theorem wsInit_ok [FfiSyntax] : WsOk wsInit := by
  have hv : ∀ w, wsInit.victimOf w = none := fun w => rfl
  have hl : ∀ w, ¬ wsInit.live w := by
    intro w h
    unfold WsState.live at h
    rw [hv w] at h
    simp [wsInit, GMap.lookup_empty] at h
  constructor <;> intros <;> simp_all [wsInit, GMap.lookup_empty, WsState.victimOf]

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

instance wsWgInv_timeless_ctor (γwg : sync.WaitGroupNames) (γd : GName) :
    Timeless (wsWgInv (GF := GF) γwg γd) := by
  unfold wsWgInv; infer_instance

theorem wsWg_maskW : (↑wsWgWGN : CoPset) ⊆ ⊤ \ ↑wsWgN :=
  sync.wg_mask_ndot_ne nroot "mvccWaitGroup" "mvccWgCounter" (by decide)

theorem wsWg_maskN : (↑wsWgN : CoPset) ⊆ ⊤ \ ↑wsWgWGN :=
  sync.wg_mask_ndot_ne nroot "mvccWgCounter" "mvccWaitGroup" (by decide)

theorem ghostVar_halves_nw {A : Type} [Pos.Countable A] (γ : GName) (a : A) :
    (ghostVar (GF := GF) γ 1 a : IProp GF) ⊣⊢ ghostVar γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half a := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (ghostVar_fractional γ a).fractional _ _

/-- Two lists of `n` resources, pointwise. -/
theorem replicate_sep_nw (A B : IProp GF) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), A) ∗ ([∗list] _x ∈ List.replicate n (), B) ⊢
      [∗list] _x ∈ List.replicate n (), iprop(A ∗ B)
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨Ha, Hb⟩
    icases BigSepL.bigSepL_cons.1 $$ Ha with ⟨Ha1, Ha⟩
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨Hb1, Hb⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Ha1 Hb1
    iapply replicate_sep_nw A B n
    iframe Ha Hb

/-- A guard of a lock from its reader slots (there is at least one). -/
theorem guard_of_slots_nw (rw : Loc) (P : Qp → IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ⊢
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), sync.ownRWMutex rw P) ∗
        sync.isRWMutexGuard rw P := by
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨Htok, Htoks⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  iframe Hguard
  iapply BigSepL.bigSepL_cons.2
  iframe Htok Htoks

/-- The watchable store's reader slots from the inner store's and its lock's. -/
theorem watchReaders_of (s st : Loc) (γ : WsNames) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), storeReader st γ.st) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (wsMuAddr s) (watchStoreInv s γ)) ⊢
      [∗list] _x ∈ List.replicate n (), watchReader (GF := GF) s st γ := by
  unfold watchReader
  exact replicate_sep_nw _ _ n

/-- `s.wg.Add(2)` on the fresh wait group (counter `0`, no waiter: `New`'s), owned. -/
theorem wp_wsWg_Add2_init (s : Loc) (γwg : sync.WaitGroupNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (wsWgAddr s) γwg wsWgWGN ∗
        sync.ownWaitGroup γwg (W32 0) ∗ sync.ownWaitGroupWaiters γwg 0 }}
      (App (Val (wsWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 2)))
    {{ RET #(); sync.ownWaitGroup γwg (W32 2) ∗ sync.ownWaitGroupWaiters γwg 0 }} := by
  iintro %Φ ⟨#Hsync, #Hwg, Hc, Hw⟩ HΦ
  iapply sync.WaitGroup.wp_Add (wsWgAddr s) (W64 2) γwg wsWgWGN $$ [] [Hc Hw HΦ]
  · iframe #
  iapply fupd_mask_intro CoPset.subseteq_top
  iintro Hmask
  inext
  iexists W32 0
  iframe Hc
  isplitr
  · ipureintro; decide
  iright
  iframe Hw
  iintro Hw Hc
  imod Hmask with -
  imodintro
  iapply HΦ
  iframe

end lemmas

end mvcc
end EtcdGrove
end Perennial
