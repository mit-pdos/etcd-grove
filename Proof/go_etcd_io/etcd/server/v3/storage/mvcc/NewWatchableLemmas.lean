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

theorem wsInit_settled [FfiSyntax] : wsInit.settled := by
  constructor
  · intro w γw ed h; simp [wsInit, GMap.lookup_empty] at h
  · exact ⟨fun w st h => by simp [wsInit, WsState.victimOf] at h,
      fun w st h => by simp [wsInit, GMap.lookup_empty] at h⟩

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

instance wsWgInv_timeless_ctor (γwg : sync.WaitGroupNames) (γd : GName) :
    Timeless (wsWgInv (GF := GF) γwg γd) := by
  unfold wsWgInv; infer_instance

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
