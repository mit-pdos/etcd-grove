/-
`mvcc.wp_wsWg_Wait` (the store's one waiter's `s.wg.Wait()`), out of `watchableStore__Close.lean`'s
proof so that `Api/CloseApi.lean` imports it without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.wg.Wait()` by the store's one waiter, which (R-D1, 2026-11-04) then takes the loops' readers
of the inner store with its claim (`token γw`): the counter at `0`, every loop has called `Done`. -/
theorem mvcc.wp_wsWg_Wait (s st : Loc) (γs : mvcc.StoreNames) (γwg : sync.WaitGroupNames)
    (γd γw : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (mvcc.wsWgAddr s) γwg mvcc.wsWgWGN ∗
        inv mvcc.wsWgN (mvcc.wsWgInv st γs γwg γd γw) ∗ sync.ownWaitGroupWaitToken γwg ∗ token γw }}
      (App (Val (mvcc.wsWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); [∗list] _x ∈ List.replicate mvcc.wsLoopN (), mvcc.storeReader st γs }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Htok, Hγw⟩ HΦ
  iapply sync.WaitGroup.wp_Wait (mvcc.wsWgAddr s) γwg mvcc.wsWgWGN $$ [Htok] [HΦ Hγw]
  · iframe #
    iframe
  iinv Hinv with Hi Hclose
  · exact mvcc.wsWg_maskN
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold mvcc.wsWgInv at Hi
  icases Hi with ⟨%ctr, %n, %d, Hwgo, Hauth, %Hctr, Hdep⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  have hd : d = mvcc.wsLoopN := by omega
  icases Hdep with (Hl | Hr)
  · imod Hclose $$ [Hwgo Hauth Hγw] with -
    · inext
      unfold mvcc.wsWgInv
      iexists ctr, n, d
      iframe Hwgo Hauth
      isplitr
      · ipureintro; exact Hctr
      iright; iexact Hγw
    imodintro
    iintro -
    iapply HΦ
    rw [← hd]
    iexact Hl
  · iexfalso
    iapply token_exclusive $$ Hr Hγw


end proof

end EtcdGrove
end Perennial
