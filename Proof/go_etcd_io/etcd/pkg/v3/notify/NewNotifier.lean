/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/notify/NewNotifier.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.notify.NewNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.notify.Assumptions]

/-- A guard of a lock from its reader slots (there is at least one; as `read_guard_of_slots`). -/
theorem notify_guard_of_slots [sync.Assumptions] (rw : Loc) (P : Qp → IProp GF) :
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

theorem notify.NewNotifier.wp_proof : notify.NewNotifier.spec (GF := GF) (hG := hG) := by
  wp_start as -
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γch ch $$ Hch Hoc with Hbc
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γi, #Hint, Hpend⟩
  wp_alloc n as Hn
  iStructNamed Hn
  imod ghostVar_alloc (NotifyCur.mk ch γch γi) with ⟨%γ, Hcur⟩
  imod sync.init_RWMutex (notifyLockInv n γ) (notifyMuAddr n) $$ [channel Hcur Hpend] mu with Hslots
  · inext; iunfold notifyLockInv; iexists NotifyCur.mk ch γch γi; simp only [named]; iframe
    iexact Hint
  icases notify_guard_of_slots _ _ $$ Hslots with ⟨Hslots, #Hguard⟩
  wp_auto
  iapply HΦ
  isplitr
  · iunfold isNotifier; iexists γ; iexact Hguard
  iapply BigSepL.bigSepL_mono_of_forall (fun {_ _} => ?_) $$ Hslots
  iintro H
  iunfold notifyReader
  iexists γ
  iexact H

end proof

end EtcdGrove
end Perennial
