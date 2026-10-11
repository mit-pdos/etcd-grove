/-
Proof of `Spec/newNotifier.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newNotifier.wp_proof : newNotifier.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γc, Hauth, #Hlb⟩
  imod ghostVar_alloc (GF := GF) (NotifierCur.mk ch γch ⟨0⟩ 0) with ⟨%γcur, Hcur⟩
  imod alloc_broadcast_chan (E := ⊤) (notifierLb (GF := GF) ⟨γc, γcur⟩ (0 + 1)) γch ch $$ Hch Hoc
    with Hbc
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γi, #Hint, Hpend⟩
  imod ghostVar_update (NotifierCur.mk ch γch γi 0) γcur _ $$ Hcur with Hcur
  wp_alloc n as Hn
  iStructNamed Hn
  imod sync.init_RWMutex (notifierLockInv (hG := hG) n ⟨γc, γcur⟩) (notifierMuAddr n)
    $$ [Hcur ch Hauth Hpend] mu with Htoks
  · inext
    unfold notifierLockInv
    iexists NotifierCur.mk ch γch γi 0
    simp only [named]
    iframe
    iframe #
  wp_auto
  -- keep the kernel from unfolding the reader count (`2^30 - 1` tokens)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m := ⟨_, rfl⟩
  rw [hm]
  iapply HΦ $$ %n %(NotifierNames.mk γc γcur)
  isplitr
  · unfold notifierLb; iexact Hlb
  unfold notifierHandle
  iexact Htoks

end proof

end EtcdGrove
end Perennial
