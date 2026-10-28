/-
Lean-first (no Rocq counterpart).

The proof of `CounterClock`: the invariant (at `N`) owns the counter `n`, the other half of
the clock's ghost value (`ghostVar γ ½ n`) and `n` time receipts; a reading's Go step (the
method resolution of `Add`) brings one more receipt, so `n + 1 < receiptBound GF ≤ 2^63`
(`receipt_add_one_lt`) and the increment does not wrap around.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock
public import Perennial.Spec.sync.atomic.Int64__Add
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

theorem CounterClock.wp_proof :
    CounterClock.spec (GF := GF) (hG := hG) := fun N Hbound => by
  wp_start
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hu
  ihave Hu : sync.atomic.ownInt64 (GF := GF) «$r0_ptr» (DFrac.own 1) (W64 0) $$ [Hu]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact Hu
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γ, Hv⟩
  icases ghostVar_split γ (W64 0) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod receipt_zero (GF := GF) with H0
  imod inv_alloc N ⊤ iprop(∃ k : Nat, sync.atomic.ownInt64 (GF := GF) «$r0_ptr» (DFrac.own 1) (W64 (k : Int)) ∗
      ghostVar γ (1 : Qp).half (W64 (k : Int)) ∗ ⧗ k) $$ [Hu Hv1 H0] with #Hinv
  · inext; iexists 0; iframe
  ipersist t
  imodintro
  iapply HΦ
  iexists (fun t => ghostVar γ (1 : Qp).half t)
  iframe Hv2
  unfold clockSpec
  imodintro
  iintro %Φ' HAU
  wp_pure
  wp_pure
  wp_alloc r as Hres
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_load
  wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal _
  inext
  iintro Hr Hlc
  iapply wp_value'
  wp_apply_core sync.atomic.Int64.wp_Add «$r0_ptr» (W64 1) $$ [] [-]
  · iPkgInit
  iinv Hinv with ⟨%k, >Hu, >Hv, >Hk⟩ Hclose
  imod HAU with ⟨%t0, Hv', Hcommit⟩
  icombine Hv Hv' gives % ⟨_, Heq⟩
  subst Heq
  icases receipt_add_one_lt k $$ [Hr Hk] with ⟨%Hlt, Hk⟩
  · iframe
  have Hk63 : k + 1 < 2 ^ 63 := Nat.lt_of_lt_of_le Hlt Hbound
  have Hadd : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
  imodintro
  inext
  iexists (W64 (k : Int))
  iframe Hu
  iintro Hu
  rw [Hadd]
  imod ghostVar_update_halves (W64 ((k + 1 : Nat) : Int)) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hcommit $$ [Hv'] with HΦ'
  · iframe
    ipureintro
    word
  imod Hclose $$ [Hu Hv Hk] with -
  · inext; iexists k + 1; iframe
  imodintro
  wp_auto
  iapply HΦ'
  itrivial

end proof

end lintest
end EtcdGrove
end Perennial
