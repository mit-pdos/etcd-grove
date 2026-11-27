/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__goFunc.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).goFunc` (called through `*Raft`).

Quarter thread tokens (decision D15): the routines group's invariant (`rgInv`) holds one quarter
per goroutine not `Done` in a quarter bank. At `routinesGroup.Add(1)` the caller deposits its own
quarter `rtok tid` (the bank's quarters and the caller's are at most `4 * (threadBound GF - 1)`, so
the counter stays below `2^31` for `threadBound GF ≤ 2^28`); at the `go` statement
(`wp_fork_rtok_upd`) it takes it back and deposits one of the four quarters of the goroutine's fresh
slot `k` instead. The goroutine runs `f` with another (`rtok k`), keeps the other two, and at its
`Done` withdraws the deposited one, ending with its four quarters.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.raftState.goFunc.wp_proof :
    github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG) :=
  fun r γ rc i f tid => by
  wp_start as ⟨#His, Htok, Hf⟩
  ihave #Hrg := isRaft_rg r γ rc i $$ His
  unfold rgOk
  icases Hrg with ⟨%γwg, %γb, #Hwg, #Hinv, %HT⟩
  wp_method_call; wp_call
  wp_bind (App (Val raftState.goFunc.impl) (Val _))
  wp_call
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_load
  wp_pures
  wp_apply_core sync.WaitGroup.wp_Add _ (W64 1) γwg (rgN.@"wg") $$ [] [-]
  · iframe #; iPkgInit
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (sync.wg_mask_ndot_ne rgN "wg" "inv" (by decide))
  iintro Hmask
  inext
  iunfold rgInv at Hi
  icases Hi with ⟨%n, Hwgo, Hwait, Hb⟩
  icases qbank_count γb n tid $$ [Hb Htok] with ⟨%Hle, Hb, Htok⟩
  · iframe
  have hn : n + 1 < 2 ^ 31 := by omega
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hz : sint.Z (W32 n) = n := by
    word
  iexists W32 n
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1, hz]; omega
  iright
  iframe Hwait
  iintro Hwait Hwgo
  imod Hmask with -
  imod qbank_deposit γb n tid $$ [Hb Htok] with ⟨Hb, HslipA⟩
  · iframe
  imod Hclose $$ [Hwgo Hwait Hb] with -
  · inext
    iunfold rgInv
    iexists n + 1
    have he : W32 n + W32 (sint.Z (W64 1)) = W32 (n + 1) := by
      rw [show W32 (sint.Z (W64 1)) = W32 1 from by decide]; word
    rw [he]
    iframe
  imodintro
  wp_pures
  wp_bind (Fork _)
  iapply wp_fork_rtok_upd
  inext
  iintro %k Hk1 Hk2 Hk3 Hk4 _
  -- at the fork: the caller's quarter back, one of the goroutine's in its place
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iunfold rgInv at Hi
  icases Hi with ⟨%n1, >Hwgo, >Hwait, >Hb⟩
  imod qbank_withdraw γb n1 tid $$ [Hb HslipA] with ⟨%n2, %Hn12, Hb, Htok⟩
  · iframe
  imod qbank_deposit γb n2 k $$ [Hb Hk4] with ⟨Hb, HslipB⟩
  · iframe
  imod Hclose $$ [Hwgo Hwait Hb] with -
  · inext
    iunfold rgInv
    iexists n1
    rw [Hn12]
    iframe
  imodintro
  isplitr [HΦ Htok]
  · wp_pures
    wp_apply wp_with_defer as %defer Hdefer
    wp_bind (App (Val #f) (Val #()))
    ispecialize Hf $$ %k Hk1
    iapply wp_wand $$ Hf
    iintro %v ⟨%hv, Hk1⟩
    subst hv
    wp_auto
    wp_apply_core sync.WaitGroup.wp_Done _ γwg (rgN.@"wg") $$ [] [-]
    · iframe #; iPkgInit
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
    iunfold rgInv at Hi
    icases Hi with ⟨%n', >Hwgo, >Hwait, >Hb⟩
    icases qbank_count γb n' k $$ [Hb Hk1] with ⟨%Hle', Hb, Hk1⟩
    · iframe
    imod qbank_withdraw γb n' k $$ [Hb HslipB] with ⟨%m, %Hm, Hb, Hk4⟩
    · iframe
    subst Hm
    iapply fupd_mask_intro (sync.wg_mask_ndot_ne rgN "wg" "inv" (by decide))
    iintro Hmask
    inext
    have hm : m + 1 < 2 ^ 31 := by omega
    have hz' : sint.Z (W32 (m + 1 : Nat)) = (m + 1 : Nat) := by
      word
    iexists W32 (m + 1 : Nat)
    iframe Hwgo
    isplitr
    · ipureintro; rw [hz']; omega
    iintro Hwgo
    imod Hmask with -
    imod Hclose $$ [Hwgo Hwait Hb] with -
    · inext
      iunfold rgInv
      iexists m
      have he : W32 (m + 1 : Nat) - W32 1 = W32 m := by word
      rw [he]
      iframe
    imodintro
    wp_auto
    iframe
  wp_pures
  iapply HΦ $$ Htok
  done

end proof

end Perennial
