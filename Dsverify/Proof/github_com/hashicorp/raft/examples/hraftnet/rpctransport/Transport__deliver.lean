/-
The proof of `rpctransport.Transport.deliver`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__deliver
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QTok
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport


theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C cmd data hb Q
  wp_start as ⟨#Ht, Hpre⟩
  ihave #Henv := dialEnv_of_pkg $$ Hpkg
  iunfold dialEnv at Henv
  icases Henv with ⟨-, #Hsync, -⟩
  unfold isTrans
  iNamed Ht
  wp_auto
  wp_apply (chan.wp_make2 (V := github_com.hashicorp.raft.RPCResponse) (W64 1)) as %rch %γr ⟨#Hrch, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_bag Q _ rch γr (by simp) $$ Hrch Hown with #Hbag
  ispecialize Hpre $$ %rch %γr Hbag
  ipersist t
  wp_join iprop(∃ f : GoFunc, fn_ptr ↦ f ∗ (⌜f = func.nil⌝ ∨ (⌜hb = true⌝ ∗ github_com.hashicorp.raft.hbHandler γ i f))) with [fn] as ⟨%f, fn, Hfo⟩
  · iexists _; iframe fn; ileft; ipureintro; rfl
  · wp_apply wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
    iunfold hbInv at Hinv
    icases Hinv with ⟨%f, Hf, Hfo⟩
    wp_auto
    ihave #Hfo' : (⌜f = func.nil⌝ ∨ github_com.hashicorp.raft.hbHandler γ i f : IProp GF) $$ [Hfo]
    · icases Hfo with (%H | #H)
      · ileft; ipureintro; exact H
      · iright; iexact H
    wp_apply wp_Unlock $$ [$Hmu $Hlk Hf]
    · inext; unfold hbInv; iexists f; iframe Hf; iexact Hfo'
    wp_join_done
    iexists f; iframe fn
    icases Hfo' with (%H | #H)
    · ileft; ipureintro; exact H
    · iright; iframe H
  simp only [← decide_not]
  wp_join iprop(True) with [Hpre Hfo fn r] as -
  · icases Hfo with (%Hnil | ⟨%Hhbt, #Hh⟩)
    · exact absurd Hnil Hif
    icases Hpre with ⟨-, Hhb⟩
    ispecialize Hhb $$ %Hhbt
    (try wp_auto)
    wp_bind (Fork _)
    iapply (wp_fork_rtok _ _) $$ [Hhb]
    · inext
      iintro %tid Htok
      iunfold github_com.hashicorp.raft.hbHandler at Hh
      iapply Hh $$ Hhb Htok
      iintro Htok
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    · inext
      wp_auto
      wp_join_done
      (try itrivial)
  · icases Hpre with ⟨Hrp, -⟩
    iunfold github_com.hashicorp.raft.isRpcChan at Hrpc
    icases Hrpc with ⟨%γc, #Hcb⟩
    (try wp_auto)
    wp_apply (wp_bag_send γc ch _ (github_com.hashicorp.raft.rpcP γ snapP i)) $$ [$Hcb $Hrp]
    wp_join_done
    (try itrivial)
  wp_apply (wp_bag_receive γr rch Q) $$ [$Hbag] as %rv HQ
  (try wp_auto)
  iapply HΦ
  iexists rv
  iframe HQ
  ipureintro; exact ⟨rfl, rfl⟩

end proof

end Perennial
