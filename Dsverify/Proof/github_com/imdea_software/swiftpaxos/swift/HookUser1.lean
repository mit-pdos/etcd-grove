/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HookUser1.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`hook.HookUser1(f)` (hook/hook.go): a channel for `SIGUSR1`, `signal.Notify` on it, and a
goroutine that waits on it, then runs `f`. The net model never delivers a signal
(Harness/Proof/os/signal.lean): the channel is a bag of `False` messages, so the goroutine's
receive never returns and `f` never runs. `hook.HookUser1.specI` (Proof/swift/NewSpecs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

-- PORT: lab imports dropped: Harness.Proof.os.signal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [hook.Assumptions] [SwiftNoSignals netDistGF]

set_option goose.wp.extras true

/-- The fork's hook.go writes `SIGUSR1` as the literal `syscall.Signal(0xa)` (the harness's
`syscall.SIGUSR1` is opaque), so no premise on its value is needed. -/
theorem hook.HookUser1.wp_proof [syscall.Assumptions] [os.Assumptions] :
    hook.HookUser1.specI (hG := hG) := by
  intro fv
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := GoInterface) (W64 1) as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null $$ Hch
  iapply fupd_wp
  imod start_bag (fun _ : GoInterface => iprop(False)) (ChanState.Buffered []) ch γ (by trivial)
    $$ [$Hch] [Hown] with #Hbag
  · iExactEq Hown; simp
  imodintro
  ihave #Hsig : isPkgInit (PROP := IProp netDistGF) pkg_id.os.signal $$ []
  · iPkgInit
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_auto
  wp_apply os.signal.NotifyQuietUsr1.wp_hyp _ _ _ Hnn $$ [$Hsig $Hsl] as -
  wp_apply wp_fork $$ [-HΦ]
  · wp_auto
    wp_apply wp_bag_receive γ ch (fun _ : GoInterface => iprop(False)) $$ [$Hbag] as %v HF
    iexfalso; iexact HF
  iapply HΦ; itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
