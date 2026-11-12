/-
Lean-first (no Rocq counterpart).

The proof of `(*compactor).Stop`: `stopOnce.Do` of the closure that calls `onClose` when it is
not `nil` (`closeOk`: it returns; Q1 (c), 2026-11-05), closes the
`stop` channel and waits for the loop goroutine, with what `stopOnce` holds until its first run
(the channel's closing right and the wait group's adder, `compactorStopOk`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__Stop
public import Perennial.Spec.sync.Once__Do
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem compactor.Stop.wp_proof : compactor.Stop.spec (GF := GF) (hG := hG) := by
  intro c cl γk recorded γc
  wp_start as #Hc
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isCompactor at Hc
  icases Hc with ⟨#Hcore, %sc, %γs, #Hstop⟩
  iunfold compactorCore at Hcore
  icases Hcore with ⟨%Hpers, #Hcl, #Hiv, #Hck, ⟨%f, #Honc, #Hclose⟩, #Hmu, -⟩
  iunfold compactorStopOk at Hstop
  icases Hstop with ⟨#Hch, #Honce⟩
  iunfold compactorChanOk at Hch
  icases Hch with ⟨#Hsc, #Hbc⟩
  (try wp_auto)
  ipersist c
  wp_apply sync.Once.wp_Do $$ [$Honce]
  · iintro !> %Φ' ⟨HP, %n, Hadd⟩ HΦ'
    (try wp_auto)
    -- `onClose`, when not `nil`
    by_cases hf : f = func.nil
    -- `nil`: nothing to call
    rw [decide_eq_true hf]
    (try wp_auto)
    rotate_left
    -- otherwise it returns (`closeOk`)
    rw [decide_eq_false hf]
    iunfold closeOk at Hclose
    icases Hclose with (%h | #Hf)
    · exact absurd h hf
    (try wp_auto)
    wp_bind (App (Val #f) (Val #()))
    iapply Hf
    inext
    (try wp_auto)
    all_goals (
      wp_apply wp_broadcast_chan_close $$ [$HP] as -
      · itrivial
      (try wp_auto)
      wp_apply sync.join.WaitGroup.wp_Wait $$ [$Hadd] as -
      (try wp_auto)
      iapply HΦ'; itrivial)
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end k8s
end EtcdGrove
end Perennial
