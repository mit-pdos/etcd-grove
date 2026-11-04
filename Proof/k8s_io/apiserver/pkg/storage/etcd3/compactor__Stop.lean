/-
Lean-first (no Rocq counterpart).

The proof of `(*compactor).Stop`: `stopOnce.Do` of the closure that (no `onClose`) closes the
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
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem compactor.Stop.wp_proof : compactor.Stop.spec (GF := GF) (hG := hG) := by
  intro c cl γk recorded γc
  wp_start as #Hc
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isCompactor at Hc
  icases Hc with ⟨%Hpers, #Hcl, #Hiv, #Hck, #Honc, #Hmu, %sc, %γs, #Hstop⟩
  iunfold compactorStopOk at Hstop
  icases Hstop with ⟨#Hsc, #Hbc, #Honce⟩
  (try wp_auto)
  ipersist c
  wp_apply sync.Once.wp_Do $$ [$Honce]
  · iintro !> %Φ' ⟨HP, Hadd⟩ HΦ'
    (try wp_auto)
    wp_apply wp_broadcast_chan_close $$ [$HP] as -
    · itrivial
    (try wp_auto)
    wp_apply sync.tokJoin.WaitGroup.wp_Wait $$ [$Hadd] as -
    (try wp_auto)
    iapply HΦ'; itrivial
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end k8s
end EtcdGrove
end Perennial
