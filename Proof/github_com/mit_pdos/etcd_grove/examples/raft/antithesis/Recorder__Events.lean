/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Recorder__Events.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__Events
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [sync_sem : sync.Assumptions]


theorem Recorder.Events.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Recorder.Events.spec (GF := GF) (hG := hG) := by
  intro γr r evs
  wp_start as ⟨#Hrec, Hdone⟩
  iunfold isRecorder at Hrec
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Lock $$ [$Hsync $Hrec] as ⟨Hlocked, Hinv⟩
  iunfold recLockInv at Hinv
  icases Hinv with ⟨%sl, %evs', Hevs, #Hrep, Hcap, Ha, Hrs⟩
  iunfold recDone at Hdone
  iunfold recAuth at Hdone
  ihave %Heq := ghostVar_agree (GF := GF) γr evs (1 : Qp).half evs' (1 : Qp).half $$ Hdone Ha
  subst Heq
  iunfold AntCheck.eventsRO at Hrep
  icases Hrep with ⟨%ps, #Hps, #Hpl⟩
  ihave %Hl := ownSlice_len $$ Hps
  try wp_auto
  wp_apply wp_slice_make2 (V := Loc) sl.len $$ [] as %out ⟨Hout, -⟩
  · ipureintro; exact Hl.2
  try wp_auto
  wp_apply wp_slice_copy out _ sl ps DFrac.discard $$ [$Hout $Hps] as %n ⟨-, Hout, -⟩
  have hps : List.take (List.replicate (sint.nat sl.len) (zero_val Loc)).length ps ++
      List.drop ps.length (List.replicate (sint.nat sl.len) (zero_val Loc)) = ps := by
    simp [← Hl.1]
  rw [hps]
  imod ownSlice_persist $$ Hout with #Hout
  try wp_auto
  wp_apply wp_Unlock _ (recLockInv γr r) $$ [$Hsync $Hrec $Hlocked Hevs Ha Hcap Hrs]
  · iunfold recLockInv
    iexists sl, evs
    iframe
    iunfold AntCheck.eventsRO
    iexists ps
    iframe Hps Hpl
  try wp_auto
  iapply HΦ
  isplitr [Hdone]
  · iunfold AntCheck.eventsRO
    iexists ps
    iframe Hout Hpl
  iunfold recDone; iunfold recAuth; iexact Hdone

end proof

end AntHarness
end EtcdGrove
end Perennial
