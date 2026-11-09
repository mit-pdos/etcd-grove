/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09): the proof of
`SyncRecorder__Events`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__Events
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
variable [sync_sem : sync.Assumptions]

theorem SyncRecorder.Events.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    SyncRecorder.Events.spec (GF := GF) (hG := hG) := by
  intro γt r L
  wp_start as ⟨#Hrec, Hf⟩
  iunfold isSyncRecorder at Hrec
  icases Hrec with ⟨-, #Hm⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply wp_Lock $$ [$Hsync $Hm] as ⟨Hlocked, Hinv⟩
  iunfold recLockInv at Hinv
  icases Hinv with ⟨%sl, %L', Hevs, #Hrep, Hcap, Ha⟩
  ihave %HL := traceAuth_frag_agree γt L' L $$ Ha Hf
  subst HL
  iunfold traceEventsRep at Hrep
  icases Hrep with ⟨%gs, #Hgs, #Hgl⟩
  try wp_auto
  ihave Hnil := ownSlice_nil (V := TracingEvent) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := TracingEvent) (GF := GF)
  wp_apply wp_slice_append slice.nil ([] : List TracingEvent) sl gs DFrac.discard $$ [$Hnil $Hncap $Hgs]
    as %out ⟨Hout, -, -⟩
  imod ownSlice_persist $$ Hout with #Hout
  try wp_auto
  wp_apply wp_Unlock _ (recLockInv γt r) $$ [$Hsync $Hm $Hlocked Hevs Ha Hcap]
  · iunfold recLockInv
    iexists sl, L'
    iframe
    iunfold traceEventsRep
    iexists gs
    iframe Hgs Hgl
  try wp_auto
  iapply HΦ
  iframe Hf
  iunfold traceEventsRep
  iexists gs
  iframe Hgl
  simp only [List.nil_append]
  iexact Hout

end proof

end TraceCheck
end EtcdGrove
end Perennial
