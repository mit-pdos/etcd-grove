/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09): the proof of
`SyncRecorder__TraceEvent`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__TraceEvent
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

theorem SyncRecorder.TraceEvent.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    SyncRecorder.TraceEvent.spec (GF := GF) (hG := hG) := by
  intro γt r p e Q
  wp_start as ⟨#Hrec, #Hev, Hau⟩
  iunfold isSyncRecorder at Hrec
  icases Hrec with ⟨-, #Hm⟩
  icases tracingEventRep_val p e $$ Hev with ⟨%g, #Hp, #Hg⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Lock $$ [$Hsync $Hm] as ⟨Hlocked, Hinv⟩
  iunfold recLockInv at Hinv
  icases Hinv with ⟨%sl, %L, Hevs, #Hrep, Hcap, Ha⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  iunfold traceEventsRep at Hrep
  icases Hrep with ⟨%gs, #Hgs, #Hgl⟩
  wp_apply wp_slice_append_dfrac sl gs DFrac.discard _ [g] (DFrac.own 1) $$ [$Hgs $Hcap $Hsl1]
    as %sl' ⟨Hsl', Hcap, -⟩
  · ipureintro; exact DFrac.valid_discard
  try wp_auto
  imod traceAuth_commit γt L e Q $$ Ha Hau with ⟨Ha, HQ⟩
  wp_apply wp_Unlock _ (recLockInv γt r) $$ [$Hsync $Hm $Hlocked Hevs Ha Hsl' Hcap]
  · iunfold recLockInv
    iexists sl', L ++ [e]
    iframe
    iunfold traceEventsRep
    iexists gs ++ [g]
    iframe Hsl'
    iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hgl Hg
  try wp_auto
  iapply HΦ
  iexact HQ

end proof

end TraceCheck
end EtcdGrove
end Perennial
