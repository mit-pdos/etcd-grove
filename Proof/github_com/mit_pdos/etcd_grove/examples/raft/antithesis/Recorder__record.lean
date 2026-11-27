/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Recorder__record.lean`, as the trace
check's `SyncRecorder.TraceEvent`: under the lock, the report appended to the recorded slice; the
caller's receipts join the lock's (their sum bounds the new stream, `Stream.Fits`), and the caller's
atomic update fires against the lock's half of the stream before the lock is released.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder__record
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

/-- The linearization point: the caller's atomic update fired against the lock's half, both
halves appended `ev`. -/
private theorem record_commit (γr : GName) (evs : List AntCheck.Event) (ev : AntCheck.Event)
    (Q : IProp GF) (hfit : Stream.Fits GF (evs ++ [ev])) :
    ghostVar (GF := GF) γr (1 : Qp).half evs -∗
      (AU <{ ∃∃ evs', recAuth (GF := GF) γr evs' }> @ ⊤, ∅
        <{ recAuth γr (evs' ++ [ev]) ∗ ⌜Stream.Fits GF (evs' ++ [ev])⌝, COMM Q }>) ={⊤}=∗
      ghostVar γr (1 : Qp).half (evs ++ [ev]) ∗ Q := by
  iintro Hl Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%evs', Hc, Hclose⟩
  unfold recAuth
  ihave %Heq := ghostVar_agree (GF := GF) γr evs (1 : Qp).half evs' (1 : Qp).half $$ Hl Hc
  subst Heq
  imod ghostVar_update_halves (GF := GF) (evs ++ [ev]) γr evs evs $$ Hl Hc with ⟨Hl, Hc⟩
  icases Hclose with ⟨-, Hcom⟩
  imod Hcom $$ [Hc] with HQ
  · iframe Hc; ipureintro; exact hfit
  imodintro
  iframe

theorem Recorder.record.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Recorder.record.spec (GF := GF) (hG := hG) := by
  intro γr r p ev Q
  wp_start as ⟨#Hrec, #Hev, Hr1, Hau⟩
  iunfold isRecorder at Hrec
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Lock $$ [$Hsync $Hrec] as ⟨Hlocked, Hinv⟩
  iunfold recLockInv at Hinv
  icases Hinv with ⟨%sl, %evs, Hevs, #Hrep, Hcap, Ha, Hrs⟩
  ihave Hrs := (receipt_add _ _).2 $$ [Hrs Hr1]
  · iframe
  ihave %Hfit := receipt_lt _ $$ Hrs
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  iunfold AntCheck.eventsRO at Hrep
  icases Hrep with ⟨%ps, #Hps, #Hpl⟩
  wp_apply wp_slice_append_dfrac sl ps DFrac.discard _ [p] (DFrac.own 1) $$ [$Hps $Hcap $Hsl1]
    as %sl' ⟨Hsl', Hcap, -⟩
  · ipureintro; exact DFrac.valid_discard
  try wp_auto
  imod record_commit γr evs ev Q (by
      unfold Stream.Fits
      simpa [List.map_append, List.sum_append] using Hfit) $$ Ha Hau with ⟨Ha, HQ⟩
  wp_apply wp_Unlock _ (recLockInv γr r) $$ [$Hsync $Hrec $Hlocked Hevs Ha Hsl' Hcap Hrs]
  · iunfold recLockInv
    iexists sl', evs ++ [ev]
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    iframe
    iunfold AntCheck.eventsRO
    iexists ps ++ [p]
    iframe Hsl'
    iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hpl Hev
  try wp_auto
  iapply HΦ
  iexact HQ

end proof

end AntHarness
end EtcdGrove
end Perennial
