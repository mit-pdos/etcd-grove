/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactBarrier
public import Spec.context.Err
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- (M2, the storage side, item 17) The fields are read through the running job's share; a
cancelled context means the scheduler stopped, whose payload is the stop channel closed
(`stopPayAt_done`), so the receive is ready and the re-scheduling branch dead: `NewJob` and
`Schedule` are not called (their specs stay the hypotheses of the linked call graph). -/
theorem mvcc.store.compactBarrier.wp_proof
    (h0 : context.Err.spec (GF := GF) (hG := hG))
    (h1 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h2 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG)) :
    mvcc.store.compactBarrier.spec (GF := GF) (hG := hG) := by
  intro s γ ctx cd ch Q q o
  wp_start as ⟨Hfs, #Hctx, #HPD, Hcl, #HQ⟩
  wp_auto
  ipersist s
  ipersist ch
  -- `ctx.Err()`: `nil` (`todoCtx`'s), or an error of a cancelled context, whose `PDone` holds
  ihave #Herr : iprop(□ ∀ Ψ : val → IProp GF, ▷ (∀ err : GoInterface,
      (if err = interface.nil then iprop(True) else iprop(□ cd.PDone)) -∗ Ψ #err) -∗
      WP (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #())) {{ Ψ }}) $$ []
  · iunfold mvcc.barrierCtx at Hctx
    icases Hctx with (%Htodo | #Hic)
    · subst Htodo
      iintro !> %Ψ HΨ
      wp_method_call
      wp_auto
      wp_method_call
      wp_auto
      iapply HΨ
      simp only [↓reduceIte]
      itrivial
    · ihave #HE := h0 ctx cd Broadcast.Unknown $$ Hic
      iintro !> %Ψ HΨ
      iapply HE
      · itrivial
      inext
      iintro %err Hm -
      iapply HΨ
      by_cases he : err = interface.nil
      · simp only [he, ↓reduceIte]; itrivial
      · simp only [he, ↓reduceIte]
        icases Hm with ⟨#Hd, -⟩
        iexact Hd
  icases mvcc.fieldShareAt_acc s γ q o $$ Hfs with ⟨Hflds, #Hph, Hfclose⟩
  ihave #Hph' := Hph
  iunfold mvcc.physOk at Hph'
  iNamed Hph'
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  try simp only
  wp_apply Herr as %err Hm
  cases err with
  | nil =>
    -- not cancelled: `close(ch)`
    wp_auto
    iunfold mvcc.compactCloser at Hcl
    icases Hcl with ⟨%γc, Hcl⟩
    wp_apply wp_broadcast_chan_close $$ [$Hcl] as -
    · iexact HQ
    (try wp_auto)
    iapply HΦ
    iapply Hfclose
    iunfold mvcc.storeFields
    simp only [named]
    iframe
  | ok e =>
    -- cancelled: the scheduler was stopped, so its payload holds: the stop channel is closed
    simp only [reduceCtorEq, ↓reduceIte]
    icases Hm with #Hdone
    ihave #Hsp := HPD $$ Hdone
    ihave #Hcl' := mvcc.stopPayAt_done γ.sx γ.sch o $$ [$Hpay $Hsp]
    wp_auto_lc 1
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcl' with ⟨%γst, #Hsc⟩
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)]
        iprop(mvcc.compactCloser ch Q ∗ (True -∗ Φ #())) $$ [] [Hcl HΦ Hfclose Hfb Hfidx Hfsch Hfstop] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨Hcl, HΦ⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, o.sstop, γst
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan $$ Hsc
      iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hsc
      isplit
      · iintro -
        wp_auto
        iapply HΦ
        itrivial
      · itrivial
    · iframe Hcl
      iintro -
      (try wp_auto)
      iapply HΦ
      iapply Hfclose
      iunfold mvcc.storeFields
      simp only [named]
      iframe
    · iintro - ⟨⟨⟩, -⟩

end proof

end EtcdGrove
end Perennial
