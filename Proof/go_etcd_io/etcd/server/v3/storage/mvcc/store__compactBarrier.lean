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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.compactBarrier.wp_proof
    (h0 : context.Err.spec (GF := GF) (hG := hG))
    (h1 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h2 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG)) :
    mvcc.store.compactBarrier.spec (GF := GF) (hG := hG) := by
  intro s γ ctx cd ch Q
  iloeb as IH generalizing %ctx %cd
  wp_start as ⟨#Hs, #Hstop, #Hctx, Hcl, #HQ⟩
  wp_auto
  ipersist s
  ipersist ch
  -- `ctx.Err()`: some error (`todoCtx`'s is `nil`)
  ihave #Herr : iprop(□ ∀ Ψ : val → IProp GF, ▷ (∀ err : GoInterface, Ψ #err) -∗
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
    · ihave #HE := h0 ctx cd Broadcast.Unknown $$ Hic
      iintro !> %Ψ HΨ
      iapply HE
      · itrivial
      inext
      iintro %err - -
      iapply HΨ
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  wp_apply Herr as %err
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
    itrivial
  | ok e =>
    -- cancelled: unless the store is stopped, another barrier, under `s.mu`
    wp_auto
    ihave #Hstop' := Hstop
    iunfold mvcc.storeStop at Hstop'
    icases Hstop' with ⟨%c0, #Hc0, #Hsc⟩
    icombine Hstopc Hc0 gives %Heq
    subst Heq
    iunfold mvcc.isStopChan at Hsc
    icases Hsc with ⟨%γst, #Hsc⟩
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
        iprop(mvcc.compactCloser ch Q ∗ (True -∗ Φ #())) $$ [] [Hcl HΦ] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨Hcl, HΦ⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sstop, γst
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
      · iintro -
        iframe
    · iframe
    · iintro ⟨Hcl, HΦ⟩ -
      ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
      · iPkgInit
      ihave #Hschp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
      · iPkgInit
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
      wp_func_lits
      (try wp_auto)
      wp_apply h1 γ.sch _ _ iprop(mvcc.compactCloser ch Q ∗ □ Q) iprop(True) iprop(True) $$ []
        as %j #Hj
      · iframe #
        iunfold schedule.jobFnSpec
        iintro !> %ctx' %cd' !> %Φj ⟨Hrun, ⟨Hcl', #HQ'⟩, -, #Hctx'⟩ HΦj
        wp_auto
        rw [method_unfold (t := go.GoType.PointerType store.ty) (m := go!"compactBarrier")]
        wp_apply IH $$ %ctx' %cd' [$Hcl']
        · iframe #
          iunfold mvcc.barrierCtx
          iright
          iexact Hctx'
        (try wp_auto)
        iapply HΦj
        iframe Hrun
      (try wp_auto)
      ihave #HisS := HisSched
      iunfold schedule.isScheduler at HisS
      icases HisS with ⟨#Hfifo, #Hlive⟩
      ihave #Hfifo' := Hfifo
      iunfold schedule.isFifo at Hfifo'
      icases Hfifo' with ⟨%Hnn, -⟩
      cases ssched with
      | nil => exact absurd rfl Hnn
      | ok sci =>
        wp_auto
        wp_apply h2 sci γ.sch j iprop(mvcc.compactCloser ch Q ∗ □ Q) iprop(True) iprop(True) none
          $$ [Hcl] as -
        · iframe #
          iframe Hcl
          simp only [schedule.schedPre]
          iframe #
          ipureintro; trivial
        (try wp_auto)
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HmuP]
        (try wp_auto)
        iapply HΦ
        itrivial

end proof

end EtcdGrove
end Perennial
