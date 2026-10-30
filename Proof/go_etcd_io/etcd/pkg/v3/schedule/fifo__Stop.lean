/-
`(*fifo).Stop`. Lean-first (2026-10-22, the scheduler translated with its body).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__Stop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 schedule

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- Under the lock, the scheduler not yet stopped (a second `Stop` would bring a second stop
token): the `stopped` flag set, the context cancelled (`cancel` with `stopped`), `f.cancel` set to
`nil` and the stop token and the queue left in the lock invariant; then `<-f.donec` returns once
the worker has closed it. -/
theorem schedule.fifo.Stop.wp_proof : schedule.fifo.Stop.spec (GF := GF) (hG := hG) := by
  intro l γ F Ps
  wp_start as ⟨#Hf, Htok, HqS⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold fifoIs at Hf
  iNamed Hf
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold fifoLockInv at HI
  iNamed HI
  icases Hst with (⟨%Hcf, Hst⟩ | ⟨%Hcf, #Hstp, Htok', Hq'⟩)
  rotate_left
  · -- already stopped: two stop tokens
    iunfold schedStopTok at Htok Htok'
    icases Htok with ⟨%n, #Hn, Hd⟩
    icases Htok' with ⟨%n', #Hn', Hd'⟩
    iunfold schedStopName at Hn Hn'
    ihave %Hnn := mono_list_idx_agree γ.jobs 0 n n' $$ Hn Hn'
    subst Hnn
    ihave %Hv := dghostVar_valid_2 n () (DFrac.own 1) () (DFrac.own 1) $$ Hd Hd'
    exact absurd Hv.1 (dfrac_own_one_op_invalid _)
  subst Hcf
  (try wp_auto)
  -- the `stopped` flag: half persisted (`stopped`), half kept (the baton's taker's mark)
  imod dghostVar_update true F.st false $$ Hst with Hst
  ihave ⟨Hst, Hmark⟩ := dghostVar_split F.st true (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) $$ [Hst]
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hst
  imod dghostVar_persist F.st (1 : Qp).half true $$ Hst with #Hstp
  ihave #Hstp' : stopped F $$ []
  · iunfold stopped; iexact Hstp
  iunfold _root_.Perennial.context.cancelSpec at Hcancel
  wp_apply Hcancel $$ [] as -
  · iexact Hstp'
  (try wp_auto)
  iunfold schedQueue at HqS
  ihave %HPs := monoListAuthOwn_agree γ.jobs _ _ Ps L $$ HqS Hq
  obtain ⟨-, rfl⟩ := HPs
  -- the queue's half: a quarter to the lock invariant, a quarter kept
  ihave ⟨HqS, HqK⟩ := (monoListAuthOwn_fractional γ.jobs Ps).fractional (1 : Qp).half.half
    (1 : Qp).half.half |>.1 $$ [HqS]
  · rw [Qp.half_add_half]; iexact HqS
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hbaton
    Htok HqS]
  · inext
    iunfold fifoLockInv
    iexists sl, js, items, rs, Ps, b, func.nil, sc, fn
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact Hjs
    iright
    iframe
    iframe #
  (try wp_auto)
  -- `<-f.donec`: returns once the worker has closed it, with the last tracked job's `Post`
  wp_bind (App (Val (chan.receive _)) (Val #F.dch))
  wp_apply_core chan.wp_receive (V := Unit) F.dch F.γd $$ Hdch
  iintro -
  unfold recvAu
  clear Hjs
  iinv Hdinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold donecInv at Hi
  icases Hi with (Hch | ⟨Hch, Hdc, Hcar⟩)
  · iexists .Buffered []
    iframe Hch
  · iexists .Closed []
    iframe Hch
    dsimp only
    iintro Hch
    iunfold donecCarry at Hcar
    icases Hcar with ⟨%L', %q', Hqa, (Hbt | Hm)⟩
    rotate_left
    · -- taken already: three parts of the `stopped` flag
      icombine Hmark Hm as Hst1
      ihave %Hv := dghostVar_valid_2 F.st true (DFrac.own 1) true DFrac.discard $$ Hst1 Hstp
      exact absurd Hv.1 (dfrac_own_one_op_invalid _)
    ihave %HL := monoListAuthOwn_agree γ.jobs _ _ Ps L' $$ HqK Hqa
    obtain ⟨-, rfl⟩ := HL
    imod Hmask with -
    imod Hclose $$ [Hch Hdc Hqa Hmark] with -
    · inext; iunfold donecInv; iright; iframe
      iunfold donecCarry
      iexists Ps, q'
      iframe
    imodintro
    wp_auto
    iapply HΦ
    iunfold baton at Hbt
    icases Hbt with ⟨%p, %Q, %Hp, #HQs, HQ⟩
    have Hlast : Ps.getLast? = some p := by
      rw [List.getLast?_eq_getElem?]; exact Hp
    rw [Hlast]
    iexists Q
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
