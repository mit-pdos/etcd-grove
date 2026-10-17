/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/newPeriodic.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]
variable [package_sem_ctx : context.Assumptions]
theorem v3compactor.newPeriodic.wp_proof
    (wp_getRetentions : v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG)) :
    v3compactor.newPeriodic.spec (GF := GF) (hG := hG) := by
  intro lg clk h interval rg c
  wp_start as ⟨Hcci, %Hh⟩
  iapply wp_fupd
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  iStructNamedPrefix «$r0» "A"
  -- the window, `make([]int64, 0, pc.getRetentions())`
  wp_apply wp_getRetentions $$ [$Aperiod] as Aperiod
  · ipureintro; exact Hh
  have hpos := pdRetentions_pos h Hh
  wp_apply wp_slice_make3 (V := w64) (W64 0) (pdRetentions h) ⟨by word, by word⟩ as %sl ⟨Hsl, Hcap, -⟩
  rw [List.replicate_zero]
  try wp_auto
  -- the context
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Hctxp $Hcci]
    as %ictx %γi %cancel ⟨#Hcancel, #Hictx, #Hcc⟩
  ihave #Hcancel' : context.cancelSpec (GF := GF) cancel γi iprop(True) $$ [Hcancel]
  · iunfold context.cancelSpec; iexact Hcancel
  try wp_auto
  -- the mutex over `paused`, and one of its reader tokens
  imod sync.init_RWMutex (pdLockInv (hG := hG) «$r0_ptr») (pdMuAddr «$r0_ptr») $$ [Apaused] Amu
    with Htoks
  · inext
    iunfold pdLockInv
    iexists _
    iframe
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨Int.toNat sync.rwmutex.actualMaxReaders - 1, by have := sync.actualMaxReaders_pos; omega⟩
  rw [hm, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, -⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  ihave Hsl := ownSlice_persist _ _ _ $$ Hsl
  imod Hsl
  ipersist Alg
  ipersist Aclock
  ipersist Aperiod
  ipersist Ainterval
  ipersist Arg
  ipersist Ac
  ipersist Actx
  ipersist Acancel
  imodintro
  iapply HΦ
  iunfold isPeriodic
  iunfold cancellableCtxAt
  iunfold pdRevs
  iunfold pdReader
  iframe #
  iframe
  try (iexists sl; iframe)
  try iframe #

end proof

end EtcdGrove
end Perennial
