/-
**The auth realization meets `authSchemaSrv` and `authSchemaSnap`** (auth-schema-srv A6 (e), 2026-11-19): at boot,
the tickets' authority allocated and discarded (`ticketN` tickets `ownToks γt 1`, the read resource `R`), the store's
publication vault (V-pub, `vault_alloc`) from the succession right, the premise's half of the published index split
into the realization's quarter and the post's `authPubTok`, and the realization created (`real_create`) at the boot
state over the empty auth buckets; at a snapshot, the vault's quarter (`vault_take`) and a new realization at the
buckets' state. The contracts are the realization's (`real_backendOk`, `real_wBoot`, `real_wAtHook`,
`real_createAuthBuckets`, `real_bkLend`, `real_life`). The boot's critical section is the hook-less one (`f = nil`,
`P = Pk`), whose `Post` is the caller's open share `qo`. Lean-first (no Rocq counterpart).

The statements take the backend's and schema's package initialization (`authSchemaSrv`'s text has none) and the
receipt bound: the link (A7) discharges them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealNew
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealRd
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

section srv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The realization's open share as a rest and `authRdN` slot shares. -/
theorem authOpenQ_rep : ∃ q0 s0 : Qp, authOpenQ = qpRep q0 s0 authRdN := by
  have hN : 0 < authRdN := by unfold authRdN; omega
  refine ⟨authOpenQ.half, authOpenQ.half.divide_even authRdN hN, ?_⟩
  rw [Qp.ext_iff, qpRep_val, Qp.val_divide_even]
  have hN' : (authRdN : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [Rat.mul_comm, Rat.div_mul_cancel hN']
  simp only [Qp.val_half]
  grind

/-- **The empty auth buckets hold the boot state.** -/
theorem viewAt_boot {r : GMap GoString BktData}
    (h : (r.lookup go!"auth").getD ∅ = ∅ ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅) :
    viewAt ⟨auth.bootState, auth.bootState, auth.bootState⟩
      ⟨bktOf r go!"auth", bktOf r go!"authUsers", bktOf r go!"authRoles"⟩ := by
  obtain ⟨ha, hu, hr⟩ := h
  simp only [bktOf, ha, hu, hr]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun _ => default, ?_, ?_⟩, ⟨fun _ => default, ?_, ?_⟩⟩ <;>
    simp [schema.enabledOf, schema.revisionOf, schema.revWf, auth.bootState]

/-- **The snapshot clause** (`authSchemaSnap`) at the tickets `ownToks γt 1`, over the store's vault `γv`. -/
theorem real_snap
    (hLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (hDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (hPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (hDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (hSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (hSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hBTs : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hFCs : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (hGUb : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (hGRb : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (hGAb : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (hGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (hRTs : schema.authBackend.ReadTx.spec (GF := GF) (hG := hG))
    (hRLs : schema.authReadTx.RLock.spec (GF := GF) (hG := hG))
    (hRUs : schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hGUt : schema.authReadTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGRt : schema.authReadTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEnt : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRevt : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGAt : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (γa : auth.AuthNames) (γt γv : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      ownTokAuthDfrac γt DFrac.discard ticketN ∗ vaultInv γa γv ⊢
      authSchemaSnap γa (ownToks γt 1) := by
  iintro ⟨#Hp1, #Hp2, #Ht, #Hvi⟩
  iunfold authSchemaSnap
  iintro !> %lg %abl %d %W %Pk %f %r %st %- %Hat %- #Habl %hT #Hb #Hpl %Hf Hro Hsl Hq HI Hs
  iunfold auth.authLockI at HI
  icases HI with ⟨%hs, Hlq, %hl⟩
  ihave Hlq := (show auth.authLockShare (GF := GF) (.on γa) hs ⊢ auth.authLockQ γa hs from .rfl) $$ Hlq
  simp only [auth.histLast] at hl
  imod vault_take γa γv hs $$ [$Hvi $Hs $Hlq] with ⟨%p, Hpq, Hlv, Hlq, %hp⟩
  obtain ⟨q0, s0, hq⟩ := authOpenQ_rep
  imod real_create γa γt γv d s0 q0 hq st hs p r hl hp (bucketsAt_viewAt Hat) hT
    $$ [$Ht $Hpq $Hlv $Hq $Hsl $Hro $Hlq] with ⟨%γ, %hγ, #Hinv, HT, Hcur⟩
  obtain ⟨ha, ht, hv⟩ := hγ
  subst ha ht hv
  ihave #Hbe := real_BE hRT hRL hRU hURr hFEr hID hName hSafe γ d s0 q0 W Pk hT $$ [$Hp1 $Hp2 $Hb $Hinv]
  ihave #Hwh := real_wAtHook hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hBTs hFCs hGUb hGRb hGAb hGARs hBT hFC hRT hRL hRU hURr hFEr hLI hUL hCm hUP hDel hUR hFE hID hName hSafe hRB γ d s0 q0 hT $$ [$Hp1 $Hp2 $Hinv]
  imodintro
  iexists γ.γc
  isplitr
  · iapply real_backendOk hRTs hRLs hRUs hGUt hGRt hEnt hRevt hGAt γ d s0 q0 abl lg $$ [$Hp2 $Hinv $Habl $Hbe]
  iframe Hcur HT
  isplitr
  · iunfold authWAtHook at Hwh
    iapply Hwh $$ %abl %lg %W %Pk %f Habl Hb Hpl %Hf
  iframe Hwh
  isplitr
  · iapply real_bkLend γ d s0 q0 $$ Hinv
  iapply real_life γ d s0 q0 hq $$ [$Hinv $Hvi]

/-- **`authSchemaSrv` holds** of the realization. -/
theorem real_srv
    (hLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (hDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (hPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (hDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (hSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (hSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hBTs : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hFCs : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (hGUb : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (hGRb : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (hGAb : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (hGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (hRTs : schema.authBackend.ReadTx.spec (GF := GF) (hG := hG))
    (hRLs : schema.authReadTx.RLock.spec (GF := GF) (hG := hG))
    (hRUs : schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hGUt : schema.authReadTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGRt : schema.authReadTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEnt : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRevt : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGAt : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hCABs : schema.authBackend.CreateAuthBuckets.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ⊢
      authSchemaSrv (GF := GF) := by
  iintro ⟨#Hp1, #Hp2⟩
  iunfold authSchemaSrv
  iintro !> %γa %lg %abl %d %W %Pk %qo %r %- %Hr #Habl %hT #Hb Hqo Hq Hsl Hhk Hro Hs HI Hpub
  -- the tickets: `ticketN` of them, the authority discarded
  imod (ownTokAuth_alloc (GF := GF)) with ⟨%γt, Ha⟩
  imod ownTokAuth_add ticketN γt 0 $$ Ha with ⟨Ha, Htk⟩
  ihave Ha := (show ownTokAuth (GF := GF) γt (0 + ticketN) ⊢ ownTokAuth γt ticketN by rw [Nat.zero_add]) $$ Ha
  ipersist Ha
  -- the vault, and the published index's quarters
  imod vault_alloc γa $$ Hs with ⟨%γv, #Hvi, Hlv⟩
  iunfold auth.authPubQ at Hpub
  ihave Hpub : monoNatAuthOwn γa.pub ((1 : Qp).half.half + (1 : Qp).half.half) 0 $$ [Hpub]
  · rw [Qp.half_add_half]; iexact Hpub
  icases ((monoNatAuthOwn_fractional γa.pub 0).fractional (1 : Qp).half.half (1 : Qp).half.half).1 $$ Hpub
    with ⟨Hpq, Hpt⟩
  ihave Hpq := (show monoNatAuthOwn (GF := GF) γa.pub (1 : Qp).half.half 0 ⊢ auth.authPubQ γa (1 : Qp).half.half 0
    from .rfl) $$ Hpq
  -- the history at the boot state
  iunfold auth.authLockI at HI
  icases HI with ⟨%hs, Hlq, %hl⟩
  ihave Hlq := (show auth.authLockShare (GF := GF) (.on γa) hs ⊢ auth.authLockQ γa hs from .rfl) $$ Hlq
  simp only [auth.histLast] at hl
  obtain ⟨q0, s0, hq⟩ := authOpenQ_rep
  imod real_create γa γt γv d s0 q0 hq auth.bootState hs 0 r hl (getLast_len hl) (viewAt_boot Hr) hT
    $$ [$Ha $Hpq $Hlv $Hq $Hsl $Hro $Hlq] with ⟨%γ, %hγ, #Hinv, HT, Hcur⟩
  obtain ⟨ha, ht, hv⟩ := hγ
  subst ha ht hv
  ihave #Hbe := real_BE hRT hRL hRU hURr hFEr hID hName hSafe γ d s0 q0 W Pk hT $$ [$Hp1 $Hp2 $Hb $Hinv]
  imodintro
  iexists ownToks γ.γt 1, Pk, func.nil, backend.bOpen d.γB qo, iprop(Pk ∗ backend.bOpen d.γB qo),
    backend.bOpen d.γB qo, γ.γc
  isplitr
  · iapply real_backendOk hRTs hRLs hRUs hGUt hGRt hEnt hRevt hGAt γ d s0 q0 abl lg $$ [$Hp2 $Hinv $Habl $Hbe]
  iframe Hcur
  isplitr
  · iapply real_wBoot hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hBTs hFCs hGUb hGRb hGAb hGARs hBT hFC
      hRT hRL hRU hURr hFEr hLI hUL hCm hUP hDel hUR hFE hID hName hSafe hRB γ d s0 q0 W Pk hT abl lg
    iframe #
  isplitr
  · iapply real_wAtHook hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hBTs hFCs hGUb hGRb hGAb hGARs hBT hFC hRT hRL hRU hURr hFEr hLI hUL hCm hUP hDel hUR hFE hID hName hSafe hRB γ d s0 q0 hT $$ [$Hp1 $Hp2 $Hinv]
  isplitr
  · iapply real_bkLend γ d s0 q0 $$ Hinv
  isplitr
  · iintro !>
    iapply real_createAuthBuckets hCABs hBT hLO hCB hUL hID hName hSafe hRB γ d s0 q0 W Pk hT abl lg
    iframe #
  iframe HT Hhk
  isplitl [Hpt]
  · iunfold auth.authPubTok; iexists 0; iunfold auth.authPubQ; iexact Hpt
  isplitr
  · iapply real_life γ d s0 q0 hq $$ [$Hinv $Hvi]
  isplitl [Hqo]
  · iunfold srvApi.csContractA
    iframe Hqo
    isplitl []
    · rw [mvcc.api.hookRun, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      iintro ⟨HP, HPre⟩; imodintro; iframe HP HPre
    · iintro ⟨HP, HPre⟩; imodintro; iframe HP HPre
  isplitl [Htk]
  · iapply (show ownToks (GF := GF) γ.γt ticketN ⊢ [∗list] _x ∈ List.replicate (authRdN - 1) (), ownToks γ.γt 1
      from sync.rwmutex.ownToks_replicate γ.γt ticketN) $$ Htk
  isplitr
  · iintro H; iexact H
  iapply real_snap hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hBTs hFCs hGUb hGRb hGAb hGARs hBT hFC hRT hRL hRU hURr hFEr hLI hUL hCm hUP hDel hUR hFE hID hName hSafe hRB hRTs hRLs hRUs hGUt hGRt hEnt hRevt hGAt γ.γa γ.γt γ.γv
  iframe #

end srv

end authReal
end EtcdGrove
end Perennial
