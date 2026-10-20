/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/witnessRead__Update.lean`. Lean-first (2026-10-20,
witness support).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.witnessRead__Update

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- Under the lock, the state stored is compared with the read's by identity: the same, it is
the read's state (`whsRO_agree`), the caller's shift runs and `q` is stored; else the error. -/
theorem witnessRead.Update.wp_proof : witnessRead.Update.spec (GF := GF) (hG := hG) := by
  intro r s P p σ N q σ' Ψ
  wp_start as ⟨#Hr, #Hq, Hsh⟩
  iunfold isWRead at Hr
  icases Hr with ⟨#Hrs, #Hrst, #Hp, #Hw⟩
  iunfold isWStore at Hw
  icases Hw with ⟨#Hmu, #Herr⟩
  iunfold wErrOk at Herr
  icases Herr with ⟨%e, #He, %Hene⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold wStoreLock at HR
  icases HR with ⟨%p0, %σ0, Hst, #Hp0, HP⟩
  wp_auto
  wp_if_destruct
  · -- the read's state: run the caller's shift, store `q`
    subst Hif
    ihave %Hag := whsRO_agree p0 σ0 σ $$ []
    · iframe #
    subst Hag
    ihave Hsh' := Hsh $$ HP
    imod (fupd_mask_mono (P := iprop(P σ' ∗ Ψ)) (E1 := ⊤ \ ↑N) (E2 := ⊤) CoPset.subseteq_top) $$ Hsh'
      with ⟨HP, HΨ⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HP]
    · inext
      unfold wStoreLock
      iexists q, σ'
      iframe
      iframe #
    iapply HΦ
    ileft
    iframe HΨ
    ipureintro; rfl
  · -- another update took: the error, the shift handed back
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HP]
    · inext
      unfold wStoreLock
      iexists p0, σ0
      iframe
      iframe #
    iapply HΦ
    iright
    iframe Hsh
    ipureintro; exact Hene

end proof

end kv
end EtcdGrove
end Perennial
