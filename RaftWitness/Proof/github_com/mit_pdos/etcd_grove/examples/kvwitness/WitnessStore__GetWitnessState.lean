/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/WitnessStore__GetWitnessState.lean`. Lean-first (2026-10-20,
witness support).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.WitnessStore__GetWitnessState

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

/-- Under the lock: the caller's shift on the state stored, and a read of it (its two fields
never written: persistent). -/
theorem WitnessStore.GetWitnessState.wp_proof :
    WitnessStore.GetWitnessState.spec (GF := GF) (hG := hG) := by
  intro s P N Ψ
  wp_start as ⟨#Hw, Hsh⟩
  ihave #Hw' := Hw
  iunfold isWStore at Hw'
  icases Hw' with ⟨#Hmu, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold wStoreLock at HR
  icases HR with ⟨%p0, %σ0, Hst, #Hp0, HP⟩
  ihave Hsh' := Hsh $$ %σ0 HP
  imod (fupd_mask_mono (P := iprop(P σ0 ∗ Ψ σ0)) (E1 := ⊤ \ ↑N) (E2 := ⊤) CoPset.subseteq_top) $$ Hsh'
    with ⟨HP, HΨ⟩
  wp_auto
  iStructNamed «$r0»
  ipersist s
  ipersist state
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HP]
  · inext
    unfold wStoreLock
    iexists p0, σ0
    iframe
    iframe #
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists «$r0_ptr», p0, σ0
  iframe HΨ
  isplitr
  · ipureintro; rfl
  unfold isWRead
  iframe s state Hp0 Hw

end proof

end kv
end EtcdGrove
end Perennial
