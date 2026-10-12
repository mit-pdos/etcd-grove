/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/copyKeyValue.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.copyKeyValue

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem copyKeyValue.wp_proof : copyKeyValue.spec (GF := GF) (hG := hG) := by
  intro c dq keysOnly
  wp_start as Hc
  unfold cachedKvOwn
  icases Hc with ⟨%Hnn, HK, #HKs, HC, HM, HV, HVal, #HVs, HL⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  ihave %HlenK := ownSlice_len _ _ _ $$ HKs
  wp_apply wp_slice_make2 (V := w8) $$ [] as %ksl ⟨Hksl, -⟩
  · ipureintro; exact HlenK.2
  wp_apply wp_slice_copy $$ [$Hksl $HKs] as %n ⟨%Hn, Hksl, -⟩
  have hk : (c.kv.key.take (List.replicate (sint.nat c.keySl.len) (zero_val w8)).length ++
      (List.replicate (sint.nat c.keySl.len) (zero_val w8)).drop c.kv.key.length) = c.kv.key := by
    simp [List.length_replicate, ← HlenK.1]
  rw [hk]
  ipersist Hksl
  cases keysOnly
  · simp only [Bool.not_false]
    wp_auto
    ihave %HlenV := ownSlice_len _ _ _ $$ HVs
    wp_apply wp_slice_make2 (V := w8) $$ [] as %vs ⟨Hvs, -⟩
    · ipureintro; exact HlenV.2
    wp_apply wp_slice_copy $$ [$Hvs $HVs] as %n2 ⟨%Hn2, Hvs, -⟩
    have hv : (c.kv.value.take (List.replicate (sint.nat c.valSl.len) (zero_val w8)).length ++
        (List.replicate (sint.nat c.valSl.len) (zero_val w8)).drop c.kv.value.length) =
        c.kv.value := by
      simp [List.length_replicate, ← HlenV.1]
    rw [hv]
    ipersist Hvs
    wp_alloc p as Hp
    ihave %Hpnn := typedPointsto_not_null $$ Hp
    iStructNamed Hp
    wp_auto
    iapply HΦ
    isplitl [HK HC HM HV HVal HL]
    · iframe; iframe #; ipureintro; exact Hnn
    iexists (CachedKv.mk p ksl vs c.kv)
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    ipureintro; simp [Hpnn]
  · simp only [Bool.not_true]
    wp_auto
    ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
    wp_alloc p as Hp
    ihave %Hpnn := typedPointsto_not_null $$ Hp
    iStructNamed Hp
    wp_auto
    iapply HΦ
    isplitl [HK HC HM HV HVal HL]
    · iframe; iframe #; ipureintro; exact Hnn
    iexists (CachedKv.mk p ksl slice.nil { c.kv with value := [] })
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    ipureintro; simp [Hpnn]

end proof

end leasing
end EtcdGrove
end Perennial
