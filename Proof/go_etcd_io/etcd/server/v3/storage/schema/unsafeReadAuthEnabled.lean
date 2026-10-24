/-
Proof of `Spec/.../schema/unsafeReadAuthEnabled.lean`: the point read of `authEnabled` through the reader's contract, `bytes.Equal` with `authEnabled` (`[]byte{1}`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.unsafeReadAuthEnabled.wp_proof :
    schema.unsafeReadAuthEnabled.spec (GF := GF) (hG := hG) := by
  intro r H D
  wp_start as ⟨#Hrd, HH⟩
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%ab, #HAuth, -⟩, -, -, ⟨%sae, #HAE, #HAEb⟩, -, ⟨%sen, #HEn, #HEnb⟩, -⟩
  iunfold schema.authReader at Hrd
  icases Hrd with ⟨#HA, -, -⟩
  iunfold schema.authPointSpec at HA
  ihave #HAEk : (sae ↦*□ schema.authEnabledKey : IProp GF) $$ []
  · unfold schema.authEnabledKey; iexact HAEb
  wp_auto
  wp_apply HA $$ [$HAuth $HH $HAEk] as %ks %vs ⟨HH, -, #Hv⟩
  (try wp_auto)
  unfold schema.enabledOf schema.pointValsA
  cases hl : D.auth.lookup schema.authEnabledKey with
  | none =>
    ihave %Hlen := ownSlice_len _ _ _ $$ Hv
    have hl0 : vs.len = W64 0 := by simp only [List.length_nil] at Hlen; word
    wp_if_destruct
    · exfalso; rw [hl0] at Hif; exact absurd Hif (by decide)
    (try wp_auto)
    iapply HΦ
    iframe HH
    ipureintro; simp
  | some v =>
    icases Hv with ⟨%s, #Hvs, #Hacc⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    have hl1 : vs.len = W64 1 := by simp only [List.length_singleton] at Hlen; word
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl1]; decide))]
      wp_apply wp_load_slice_index vs (sint.Z (W64 0)) [s] DFrac.discard s (by decide) $$ [Hvs] as _
      · iframe Hvs; ipureintro; rfl
      (try wp_auto)
      icases Hacc $$ HH with ⟨%dq, Hs, HHback⟩
      wp_apply (bytes.wp_Equal s sen dq DFrac.discard v [W8 1]) $$ [$Hs $HEnb] as ⟨Hs, -⟩
      ihave HH := HHback $$ Hs
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        iapply HΦ
        iframe HH
        ipureintro; simpa using Hif
      · (try wp_auto)
        iapply HΦ
        iframe HH
        ipureintro; simpa using Hif
    · exfalso; exact Hif hl1

end proof

end EtcdGrove
end Perennial
