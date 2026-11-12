/-
Proof of `Spec/.../schema/unsafeReadAuthRevision.lean`: the point read of `authRevision` through the reader's contract, `binary.BigEndian.Uint64` of its 8 bytes. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthRevision
public import Spec.encoding.binary.bigEndian__Uint64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.unsafeReadAuthRevision.wp_proof
    (hU : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)) :
    schema.unsafeReadAuthRevision.spec (GF := GF) (hG := hG) := by
  intro r H D hwf
  wp_start as ⟨#Hrd, HH⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%ab, #HAuth, -⟩, -, -, -, ⟨%sar, #HAR, #HARb⟩, -, -⟩
  iunfold schema.authReader at Hrd
  icases Hrd with ⟨#HA, -, -⟩
  iunfold schema.authPointSpec at HA
  ihave #HARk : (sar ↦*□ schema.authRevisionKey : IProp GF) $$ []
  · unfold schema.authRevisionKey; iexact HARb
  wp_auto
  wp_apply HA $$ [$HAuth $HH $HARk] as %ks %vs ⟨HH, -, #Hv⟩
  (try wp_auto)
  unfold schema.revisionOf schema.pointValsA
  cases hl : D.auth.lookup schema.authRevisionKey with
  | none =>
    ihave %Hlen := ownSlice_len _ _ _ $$ Hv
    have hl0 : vs.len = W64 0 := by simp only [List.length_nil] at Hlen; word
    wp_if_destruct
    · exfalso; rw [hl0] at Hif; exact absurd Hif (by decide)
    (try wp_auto)
    iapply HΦ
    iframe HH
    ipureintro; rfl
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
      have hU' := hU s v [] dq (hwf v hl)
      rw [List.append_nil] at hU'
      wp_apply hU' $$ [$Hs] as Hs
      ihave HH := HHback $$ Hs
      (try wp_auto)
      iapply HΦ
      iframe HH
      ipureintro; rfl
    · exfalso; exact Hif hl1

end proof

end EtcdGrove
end Perennial
