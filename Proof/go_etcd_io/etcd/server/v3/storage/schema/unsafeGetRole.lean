/-
Proof of `Spec/.../schema/unsafeGetRole.lean`: the point read of the name through the reader's contract, `proto.Unmarshal` of its value (the trust boundary: `Spec/google_golang_org/protobuf/proto/UnmarshalRole.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeGetRole
public import Spec.google_golang_org.protobuf.proto.UnmarshalRole

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

theorem schema.unsafeGetRole.wp_proof
    (hUnm : proto.UnmarshalRole.spec (GF := GF) (hG := hG)) :
    schema.unsafeGetRole.spec (GF := GF) (hG := hG) := by
  intro lg r name H D hlg hwf
  wp_start as ⟨#Hrd, HH⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, ⟨%rb, #HRoles, -⟩, -⟩
  iunfold schema.authReader at Hrd
  icases Hrd with ⟨-, -, #HU⟩
  iunfold schema.authPointSpec at HU
  wp_auto
  wp_apply wp_string_to_bytes name as %key ⟨Hkey, -⟩
  (try wp_auto)
  wp_apply HU $$ [$HRoles $HH $Hkey] as %ks %vs ⟨HH, -, #Hv⟩
  (try wp_auto)
  unfold schema.roleOutDX schema.pointValsA
  cases hl : D.roles.lookup name with
  | none =>
    ihave %Hlen := ownSlice_len _ _ _ $$ Hv
    have hl0 : vs.len = W64 0 := by simp only [List.length_nil] at Hlen; word
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      iframe HH
      ipureintro; rfl
    · exfalso; exact Hif hl0
  | some v =>
    icases Hv with ⟨%s, #Hvs, #Hacc⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    have hl1 : vs.len = W64 1 := by simp only [List.length_singleton] at Hlen; word
    wp_if_destruct
    · exfalso; rw [hl1] at Hif; exact absurd Hif (by decide)
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl1]; decide))]
    wp_apply wp_load_slice_index vs (sint.Z (W64 0)) [s] DFrac.discard s (by decide) $$ [Hvs] as _
    · iframe Hvs; ipureintro; rfl
    (try wp_auto)
    icases Hacc $$ HH with ⟨%dq, Hs, HHback⟩
    obtain ⟨x, rfl⟩ := hwf name v hl
    wp_apply (hUnm s x _ _ dq) $$ [$Hs $«$r0»] as ⟨Hs, Hu⟩
    ihave HH := HHback $$ Hs
    (try wp_auto)
    iapply HΦ
    iframe HH
    iexists x
    iframe Hu
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
