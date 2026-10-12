module
public import Spec.go_etcd_io.bbolt.DB__getPageSize
public import Proof.go_etcd_io.bbolt.ErrShape

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]

theorem DB.getPageSize.wp_proof
    (hFirst : DB.getPageSizeFromFirstMeta.spec (GF := GF) (hG := hG))
    (hSecond : DB.getPageSizeFromSecondMeta.spec (GF := GF) (hG := hG)) :
    DB.getPageSize.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs ps dq Hbl
  wp_start as ⟨Hf, Hps, #Hof, Hfb⟩
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  icases bboltError_access errors.ErrInvalid (by simp [bboltErrorNames]) $$ Hei
    with ⟨%e, #He, %Hne⟩
  wp_auto
  wp_apply hFirst dbl f fd bs ps dq $$ [Hf Hps Hfb] as %sz1 %cr1 %err1 ⟨Hf, Hps, Hfb, %H1⟩
  · iframe; iframe #
  try wp_auto
  cases err1 with
  | nil =>
    -- the first meta is valid
    rcases H1 with ⟨-, -, hl, hv, hs⟩ | ⟨h, -⟩
    · try wp_auto
      iapply HΦ
      iframe
      ipureintro
      left
      exact ⟨rfl, Or.inl ⟨hl, hv, hs⟩⟩
    · exact absurd rfl h
  | ok ei1 =>
    try wp_auto
    wp_apply hSecond dbl f fd bs ps dq Hbl $$ [Hf Hps Hfb] as %sz2 %cr2 %err2 ⟨Hf, Hps, Hfb, %H2⟩
    · iframe; iframe #
    try wp_auto
    cases err2 with
    | nil =>
      rcases H2 with ⟨-, hi⟩ | ⟨h, -⟩
      · try wp_auto
        iapply HΦ
        iframe
        ipureintro
        left
        exact ⟨rfl, Or.inr (Or.inl hi)⟩
      · exact absurd rfl h
    | ok ei2 =>
      try wp_auto
      obtain ⟨t', p', rfl⟩ := Hne
      cases cr1 <;> cases cr2
      all_goals
        try wp_auto
        iapply HΦ
        iframe
        ipureintro
        first
          | exact Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩
          | exact Or.inr ⟨fun h => (by cases h), errWF_ptr _ _⟩

end proof

end bbolt
end EtcdGrove
end Perennial
