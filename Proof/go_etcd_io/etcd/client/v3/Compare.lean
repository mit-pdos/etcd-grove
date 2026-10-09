/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Compare.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__ensureCompare
public import Spec.go_etcd_io.etcd.client.v3.mustInt64
public import Spec.go_etcd_io.etcd.client.v3.mustInt64orLeaseID
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Compare.wp_proof (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_ensureCompare : Cmp.ensureCompare.spec (GF := GF) (hG := hG))
    (wp_mustInt64 : mustInt64.spec (GF := GF) (hG := hG))
    (wp_mustInt64orLeaseID : mustInt64orLeaseID.spec (GF := GF) (hG := hG)) :
    Compare.spec (GF := GF) (hG := hG) := by
  intro c m result op v x
  wp_start as ⟨#Hc, %Hop, %Harg⟩
  unfold cmpOpOf at Hop
  have Hr : (result = go!"=" ∧ op = .eq) ∨ (result ≠ go!"=" ∧ result = go!"!=" ∧ op = .neq) ∨
      (result ≠ go!"=" ∧ result ≠ go!"!=" ∧ result = go!">" ∧ op = .gt) ∨
      (result ≠ go!"=" ∧ result ≠ go!"!=" ∧ result ≠ go!">" ∧ result = go!"<" ∧ op = .lt) := by
    by_cases h1 : result = go!"="
    · rw [if_pos h1] at Hop; cases Hop; exact Or.inl ⟨h1, rfl⟩
    rw [if_neg h1] at Hop
    by_cases h2 : result = go!"!="
    · rw [if_pos h2] at Hop; cases Hop; exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
    rw [if_neg h2] at Hop
    by_cases h3 : result = go!">"
    · rw [if_pos h3] at Hop; cases Hop; exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, rfl⟩))
    rw [if_neg h3] at Hop
    by_cases h4 : result = go!"<"
    · rw [if_pos h4] at Hop; cases Hop
      exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, rfl⟩))
    rw [if_neg h4] at Hop; cases Hop
  clear Hop
  iapply wp_fupd
  wp_auto
  rcases Hr with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, h3, h4, rfl⟩
  all_goals (simp only [*, decide_true, decide_false, etcdserverpb.Compare_EQUAL,
    etcdserverpb.Compare_NOT_EQUAL, etcdserverpb.Compare_GREATER, etcdserverpb.Compare_LESS,
    etcdserverpb.Compare_VALUE, etcdserverpb.Compare_VERSION, etcdserverpb.Compare_CREATE,
    etcdserverpb.Compare_MOD, etcdserverpb.Compare_LEASE]; wp_auto)
  all_goals (
    wp_apply wp_Clone $$ [$cmp $Hc] as %c' ⟨cmp, %Hnn, Hown⟩
    try wp_auto
    wp_apply wp_ensureCompare $$ [$cmp] as cmp
    · iframe %
    unfold compareOwn
    icases Hown with ⟨%ksl, %esl, %u, Hres, #Htgt, #Hkey, #Hks, Hend, #Hes, Hu, #Hua⟩
    ihave %Hcn := typedPointsto_not_null _ _ _ $$ cmp
    iStructNamed cmp
    try wp_auto)
  all_goals (
    obtain ⟨key, rangeEnd, tgt, op0, num, val⟩ := m
    unfold cmpArgOf at Harg
    cases tgt <;> dsimp only [CmpTarget.code] at Harg ⊢
    case value =>
      obtain ⟨sv, rfl, rfl⟩ := Harg
      try wp_auto
      wp_apply wp_string_to_bytes sv as %vsl ⟨Hvs, -⟩
      try wp_auto
      wp_alloc w as Hw
      try wp_auto
      ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iStructNamed Hw
      ipersist Hvs
      ipersist Value
      ipersist Hres
      ipersist Hend
      ipersist Hu
      imodintro
      iapply HΦ
      unfold cmpAt compareAt compareUnionAt
      dsimp only [compareM, CmpTarget.code, CmpOp.code]
      isplitl []
      · ipureintro; exact Hnn
      iexists ksl, esl, interface.mkOk etcdserverpb.Compare_Value.ty.PointerType #w
      iframe #
      ipureintro; exact Or.inr rfl
    case version =>
      obtain ⟨n, hv, rfl⟩ := Harg
      try wp_auto
      wp_apply wp_mustInt64 $$ [$Hpkg]
      · ipureintro
        rcases hv with rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) |
            exact Or.inr rfl
      iintro -
      try wp_auto
      wp_alloc w as Hw
      try wp_auto
      ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iStructNamed Hw
      ipersist Version
      ipersist Hres
      ipersist Hend
      ipersist Hu
      imodintro
      iapply HΦ
      unfold cmpAt compareAt compareUnionAt
      dsimp only [compareM, CmpTarget.code, CmpOp.code]
      isplitl []
      · ipureintro; exact Hnn
      iexists ksl, esl, interface.mkOk etcdserverpb.Compare_Version.ty.PointerType #w
      iframe #
      ipureintro; exact Or.inr rfl
    case create =>
      obtain ⟨n, hv, rfl⟩ := Harg
      try wp_auto
      wp_apply wp_mustInt64 $$ [$Hpkg]
      · ipureintro
        rcases hv with rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) |
            exact Or.inr rfl
      iintro -
      try wp_auto
      wp_alloc w as Hw
      try wp_auto
      ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iStructNamed Hw
      ipersist CreateRevision
      ipersist Hres
      ipersist Hend
      ipersist Hu
      imodintro
      iapply HΦ
      unfold cmpAt compareAt compareUnionAt
      dsimp only [compareM, CmpTarget.code, CmpOp.code]
      isplitl []
      · ipureintro; exact Hnn
      iexists ksl, esl, interface.mkOk etcdserverpb.Compare_CreateRevision.ty.PointerType #w
      iframe #
      ipureintro; exact Or.inr rfl
    case mod =>
      obtain ⟨n, hv, rfl⟩ := Harg
      try wp_auto
      wp_apply wp_mustInt64 $$ [$Hpkg]
      · ipureintro
        rcases hv with rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) |
            exact Or.inr rfl
      iintro -
      try wp_auto
      wp_alloc w as Hw
      try wp_auto
      ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iStructNamed Hw
      ipersist ModRevision
      ipersist Hres
      ipersist Hend
      ipersist Hu
      imodintro
      iapply HΦ
      unfold cmpAt compareAt compareUnionAt
      dsimp only [compareM, CmpTarget.code, CmpOp.code]
      isplitl []
      · ipureintro; exact Hnn
      iexists ksl, esl, interface.mkOk etcdserverpb.Compare_ModRevision.ty.PointerType #w
      iframe #
      ipureintro; exact Or.inr rfl
    case lease =>
      obtain ⟨n, hv, rfl⟩ := Harg
      try wp_auto
      wp_apply wp_mustInt64orLeaseID $$ [$Hpkg]
      · ipureintro
        rcases hv with rfl | rfl | rfl <;>
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) |
            exact Or.inr rfl
      iintro -
      try wp_auto
      wp_alloc w as Hw
      try wp_auto
      ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
      · iapply typedPointsto_combine _ _ _ Hcn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      try wp_auto
      iStructNamed Hw
      ipersist Lease
      ipersist Hres
      ipersist Hend
      ipersist Hu
      imodintro
      iapply HΦ
      unfold cmpAt compareAt compareUnionAt
      dsimp only [compareM, CmpTarget.code, CmpOp.code]
      isplitl []
      · ipureintro; exact Hnn
      iexists ksl, esl, interface.mkOk etcdserverpb.Compare_Lease.ty.PointerType #w
      iframe #
      ipureintro; exact Or.inr rfl)


end proof

end EtcdGrove
end Perennial
