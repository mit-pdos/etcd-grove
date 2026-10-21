/-
Proof of `Spec/go_etcd_io/etcd/client/v3/filterCallOptions.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.filterCallOptions

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem filterCallOptions.wp_proof :
    filterCallOptions.spec (GF := GF) (hG := hG) := by
  intro sl vs
  wp_start as ⟨#Hsl, #Hvs⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (ov : GoInterface) (gsl rsl : GoSlice) (gs : List GoInterface)
      (ros : List go_etcd_io.etcd.client.v3.retryOption),
      "i" ∷ i_ptr ↦ n ∗ "opt" ∷ opt_ptr ↦ ov ∗
      "grpcOptions" ∷ grpcOptions_ptr ↦ gsl ∗ "Hg" ∷ gsl ↦* gs ∗
      "Hgc" ∷ ownSliceCap GoInterface gsl (DFrac.own 1) ∗
      "retryOptions" ∷ retryOptions_ptr ↦ rsl ∗ "Hr" ∷ rsl ↦* ros ∗
      "Hrc" ∷ ownSliceCap go_etcd_io.etcd.client.v3.retryOption rsl (DFrac.own 1) ∗
      "%Hgs" ∷ ⌜∀ v ∈ gs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧
        t ∈ grpcScalarOptTys⌝ ∗
      "#Hros" ∷ ([∗list] ro ∈ ros, retryApplyOk ro.applyFunc') ∗
      "%Hnone" ∷ ⌜(∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧
        t ∈ grpcScalarOptTys) → ros = []⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i opt grpcOptions retryOptions]
  · iexists W64 0, _, slice.nil, slice.nil, [], []
    simp only [named]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    isplitl
    · ipureintro; intro v hv; cases hv
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl
    · first | itrivial | (ipureintro; simp)
    ipureintro; constructor <;> word
  iunfold callOptsOk at Hvs
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) v sl DFrac.discard vs Hn.1 Hv $$ Hsl with ⟨#Hve, -⟩
    ihave #Hco := BigSepL.bigSepL_lookup (Φ := fun _ (w : GoInterface) => callOptOk (GF := GF) w)
      Hv $$ Hvs
    wp_auto
    iunfold callOptOk at Hco
    icases Hco with (%Hsc | ⟨%ro, %Hvro, #Hap⟩)
    · obtain ⟨t, x, rfl, Ht⟩ := Hsc
      have Htne : t ≠ go_etcd_io.etcd.client.v3.retryOption.ty := by
        simp only [grpcScalarOptTys, List.mem_cons, List.not_mem_nil, _root_.or_false] at Ht
        rcases Ht with rfl | rfl | rfl | rfl <;>
          (intro h
           simp [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty,
             google_golang_org.grpc.MaxSendMsgSizeCallOption.ty,
             google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty, go_etcd_io.etcd.client.v3.retryOption.ty] at h)
      simp only [interface.mkOk, Htne, ↓reduceIte, decide_false]
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok ⟨t, x⟩]
      isplitr
      · ipureintro; rfl
      iintro %lp ⟨Hl, -⟩
      wp_apply wp_slice_append $$ [$Hg $Hgc $Hl] as %gsl' ⟨Hg', Hgc', -⟩
      wp_for_post
      iframe
      iexists n + W64 1, _, gsl', rsl, gs ++ [GoInterface.ok ⟨t, x⟩], ros
      simp only [named]
      iframe
      iframe #
      ipureintro
      refine ⟨?_, Hnone, by constructor <;> word⟩
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact Hgs w hw
      · simp only [List.mem_singleton] at hw
        exact ⟨t, x, hw, Ht⟩
    · subst Hvro
      simp only [interface.mkOk, ↓reduceIte, _root_.decide_true]
      wp_auto
      wp_apply wp_slice_literal (V := go_etcd_io.etcd.client.v3.retryOption) [ro]
      isplitr
      · ipureintro; rfl
      iintro %lp ⟨Hl, -⟩
      wp_apply wp_slice_append $$ [$Hr $Hrc $Hl] as %rsl' ⟨Hr', Hrc', -⟩
      wp_for_post
      iframe
      iexists n + W64 1, _, gsl, rsl', gs, ros ++ [ro]
      simp only [named]
      iframe
      isplitr
      · ipureintro; exact Hgs
      isplitr
      · iapply BigSepL.bigSepL_append.2
        iframe #
        iapply BigSepL.bigSepL_nil.2
        itrivial
      isplitr
      · -- a retry option among `vs`: not all scalar
        ipureintro
        intro hall
        exfalso
        obtain ⟨t, x, he, ht⟩ := hall _ (List.mem_of_getElem? Hv)
        simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at he
        obtain ⟨rfl, -⟩ := he
        simp only [grpcScalarOptTys, List.mem_cons, List.not_mem_nil, _root_.or_false] at ht
        rcases ht with h | h | h | h <;>
          simp [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty,
            google_golang_org.grpc.MaxSendMsgSizeCallOption.ty,
            google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty, go_etcd_io.etcd.client.v3.retryOption.ty] at h
      ipureintro
      constructor <;> word
  · iapply HΦ
    iexists gs, ros
    iframe
    iframe #
    ipureintro; exact ⟨Hgs, Hnone⟩

end proof

end EtcdGrove
end Perennial
