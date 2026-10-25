/-
Proof of `Spec/go_etcd_io/etcd/client/v3/validateChannelKey.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.validateChannelKey
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem validateChannelKey.wp_proof
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    validateChannelKey.spec (GF := GF) (hG := hG) := by
  intro k
  wp_start as -
  ihave Hi : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, -, -, -, -, ⟨%eRCK, #Hrck, #HrckE⟩⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [$Hsl] as %err ⟨-, #Herr⟩
    · iframe #; fmt_args_ok; iright; ileft
      unfold go_etcd_io.etcd.cache.v3.errorStringSpec fmt.stringMethodSpec at *
      iexact HrckE
    iapply HΦ
    simp only [_root_.true_or, ↓reduceIte]
    iexists err
    isplitr
    · ipureintro; rfl
    unfold go_etcd_io.etcd.cache.v3.errorStringSpec fmt.stringMethodSpec at *
    iexact Herr
  · have h1 := Hif
    wp_if_destruct
    · wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Errorf $$ [$Hsl] as %err ⟨-, #Herr⟩
      · iframe #; fmt_args_ok; iright; ileft
        unfold go_etcd_io.etcd.cache.v3.errorStringSpec fmt.stringMethodSpec at *
        iexact HrckE
      iapply HΦ
      simp only [_root_.or_true, ↓reduceIte]
      iexists err
      isplitr
      · ipureintro; rfl
      unfold go_etcd_io.etcd.cache.v3.errorStringSpec fmt.stringMethodSpec at *
      iexact Herr
    · iapply HΦ
      have hnot : ¬ (k = go!"" ∨ k = go!"default") := not_or.2 ⟨h1, Hif⟩
      simp only [hnot, ↓reduceIte]
      ipureintro; trivial

end proof

end EtcdGrove
end Perennial
