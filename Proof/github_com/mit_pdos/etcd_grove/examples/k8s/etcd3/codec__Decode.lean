module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec__Decode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem codec.Decode.wp_proof (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG)) :
    codec.Decode.spec (GF := GF) (hG := hG) := by
  intro sl dq d
  wp_start as Hs
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, ⟨%eD, #HeD, #HsD, -⟩, -⟩
  (try wp_auto)
  wp_alloc po as Hpo
  (try wp_auto)
  wp_apply wp_decodeObj $$ [$Hs] as %w %ok ⟨Hs, %Hd⟩
  cases hdec : decodeD d with
  | none =>
    rw [hdec] at Hd
    subst Hd
    (try wp_auto)
    iapply HΦ
    simp only
    iframe Hs
    isplitr
    · ipureintro; nofun
    iunfold go_etcd_io.etcd.cache.v3.errStrOk
    imodintro
    iintro %e %he
    cases he
    isplitr
    · iexact HsD
    · have hF := go.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format"
      have hE := go.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Error"
      simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hF hE
      ipureintro; exact ⟨hF, hE⟩
  | some w' =>
    rw [hdec] at Hd
    obtain ⟨rfl, rfl⟩ := Hd
    (try wp_auto)
    iapply HΦ
    simp only
    iframe Hs
    isplitr
    · ipureintro; trivial
    iexists po
    isplitr
    · ipureintro; rfl
    iExactEq Hpo
    rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
