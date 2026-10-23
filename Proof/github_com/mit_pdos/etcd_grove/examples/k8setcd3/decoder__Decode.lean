module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder__Decode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.decodeObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem decoder.Decode.wp_proof (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG)) :
    decoder.Decode.spec (GF := GF) (hG := hG) := by
  intro sl dq d p name val rv rev
  wp_start as ⟨Hs, Hp⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, ⟨%eD, #HeD, #HsD⟩, -⟩
  (try wp_auto)
  wp_apply wp_decodeObj $$ [$Hs] as %n %v %ok ⟨Hs, %Hd⟩
  cases hdec : decodeD d with
  | none =>
    rw [hdec] at Hd
    subst Hd
    (try wp_auto)
    iapply HΦ
    simp only
    iframe Hs Hp
    isplitr
    · ipureintro; nofun
    iunfold go_etcd_io.etcd.cache.v3.errStrOk
    imodintro
    iintro %e %he
    cases he
    iexact HsD
  | some nv =>
    rcases nv with ⟨n', v'⟩
    rw [hdec] at Hd
    obtain ⟨rfl, rfl, rfl⟩ := Hd
    (try wp_auto)
    iapply HΦ
    simp only
    (try isimp only at Hp)
    iframe Hs Hp

end proof

end k8setcd3
end EtcdGrove
end Perennial
