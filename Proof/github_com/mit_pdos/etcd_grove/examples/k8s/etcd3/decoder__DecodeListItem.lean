/- Lean-first (no Rocq counterpart). Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/decoder__DecodeListItem.lean`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder__DecodeListItem
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeObj

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem decoder.DecodeListItem.wp_proof (wp_decodeObj : decodeObj.spec (GF := GF) (hG := hG)) :
    decoder.DecodeListItem.spec (GF := GF) (hG := hG) := by
  intro ctx dsl d rev nf
  wp_start as ⟨#Hd, #Hnf⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, ⟨%eD, #HeD, #HsD, -⟩, -⟩
  (try wp_auto)
  iunfold newItemOk at Hnf
  wp_bind (App (Val #nf) _)
  iapply Hnf
  inext
  iintro %x Hx
  simp only [driverSpec] at *
  iunfold objAtD at Hx
  icases Hx with ⟨%p, %n, %Hxp, Hp⟩
  obtain ⟨rfl, hp, -⟩ := Hxp
  (try wp_auto)
  wp_apply wp_decodeObj $$ [$Hd] as %w %ok ⟨-, %Hdw⟩
  cases hdec : decodeD d with
  | none =>
    rw [hdec] at Hdw
    subst Hdw
    (try wp_auto)
    iapply HΦ
    rw [decodeObjD_none d hdec]
    simp only
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
      simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hF
      ipureintro; exact hF
  | some w' =>
    rw [hdec] at Hdw
    obtain ⟨rfl, rfl⟩ := Hdw
    (try wp_auto)
    iapply HΦ
    rw [decodeObjD_of d w hdec]
    simp only
    isplitr
    · ipureintro; trivial
    iunfold objAtD
    iexists p, rev
    rw [DObj.ofObj_toObj_rv w _ (decodeD_some d w hdec).2.2.2 rev]
    iframe Hp
    ipureintro; simp [hp]

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
