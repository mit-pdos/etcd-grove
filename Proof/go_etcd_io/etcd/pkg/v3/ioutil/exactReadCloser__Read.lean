/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/ioutil/exactReadCloser__Read.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.exactReadCloser__Read

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem ioutil.exactReadCloser.Read.wp_proof : ioutil.exactReadCloser.Read.spec (GF := GF) (hG := hG) := by
  intro e rc R Buf k br total p
  wp_start as ⟨He, #Hrd, HR, HB⟩
  wp_auto
  iunfold readerSpec at Hrd
  wp_apply Hrd $$ %k %p [HR HB] as %n %err ⟨HR, HB, %Hn⟩
  · iframe HR HB
  ihave Hei : (go_etcd_io.etcd.pkg.v3.ioutil.ioutilInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hei with ⟨%e1, %e2, #Hshort, #Hexp, -⟩
  wp_if_destruct
  · iapply HΦ
    iexists n, err
    iframe He HR HB
    isplitr
    · ipureintro; exact Hn
    iunfold exactReadResult
    ileft
    iframe Hexp
    ipureintro; exact ⟨by omega, rfl⟩
  wp_if_destruct
  · wp_if_destruct
    · iapply HΦ
      iexists (W64 0), err
      isplitl [He]
      · iexact He
      isplitl [HR]
      · iexact HR
      isplitl [HB]
      · iexact HB
      isplitr
      · ipureintro; exact Hn
      iunfold exactReadResult
      iright; ileft
      iframe Hshort
      ipureintro; exact ⟨Hif, rfl, rfl⟩
    · iapply HΦ
      iexists n, err
      iframe He HR HB
      isplitr
      · ipureintro; exact Hn
      iunfold exactReadResult
      iright; iright
      ipureintro
      exact ⟨by omega, fun h => Hif h.2, rfl, rfl⟩
  · iapply HΦ
    iexists n, err
    iframe He HR HB
    isplitr
    · ipureintro; exact Hn
    iunfold exactReadResult
    iright; iright
    ipureintro
    exact ⟨by omega, fun h => Hif h.1, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
