/- Lean-first (no Rocq counterpart).

# `(*server).Fail`'s proof

Both errors have `v` as their description: `errors.New(v)`'s (`errStr_descIs`) and
`status.Error(codes.NotFound, v)`'s (its spec); `failSpec`'s `Ψe v` is the error outcome.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Fail
public import Spec.google_golang_org.grpc.status.Error
public import Perennial.Spec.strings.HasPrefix
public import Perennial.Proof.errors.NewVar
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem server.Fail.wp_proof (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG))
    (wp_status_Error : EtcdGrove.status.Error.spec (GF := GF) (hG := hG)) :
    server.Fail.spec (GF := GF) (hG := hG) := by
  intro s ctx r v md Φ Ψe
  wp_start as ⟨Hrecv, HΨ⟩
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hgs : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  isimp only [pbStringValueT, pbStringValue] at Hrecv
  icases Hrecv with ⟨%Hnn, %Hlen, #Hval⟩
  isimp only [failSpec] at HΨ
  try wp_auto
  wp_apply wp_HasPrefix v go!"p" $$ [$Hstr]
  by_cases hp : go!"p" <+: v
  · rw [decide_eq_true hp]
    try wp_auto
    wp_apply _root_.Perennial.errors.wp_New_errorString v as %x ⟨#-, #Hx⟩
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; simp [interface.mkOk]
    isplitl [HΨ]
    · unfold handlerErrOut
      iexists v
      isplitr
      · iapply svc.errStr_descIs $$ Hx
      · iintro %_
        iexact HΨ
    · iapply svc.errStr_srvErrOk $$ Hx
  · rw [decide_eq_false hp]
    try wp_auto
    wp_apply wp_status_Error (W32 5) v as %err ⟨%Hne, #Hse, #Hd, -, -⟩
    · ipureintro
      simp only [google_golang_org.grpc.codes.OK]
      exact fun h => absurd (go.intoVal_inj h) (by decide)
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; exact Hne
    isplitl [HΨ]
    · unfold handlerErrOut
      iexists v
      iframe Hd
      iintro %_
      iexact HΨ
    · iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hse

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
