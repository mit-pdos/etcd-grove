/- Lean-first (no Rocq counterpart).

# `errOk`'s proof

`err == io.EOF` compares at the dynamic types (`go_eq_interface`): `io.EOF` is a `*errors.errorString`
(`io.eof_of_init`), which has no `GRPCStatus` (`ErrorStringNoGRPCStatus`), so a status error differs from
it, and `status.FromError` gives `ok = true` of it (T3); `io.EOF`'s own value is equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.errOk
public import Spec.google_golang_org.grpc.status.FromError
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

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
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem errOk.wp_proof (wp_FromError : status.FromError.spec (GF := GF) (hG := hG)) :
    errOk.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as ⟨#Hse, #Hsh⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, -⟩
  icases Hsh with (%Hg | #He)
  · obtain ⟨e, rfl, hm⟩ := Hg
    have hne : e.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty := by
      intro h; rw [h] at hm; exact ErrorStringNoGRPCStatus.noGRPCStatus hm
    try wp_auto
    simp only [interface.mkOk, hne, ↓reduceIte]
    try wp_auto
    ihave ⟨%m, #Hd⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
    ihave ⟨%c, #Hc⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_code _ $$ Hse
    wp_apply wp_FromError _ m c $$ [] as %s %ok ⟨-, -, -, -, -, %Hok⟩
    · iframe #
    have hok : ok = true := Hok ⟨e, rfl, hm⟩
    subst hok
    try wp_auto
    iapply HΦ
    itrivial
  · iunfold eofIs at He
    icombine Hpt He gives %Heq
    subst Heq
    try wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
