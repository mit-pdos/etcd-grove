/-
Proof of `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessageWalSnap.lean`, over the part's
`proto.MarshalPb.spec` at the registered `pbSnapC` (`pbSnapC_reg`), as the main tree's
`pbutil.MustMarshalMessage.wp_proof`; the non-nil result from the encoding's non-emptiness
(`snapEnc_ne_of_index`: `Index` is set). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessageWalSnap
public import LinuxFs.Spec.google_golang_org.protobuf.proto.MarshalPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

theorem go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.wp_proofWalSnap (Mr : WalMarshal)
    (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specWalSnap (GF := GF) Mr := by
  intro sp sm cs hsz
  wp_start as #Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%c, #Hro, %Hc⟩
  obtain ⟨-, hi, -, -, he⟩ := Hc
  have hs : snapSize c < 2 ^ 48 := by unfold snapSize; rw [he]; exact hsz
  have hne : snapEnc c ≠ [] := snapEnc_ne_of_index c (by simp [hi])
  wp_auto
  have wpM := wp_Marshal pbSnapC pbSnapC_reg sp c trivial hs
  simp only [pbSnapC_ty, pbSnapC_roC, pbEncC_pbSnapC, he] at wpM
  wp_apply wpM $$ [] as %d ⟨Hd, Hcap⟩
  · iframe #
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hd
  iapply HΦ
  iframe
  ipureintro
  rintro rfl
  apply hne
  rw [he]
  apply List.eq_nil_of_length_eq_zero
  rw [Hlen.1]; simp [slice.nil]

end proof

end EtcdGrove
end Perennial
