/-
Proof of `pbutil.MustUnmarshalMessage.specWalSnap`
(`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ReadAllCallees.lean`), over the part's
`proto.UnmarshalPb.spec` at the registered `pbSnapC` (`pbSnapC_reg`), as the main tree's
`pbutil.MustUnmarshalMessagePb.wp_proof`: `U`'s coherence (`WalUnmarshal.SnapCoh`) makes the bytes
`snapEnc c` of a content `c` with valid unknown fields, so `Unmarshal` returns `nil` and the decoded
object is `snapOwnC sp c` (D2), which `snapOwnC_freeze` freezes into the read-only `walSnapIdTerm`.
(`snapOwnC_freeze` is a lemma of `proto.CloneWalSnap`'s proof module, imported for it: it belongs in
`walpb/PbSnapshot.lean`, moved there when that file is next edited.) Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import LinuxFs.Spec.google_golang_org.protobuf.proto.UnmarshalPb
public import LinuxFs.Proof.google_golang_org.protobuf.proto.CloneWalSnap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [pbutil_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

theorem go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage.wp_proofWalSnap (U : WalUnmarshal)
    (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage.specWalSnap (GF := GF) (hG := hG) U := by
  intro hU sp d dq bs s hs
  obtain ⟨c₀, hu, hbs, hc₀⟩ := hU bs s hs
  wp_start as ⟨Hb, Hd⟩
  iapply wp_fupd
  wp_auto
  have wpU := wp_Unmarshal pbSnapC pbSnapC_reg d bs dq sp
  simp only [pbSnapC_ty] at wpU
  wp_apply wpU $$ [Hd Hb] as %err ⟨Hd, %Hok, Hdec⟩
  · iframe; simp only [pbSnapC, pbSnapM]; iexact Hb
  have he : err = GoInterface.nil := Hok ⟨c₀, trivial, hu, hbs⟩
  subst he
  wp_auto
  ihave ⟨%c, Hm, %Hc⟩ := Hdec $$ %rfl
  obtain ⟨-, -, -, Heq⟩ := Hc
  have h0 := Heq c₀ trivial hu hbs
  subst h0
  imod snapOwnC_freeze sp c $$ Hm with #Hm
  imodintro
  iapply HΦ
  iframe
  unfold walSnapIdTerm
  iexists c
  iframe Hm
  ipureintro; exact hc₀

end proof

end EtcdGrove
end Perennial
