/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/copyMsg.lean`. Lean-first (no Rocq
counterpart).

The composite literal takes the source's field cells (persistent `cellRO`s), its `Context` slice
(read-only bytes) and a fresh `Entries` slice (`append` onto `nil`: its elements and capacity
owned, the entries read-only), with no snapshot and no responses: an owned message
(`msgPtsC_of_struct`). A snapshot, if any, is then cloned (`proto.CloneSnapshot`) and stored.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.copyMsg
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Proof.go_etcd_io.raft.v3.InvPbMsg

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem copyMsg.wp_proof
    (wp_Clone : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    copyMsg.spec (GF := GF) (hG := hG) := by
  intro l dq dqe cap st
  wp_start as Hm
  iunfold msgPtsC at Hm
  iNamed Hm
  try wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnilc : ownSliceCap (GF := GF) Loc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  wp_apply wp_slice_append slice.nil ([] : List Loc) es els dqe $$ [$Hnil $Hnilc $Hes]
    as %es' ⟨Hes', Hcap', Hes⟩
  try wp_auto
  rw [List.nil_append]
  ihave Hrnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod msgPtsC_of_struct _ _ (DFrac.own 1) true els { st with resps := [], snap := none } ⊤ rfl
    $$ [$«$r0» $Hes' $Hrnil Hcap'] with Hc
  · iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs
    simp only [snapOpt, ↓reduceIte]
    iframe Hcap'
  cases Hs : st.snap with
  | none =>
    simp only [snapOpt]
    icases Hsn with %Hps
    subst Hps
    try wp_auto
    iapply HΦ
    iframe Hc
    iunfold msgPtsC
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, null, cs, rs, uf
    simp only [Hs, snapOpt]
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
    ipureintro; exact Hnn
  | some sv =>
    simp only [snapOpt]
    iunfold ownSnapM at Hsn
    icases Hsn with ⟨%ds, %pm, %uf', %Hpsn, HD, Hd, HM, Hm, #Hpbs⟩
    ihave Hsn : ownSnapM ps dq sv $$ [HD Hd HM Hm]
    · iunfold ownSnapM
      iexists ds, pm, uf'
      iframe
      iframe Hpbs
      ipureintro; exact Hpsn
    ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
    · iPkgInit
    try wp_auto
    simp only [Hpsn, decide_false, Bool.not_false]
    try wp_auto
    wp_apply wp_Clone.1 ps dq sv $$ [$Hproto $Hsn] as %p' ⟨Hsn, Hsn'⟩
    ihave Hm : msgPtsC l dq dqe cap st $$ [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn
      Hsn HCx HRs Hrs]
    · iunfold msgPtsC
      iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
      simp only [Hs, snapOpt]
      iframe
      iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
      ipureintro; exact Hnn
    iunfold msgPtsC at Hc
    iNamed Hc
    try wp_auto
    iapply HΦ
    iframe Hm
    iunfold msgPtsC
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, p', cs, rs, uf
    simp only [snapOpt]
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
    ipureintro; exact Hnn

end proof

end kvreconf
end EtcdGrove
end Perennial
