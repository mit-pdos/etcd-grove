-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/RawNodeSpecOfAbs.lean` (etc/copy-part.py; rerun it, do not edit).
/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.2. **The old `RawNode` specs from the
strengthened ones** (`RawNode.<F>.spec_of_abs.law`, `RawNodeAbsSpecs.lean`), for the six forms: the
pre's `ownRawNode` is an `ownRawNodeAt` outside the scope (`ownRawNode_at`), the strengthened triple at
`sc = false`, and the post's `ownRawNodeAt` forgets back (`ownRawNodeAt_ownRawNode`); `HasReady`'s
`false` arm keeps the conjunction's `ownRawNodeIdle`. Each function's proof file then proves its old
spec from its strengthened proof, so `Link.lean`'s linked results keep their statements.
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNodeAtLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem RawNode.HasReady.spec_of_abs : RawNode.HasReady.spec_of_abs.law (GF := GF) (hG := hG) := by
  intro Habs γ rn id rs
  wp_start_folded as H
  iNamed H
  icases ownRawNode_at γ rn id rs $$ Hrn with ⟨%ps, %qs, %ip, Hrn⟩
  wp_apply Habs none (fun _ h => by cases h) γ rn id rs ps qs ip $$ [$Hrn] as %b H
  icases H with (⟨%Hb, H⟩ | ⟨%Hb, -, ⟨H, -⟩⟩)
  · ihave H := ownRawNodeAt_ownRawNode γ rn id rs ps qs ip none $$ H
    iapply HΦ
    ileft
    iframe H
    ipureintro; exact Hb
  · iapply HΦ
    iright
    iframe H
    ipureintro; exact Hb

theorem RawNode.Tick.spec_of_abs : RawNode.Tick.spec_of_abs.law (GF := GF) (hG := hG) := by
  intro Habs γ rn id rs H1 H2 H3
  wp_start_folded as H
  iNamed H
  icases ownRawNode_at γ rn id rs $$ Hrn with ⟨%ps, %qs, %ip, Hrn⟩
  wp_apply Habs none (fun _ h => by cases h) γ rn id rs ps qs ip H1 H2 H3 $$ [$Hrn] as %t %ps' %ip' H
  iNamed H
  ihave Hrn := ownRawNodeAt_ownRawNode _ _ _ _ _ _ _ _ $$ Hrn
  iapply HΦ $$ %t
  iframe Hrn
  ipureintro; exact Ht

theorem RawNode.Propose.spec_of_abs : RawNode.Propose.spec_of_abs.law (GF := GF) (hG := hG) := by
  intro Habs γ rn id rs data_sl data H1
  wp_start_folded as H
  iNamed H
  icases ownRawNode_at γ rn id rs $$ Hrn with ⟨%ps, %qs, %ip, Hrn⟩
  wp_apply Habs none (fun _ h => by cases h) γ rn id rs ps qs ip data_sl data H1 $$ [$Hrn $Hdata $Hent $Htk] as %err %ps' %ip' H
  · ipureintro; exact Hmd
  iNamed H
  ihave Hrn := ownRawNodeAt_ownRawNode _ _ _ _ _ _ _ _ $$ Hrn
  iapply HΦ $$ %err
  iframe Hrn Herr

theorem RawNode.Step.spec_of_abs : RawNode.Step.spec_of_abs.law (GF := GF) (hG := hG) := by
  intro Habs γ rn id rs ml st H1 H2 H3 H4 H5
  wp_start_folded as H
  iNamed H
  icases ownRawNode_at γ rn id rs $$ Hrn with ⟨%ps, %qs, %ip, Hrn⟩
  wp_apply Habs none (fun _ h => by cases h) γ rn id rs ps qs ip ml st H1 (fun _ h => by cases h) H2 H3 H4 H5
    $$ [$Hrn $Hm $Hxfer $Hmsg $Hsnap $Hcred] as %err %t %ps' %ip' H
  iNamed H
  ihave Hrn := ownRawNodeAt_ownRawNode _ _ _ _ _ _ _ _ $$ Hrn
  iapply HΦ $$ %err %t
  iframe Hrn
  ipureintro; exact Ht

theorem RawNode.Advance.spec_of_abs : RawNode.Advance.spec_of_abs.law (GF := GF) (hG := hG) := by
  intro Habs γ rn id rs rd H1 H2 H3
  wp_start_folded as H
  iNamed H
  icases ownRawNode_at γ rn id rs $$ Hrn with ⟨%ps, %qs, %ip, Hrn⟩
  wp_apply Habs none (fun _ h => by cases h) γ rn id rs ps qs ip rd H1 H2 H3 (fun _ h => by cases h)
    $$ [$Hrn $Hret $HA1 $Hbw]
    as %t %ca %ps' %ip' ⟨Hrn, %Ht1, %Ht2, %Hca, %Hca2, -⟩
  ihave Hrn := ownRawNodeAt_ownRawNode _ _ _ _ _ _ _ _ $$ Hrn
  iapply HΦ $$ %t %ca
  iframe Hrn
  ipureintro; exact ⟨Ht1, Ht2, Hca, Hca2⟩

theorem RawNode.Ready.spec_of_abs : RawNode.Ready.spec_of_abs.law (GF := GF) (hG := hG) := by
  intro Habs γ rn id x rs q g H1 H2 H3
  wp_start_folded as H
  iNamed H
  icases ownRawNode_at γ rn id rs $$ Hrn with ⟨%ps, %qs, %ip, Hrn⟩
  wp_apply Habs none (fun _ h => by cases h) γ rn id x rs ps qs ip q g H1 H2 H3 $$ [$Hrn $Hlive $Hfree]
    as %rd %ce %es %ms %sts %h %steps %L %ss %W %r' %qs' %ip' H
  iNamed H
  ihave Hrn := ownRawNodeAt_ownRawNode _ _ _ _ _ _ _ _ $$ Hrn
  iapply HΦ $$ %rd %ce %es %ms %sts %h %steps %L %ss %W
  iframe Hrn Hlive Henter Hlead Hsnapto Hsrcs Hss Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_own
    Hmsgs_cred Hsnapz Hrs Hrs_ok Hhard Hhsw Happ Hfrz Hdk
  ipureintro; exact ⟨Hmsgs_term, Hpsn⟩

end proof

end EtcdGrove
end Perennial
