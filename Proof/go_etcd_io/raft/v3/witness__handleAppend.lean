/-
Proof of `Spec/go_etcd_io/raft/v3/witness__handleAppend.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.witness__handleAppend
public import Spec.go_etcd_io.raft.v3.witness__handleAppendNoUpdate
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasWitness
public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Proof.go_etcd_io.raft.v3.InvEpoch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `handleAppendNoUpdate` first; if it does not answer, the state being built takes the
request's entry (fresh cells) and replication sets (the request's slices, read-only), and the
answer acknowledges its index at its term. -/
theorem witness.handleAppend.wp_proof
    (wp_handleAppendNoUpdate : witness.handleAppendNoUpdate.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetLastLogIndex : raftpb.WitnessHardState.GetLastLogIndex.spec (GF := GF) (hG := hG)) :
    witness.handleAppend.spec (GF := GF) (hG := hG) := by
  intro w id dq p σ mv μ q st
  wp_start as ⟨#Hid, Hst, #Hp, #Hm, Hq⟩
  ihave #Hm' := Hm
  iunfold ownWMsg at Hm'
  icases Hm' with ⟨%s0, %s1, %Hmv, #Hs0, #Hs1, -, -⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  wp_auto
  wp_apply wp_handleAppendNoUpdate w id dq p σ mv μ $$ [$Hid $Hst $Hp $Hm] as %ml ⟨Hst, Hml⟩
  cases hr : (wAppendNoUpdate id σ μ).2
  · -- the state is written
    have hw : wAppend id σ st μ = (WHS.mk st.term st.vote st.commit μ.li μ.lt μ.ls st.lead μ.rs0
        μ.rs1, (respM MsgAppResp μ.frm id st.term μ.li false, [])) := by
      simp only [wAppend, hr, Bool.false_eq_true, ↓reduceIte]
    rw [hw]
    iunfold whsOwn at Hq
    iNamed Hq
    iunfold hsF at Hhs
    iNamed Hhs
    iunfold whsRest at Hr
    iNamed Hr
    iapply wp_fupd
    wp_auto
    rename_i plt' pls'
    irename : (plt' ↦ mv.LastLogTerm' : IProp GF) => Hlt'
    irename : (pls' ↦ mv.LastLogSubterm' : IProp GF) => Hls'
    imod cellRO_alloc $$ Hlt' with #cLt'
    imod cellRO_alloc $$ Hls' with #cLs'
    imod cellRO_alloc $$ «$r0» with #cLi'
    -- `m.ReplicationSet[0]`, `m.ReplicationSet[1]`
    icases (Access.access
        (A := m_ptr.[WitnessMessage, go!"ReplicationSet"] ↦ mv.ReplicationSet')
        (A' := m_ptr.[WitnessMessage, go!"ReplicationSet"] ↦ mv.ReplicationSet')
        (P := m_ptr ↦ mv)) $$ m with ⟨Hmr, Hmback⟩
    icases array_acc_same (GF := GF) _ (sint.Z (W64 0)) _ _ _ s0 (by decide) (by rw [Hrs]; rfl)
      $$ Hmr with ⟨Hm0, Hm0back⟩
    wp_auto
    ihave Hmr := Hm0back $$ Hm0
    icases array_acc_same (GF := GF) _ (sint.Z (W64 1)) _ _ _ s1 (by decide) (by rw [Hrs]; rfl)
      $$ Hmr with ⟨Hm1, Hm1back⟩
    wp_auto
    ihave Hmr := Hm1back $$ Hm1
    ihave m := Hmback $$ Hmr
    -- the answer
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 4) as %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    try wp_auto
    wp_apply wp_GetState.1 q (DFrac.own 1) ps $$ [$HS] as HS
    · ipureintro; exact Hnn
    try wp_auto
    wp_apply wp_GetTerm.2.2 ps (DFrac.own 1) pt st.term $$ [$HT $cT] as HT
    · ipureintro; exact Hsn
    try wp_auto
    wp_apply wp_GetLastLogIndex.1 q (DFrac.own 1) _ mv.LastLogIndex' $$ [$HLi $cLi'] as HLi
    · ipureintro; exact Hnn
    try wp_auto
    imod cellRO_alloc $$ «$v1» with #cTo
    imod cellRO_alloc $$ «$v2» with #cFr
    imod cellRO_alloc $$ «$v3» with #cTe
    imod cellRO_alloc $$ «$v4» with #cIx
    wp_alloc ml' as Hml'
    imod msgOwn_lit ml' _ (respM MsgAppResp μ.frm id st.term μ.li false) [] ⊤ $$ [Hml'] with Hmsg
    · simp only [respM, show MsgAppResp = W32 4 from rfl, ← Hfr, ← Hli]
      ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
      iframe Hml' Hnilb cTy cTo cFr cTe cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      msg_nulls
    wp_auto
    imodintro
    iapply HΦ
    iframe Hst Hmsg
    rw [← Hli, ← Hlt, ← Hls]
    unfold whsOwn
    iexists ps
    iframe HS
    isplitl [HT HV HC]
    · unfold hsF
      iexists _, _, _, _
      isplitr
      · ipureintro; exact Hsn
      iframe HT cT HV cV HC cC Hpbs
    unfold whsRest
    iexists _, _, _, _, _, _, _
    isplitr
    · ipureintro; exact Hnn
    iframe HLi cLi' HLt cLt' HLs cLs' HLd cLd HRs Hs0 HRo Hs1 Hpb
  · -- answered without a write
    have hw : wAppend id σ st μ = (st, (wAppendNoUpdate id σ μ).1) := by
      simp only [wAppend, hr, ↓reduceIte]
    rw [hw]
    wp_auto
    iapply HΦ
    iframe Hst Hq Hml

end proof

end EtcdGrove
end Perennial
