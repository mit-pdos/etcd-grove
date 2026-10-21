/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

The local case reaches `r.readStates` through `ownRaftPhysC_misc`, reads `req.Entries[0].Data`
through the read-only entries, and appends the `ReadState`; the forwarded case builds the
response literal and touches nothing.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMiscR
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__responseToReadIndexReq
public import RaftWitness.Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- The local case, after either test that decides it (`From == None`, `From == r.id`), with
`Hlocal` the disjunction it gives. -/
local macro "ri_local" : tactic => `(tactic| (
    wp_auto
    icases ownRaftPhysC_misc c r id s $$ Hphys with ⟨%rsl, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
    iunfold ownRaftMisc at Hmisc
    iNamed Hmisc
    iunfold readStatesPts at HreadStates
    icases HreadStates with ⟨%vs, #Hvs, #Hvb⟩
    wp_auto
    wp_apply wp_Message_GetEntries.1 req DFrac.discard DFrac.discard false ⟨m, e :: es, sn, ctx, rs⟩
      $$ [$(frameH `Hreq)] as %esl %els ⟨#Hesl, #Hents, -, -⟩
    ihave ⟨%l0, %Hl0, #He0⟩ := entsBig_lookup els (e :: es) 0 e rfl $$ Hents
    ihave %Hlen := ownSlice_len $$ Hesl
    ihave %Hbl := entsBig_length $$ Hents
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z esl.len by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at Hbl; word)]
    wp_apply wp_load_slice_index esl (sint.Z (W64 0)) els DFrac.discard l0 (by word) $$ [Hesl] with -
    · iframe Hesl; ipureintro; exact Hl0
    wp_apply wp_Entry_GetData.1 l0 DFrac.discard e $$ [$(frameH `He0)] as %ds ⟨#Hds, -⟩
    wp_apply wp_slice_literal (V := ReadState) [ReadState.mk idx ds]
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    have Hsz : go.arrayLiteralSize [KeyedElement none (ElementExpression ReadState.ty
        #(ReadState.mk idx ds))] = 1 := rfl
    simp only [Hsz]
    wp_apply wp_slice_append_persistent (V := ReadState) rsl vs _ [ReadState.mk idx ds] (DFrac.own 1)
        $$ [$(frameH `Hvs) $(frameH `HreadStates_cap) $(frameH `Hsl)]
      as %rs' ⟨Hvs', HreadStates_cap, -⟩
    wp_alloc lresp as Hresp
    imod msgOwn_zero lresp ⊤ $$ Hresp with Hresp
    wp_auto
    iapply HΦ
    rw [ite_eq_left Hlocal]
    ihave Hphys := Hback $$ %rs' %ro %pr
      %({ s.rd with states := s.rd.states ++ [ReadStateM.mk idx e.Data'] }) Hrs Hro Hpr
      [Hvs' HreadStates_cap Hro_obj Hpri Hpri_cap]
    · unfold ownRaftMisc
      simp only [named]
      iframe HreadStates_cap Hro_obj Hpri Hpri_cap
      iunfold readStatesPts
      iexists vs ++ [ReadState.mk idx ds]
      iframe Hvs'
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hvb Hds
      ipureintro; rfl
    ihave Hphys := ownRaftPhysC_eq c r id
      { s with rd := { s.rd with states := s.rd.states ++ [ReadStateM.mk idx e.Data'] } }
      (addReadState s idx e.Data') rfl $$ Hphys
    iframe Hphys Hresp
  ))

/-- The local case (`ri_local`, once per test that decides it): `r.readStates` through
`ownRaftPhysC_misc`, `req.GetEntries()[0].GetData()` through the frozen request's read-only
entries, the `ReadState` appended (its `RequestCtx` the request's data slice, read-only), and a
fresh `&pb.Message{}`.

Raft v3.7 (stage R4): the request is a frozen `*pb.Message` read through its getters; the
local case appends the `ReadState` with the request's data slice (read-only, D6) and returns a
fresh `&pb.Message{}` (`msgOwn_zero`); the forwarded case builds the response with
`MsgReadIndexResp.Enum()`, the request's own `From` cell (frozen) as `To`, `new(readIndex)` and
the request's entries slice (read-only), `msgOwn_of_struct`. -/
theorem raft.responseToReadIndexReq.wp_proof
    (wp_Message_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_Message_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.responseToReadIndexReq.spec (GF := GF) (hG := hG) := by
  intro c r id s req m idx e es sn ctx rs
  wp_start as ⟨Hphys, #Hreq⟩
  wp_auto
  wp_apply wp_Message_GetFrom.1 req DFrac.discard DFrac.discard false ⟨m, e :: es, sn, ctx, rs⟩
    $$ [$Hreq] with -
  by_cases H0 : m.From' = W64 0
  · have Hlocal : m.From' = W64 0 ∨ m.From' = id := .inl H0
    rw [decide_eq_true H0]
    ri_local
  · rw [decide_eq_false H0]
    wp_auto
    wp_apply wp_Message_GetFrom.1 req DFrac.discard DFrac.discard false ⟨m, e :: es, sn, ctx, rs⟩
      $$ [$Hreq] with -
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    by_cases Hid : m.From' = id
    · have Hlocal : m.From' = W64 0 ∨ m.From' = id := .inr Hid
      rw [decide_eq_true Hid]
      ri_local
    · rw [decide_eq_false Hid]
      wp_auto
      rw [show raftpb.MsgReadIndexResp = #((W32 16 : raftpb.MessageType)) from rfl]
      -- (as `confchange/toConfChangeSingle.lean`) Perennial gives `NotInterface` per type
      -- constructor, and `go.int32` (`MessageType`'s underlying type) is a non-reducible definition
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply wp_MessageType_Enum (W32 16)
      iintro %pty Hpty
      imod cellRO_alloc $$ Hpty with #cTyR
      ihave Hreq2 := Hreq
      simp only [msgOwn, msgPts]
      iunfold msgPtsC at Hreq2
      icases Hreq2 with ⟨%qty, %qto, %qfr, %qte, %qlt, %qix, %qco, %qvo, %qrj, %qrh, %qes, %qels, %qps,
        %qcs, %qrs, %quf, Hreq2⟩
      iNamed Hreq2
      wp_auto
      imod cellRO_alloc $$ «$v2» with #cIx
      wp_apply wp_Message_GetEntries.1 req DFrac.discard DFrac.discard false ⟨m, e :: es, sn, ctx, rs⟩
        $$ [$Hreq] as %esl %els ⟨#Hesl, #Hents', -, -⟩
      wp_alloc lresp as Hresp
      simp only
      ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod ownSlice_persist $$ Hnilb with #Hnilb
      ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod msgOwn_of_struct lresp
        { state' := zeroValDef, Type' := pty, To' := qfr, From' := null, Term' := null,
          LogTerm' := null, Index' := «$v2_ptr», Entries' := esl, Commit' := null, Vote' := null,
          Snapshot' := null, Reject' := null, RejectHint' := null, Context' := slice.nil,
          Responses' := slice.nil, unknownFields' := slice.nil, sizeCache' := 0 } els ⟨readIndexRespMsg m idx, e :: es, none, [], []⟩ ⊤ rfl
        $$ [Hresp Hnilr] with Hresp
      · simp only [readIndexRespMsg]
        iframe Hresp Hesl Hents' Hnilb Hnilr cTyR cFr cIx
        simp only [snapOpt]
        repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
        ipureintro; trivial
      wp_auto
      iapply HΦ
      rw [if_neg (show ¬(m.From' = W64 0 ∨ m.From' = id) by rintro (h | h) <;> contradiction)]
      iframe Hphys Hresp

end proof

end EtcdGrove
end Perennial
