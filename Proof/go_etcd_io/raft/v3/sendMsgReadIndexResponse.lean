/- Lean-first (no Rocq counterpart; 2026-10-12, read-index).

The option is `ReadOnlySafe` (`ownReadOnly_option`), so the lease-based branch is dead.
`addRequest` at the commit index; `heartbeatCtx` of the non-empty queue is the position,
which `recvAck` records for the leader itself (`readonlyArrive`, through `hbCtx_add`); the
heartbeats then carry the context of the queue with the request (`hbCtx_recvAck`).
-/
module

public import Spec.go_etcd_io.raft.v3.sendMsgReadIndexResponse
public import Spec.go_etcd_io.raft.v3.readOnly__addRequest
public import Spec.go_etcd_io.raft.v3.readOnly__recvAck
public import Spec.go_etcd_io.raft.v3.readOnly__heartbeatCtx

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

theorem sendMsgReadIndexResponse.wp_proof
    (wp_readOnly_addRequest : readOnly.addRequest.spec (GF := GF) (hG := hG))
    (wp_readOnly_recvAck : readOnly.recvAck.spec (GF := GF) (hG := hG))
    (wp_readOnly_heartbeatCtx : readOnly.heartbeatCtx.spec (GF := GF) (hG := hG))
    (wp_raft_bcastHeartbeat : raft.bcastHeartbeat.spec (GF := GF) (hG := hG)) :
    sendMsgReadIndexResponse.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m ents Hlead
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  -- `switch r.readOnly.option`: `ReadOnlySafe`
  icases ownRaftPhys_readOnly cfg r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  icases ownReadOnly_option ro _ $$ Hro with ⟨%o, %Hosafe, Hopt, Hroback⟩
  wp_auto
  ihave Hro := Hroback $$ Hopt
  ihave Hphys := Hback $$ %ro %_ Hrof Hro
  ihave Hphys := ownRaftPhys_eq cfg r id _ s rfl $$ Hphys
  subst Hosafe
  wp_auto
  -- `addRequest(r.raftLog.committed, m)`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  ihave Hphys := Hlogback $$ Hlog
  icases ownRaftPhys_readOnly cfg r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  wp_auto
  wp_apply wp_readOnly_addRequest $$ [$Hro $Hents] as Hro
  ihave Hphys := Hback $$ %ro %_ Hrof Hro
  -- `recvAck(r.id, heartbeatCtx())`: the queue is not empty
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_readOnly $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  wp_auto
  wp_apply wp_readOnly_heartbeatCtx $$ [$Hro] as %sl ⟨Hro, Hsl⟩
  icases Hsl with (⟨%Hpend, -⟩ | ⟨-, Hsl, -⟩)
  · simp at Hpend
  wp_apply wp_readOnly_recvAck $$ [$Hro $Hsl] as ⟨Hro, -⟩
  · ipureintro; right; simp [u64Le_length]
  ihave Hphys := Hback $$ %ro %_ Hrof Hro
  ihave Hphys := ownRaftPhys_eq cfg r id _ (arriveState id s m ents)
    (by simp only [arriveState, readonlyArrive, arriveReq, hbCtx_add]) $$ Hphys
  -- `bcastHeartbeat()`
  wp_apply wp_raft_bcastHeartbeat _ _ _ (arriveState id s m ents) Hlead $$ [$Hphys]
    as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
  iapply HΦ
  iframe Hphys
  ipureintro
  refine ⟨fun m' Hm' => ⟨(Hms m' Hm').1, ?_⟩, Hmm⟩
  rw [(Hms m' Hm').2]
  simp only [arriveState, readonlyArrive, hbCtx_recvAck]
