/-
Port of election_proof/proof_raft__bcastHeartbeat.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeat
public import Spec.go_etcd_io.raft.v3.readOnly__heartbeatCtx
public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeatWithCtx

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

/-- `r.readOnly` through `ownRaftPhys_readOnly`, `heartbeatCtx` on the
object it hands out (no pending request, so `nil`), the object back
unchanged; then `bcastHeartbeatWithCtx` with the `nil` context. -/
theorem raft.bcastHeartbeat.wp_proof
    (wp_readOnly_heartbeatCtx : readOnly.heartbeatCtx.spec (GF := GF) (hG := hG))
    (wp_raft_bcastHeartbeatWithCtx : raft.bcastHeartbeatWithCtx.spec (GF := GF) (hG := hG)) :
    raft.bcastHeartbeat.spec (GF := GF) (hG := hG) := by
  intro cfg r id s Hlead
  wp_start as Hphys
  iNamed Hphys
  icases ownRaftPhys_readOnly cfg r id s $$ Hphys with ⟨%ro, %rr, %Hpend, Hrof, Hro, Hback⟩
  wp_auto
  wp_apply wp_readOnly_heartbeatCtx $$ [$Hro] as %sl ⟨Hro, Hsl⟩
  icases Hsl with (⟨%_, %Hsl⟩ | ⟨%Hne, -⟩)
  · subst Hsl
    ihave Hphys := Hback $$ %ro %rr %Hpend Hrof Hro
    wp_apply wp_raft_bcastHeartbeatWithCtx _ _ _ _ _ [] Hlead $$ [$Hphys]
      as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
    · iapply ownSlice_nil
    iapply HΦ
    iframe Hphys
    ipureintro
    exact ⟨fun m Hm => (Hms m Hm).1, Hmm⟩
  · exact absurd Hpend Hne

end proof

end EtcdGrove
end Perennial
