/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `recvc <- m` (a local message, `netP_local`); `n.done` never fires. -/
theorem node.ReportUnreachable.wp_proof :
    node.ReportUnreachable.spec (GF := GF) (hG := hG) := by
  intro γ id n to
  wp_start as #Hnode
  ihave #Hnode' := Hnode
  open_node Hnode'
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod rdCred_zero_upd (GF := GF) γ.raft with Hcr
  imod tickCred_zero (GF := GF) γ.bud with Htc
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists raftpb.Message, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.recvc', γ.recvc, _
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isHandshake_isChan $$ Hrecvc
    iapply handshake_send_au γ.recvc nv.recvc' _ (netP γ id) iprop(True)
      $$ [$Hlc1 $Hlc2 $Hlc3] Hrecvc [Hcr Htc]
    · iapply netP_local γ id _ (by first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr (.inl rfl)) | exact .inr (.inr (.inr rfl))) (by rfl) (by rfl) (by rfl) $$ Hlb Hcr Htc
    inext
    iintro -
    wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHandshake_isChan $$ Hdone
    iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
