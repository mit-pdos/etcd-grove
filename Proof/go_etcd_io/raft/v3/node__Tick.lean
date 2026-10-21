/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Tick

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

/-- The credit goes into `tickc` with the tick (`tickInv`), or is dropped with it; the
`default` branch's warning reads the raft struct's shared fields (`isNode`). -/
theorem node.Tick.wp_proof : node.Tick.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as ⟨#Hnode, Hcred⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  wp_auto_lc 2
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `tickc <- struct{}{}`: the credit with the tick
      simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.tickc',
        γ.tick, ()
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iexact Htickc
      unfold nonblockingSendAu nonblockingSendAuInner
      isplit
      · iinv Htickinv with Hi Hclose
        imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
        unfold tickInv
        icases Hi with ⟨%l, Hoc, Hcr⟩
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        iexists .Buffered l
        iframe Hoc
        simp only
        iintro Hoc
        imod Hmask with -
        imod Hclose $$ [Hoc Hcr Hcred] with -
        · inext
          iexists l ++ [()]
          iframe Hoc
          simp only [List.length_append, List.length_singleton]
          iapply (tickCred_split γ.bud l.length 1).2
          iframe Hcr Hcred
        imodintro
        wp_auto
        iapply HΦ
        itrivial
      · itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-n.done`: never
      simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply blocking_rcv_implies_nonblocking
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`: the warning, through the raft struct's logger
    wp_auto
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlogger
    try wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
