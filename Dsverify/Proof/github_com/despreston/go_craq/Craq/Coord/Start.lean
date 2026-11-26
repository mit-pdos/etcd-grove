/-
`c.Start()`: `pingReplicas` pings the replicas forever, each in a goroutine of its own that
waits for the ping's result (a channel of capacity 1) or a timeout (`time.After`), and removes
the replica on a failure or a timeout (`RemoveNode`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.RemoveNode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions] [LogSpecs GF]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem wp_pingReplicas (cfg : Cfg GF) (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        isCoord cfg c }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"pingReplicas"))
        (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hc
  ihave #Hc' := Hc
  unfold isCoord coordDef
  icases Hc' with ⟨#Hctx, -, %Hbound, %f, #Htport, #Hfac, #Hmu⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
    [interface.mkOk go.string #(go!"starting pinging")]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args_sl ⟨Hargs, -⟩
  wp_apply LogSpecs.wp_Println _ _ _ $$ [Hargs]
  · iframe
    iapply argOks_of_wf _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
  iintro -
  ipersist cdr
  wp_pures
  wp_for
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
  iNamed Hlk
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.PointerType coordinator.node.ty)))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := Loc) (t := go.PointerType coordinator.node.ty) ([] : List Loc)
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %esl ⟨Hesl, Hecap⟩
  wp_auto
  wp_apply wp_slice_append _ ([] : List Loc) sl (rs.map Rep.loc) (DFrac.own 1) $$ [Hesl Hecap Hsl]
    as %cp ⟨Hcp, -, Hsl⟩
  · iframe
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
    Hreps Hjoin Htok]
  · inext; iapply coordLock_pack cfg c sl rs ver hd tl Hwf; iframe; iexact Hnfs
  simp only [List.nil_append]
  ihave %Hlen := ownSlice_len $$ Hcp
  simp only [List.length_map] at Hlen
  ihave IH : iprop(∃ (k : w64) (nv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z cp.len⌝) $$ [i n]
  · iexists _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat k < rs.length := by word
    list_elem rs (sint.nat k) as r
    ihave #Hnf := nodeFacts_at cfg rs _ r Hr_lookup $$ Hnfs
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z cp.len from ⟨Hk.1, Hif⟩, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index cp (sint.Z k) _ (DFrac.own 1) r.loc Hk.1 $$ [Hcp] as Hcp
    · iframe Hcp; ipureintro; exact locs_at rs _ r Hr_lookup
    wp_apply wp_fork $$ []
    · -- the ping of `r`
      wp_auto
      ipersist n
      wp_apply chan.wp_make2 (V := Bool) (W64 1) $$ [] as %ch %γch ⟨#Hch, %Hcap, Hoc⟩
      · ipureintro; constructor <;> decide
      iapply fupd_wp
      imod start_bag (V := Bool) (fun _ => iprop(True)) (.Buffered []) ch γch trivial $$ Hch Hoc with #Hbag
      imodintro
      ipersist resultCh
      unfold nodeFacts
      icases Hnf with ⟨#Haddr, %cl, #Hrpc, #Hcl⟩
      wp_apply wp_fork $$ []
      · -- the ping itself, its result sent on the channel
        unfold isNodeClient
        icases Hcl with ⟨%e, ⟨%He, -⟩, #Hcl⟩
        subst He
        icases Hcl with ⟨#HPing, -⟩
        wp_auto
        wp_apply HPing as %err -
        cases err with
        | nil =>
          wp_auto
          wp_apply wp_bag_send γch ch true (fun _ => iprop(True)) $$ []
          all_goals first | (iframe Hbag; done) | (iframe Hbag; itrivial) | itrivial
        | ok i =>
          wp_auto
          wp_apply wp_bag_send γch ch false (fun _ => iprop(True)) $$ []
          all_goals first | (iframe Hbag; done) | (iframe Hbag; itrivial) | itrivial
      ihave #HnfR : nodeFacts cfg r.loc r.addr $$ []
      · unfold nodeFacts; iframe Haddr; iexists cl; iframe Hrpc Hcl
      wp_apply +noauto (time.After.spec_pkgInit time.wp_After _)
      iintro %ach %γa #Hafter
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Bool, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Hbag
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
        inext
        iintro %v -
        wp_auto
        cases v
        · wp_auto
          wp_apply wp_node_Address' cfg r.loc r.addr $$ HnfR
          wp_apply wp_RemoveNode cfg c r.addr $$ [] as %err -
          · unfold isCoord coordDef; iexact Hc
          itrivial
        · wp_auto
          itrivial
      iapply BigAndL.bigAndL_singleton.2
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hafter
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hafter
      inext
      iintro %t -
      wp_auto
      wp_apply wp_node_Address' cfg r.loc r.addr $$ HnfR
      wp_apply wp_RemoveNode cfg c r.addr $$ [] as %err -
      · unfold isCoord coordDef; iexact Hc
      itrivial
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  · wp_apply time.wp_Sleep
    wp_for_post
    iframe

theorem coordinator.wp_Start : coordinator.wp_Start.spec (GF := GF) (hG := hG) := by
  intro cfg c
  wp_start as #Hc
  wp_auto
  wp_apply wp_pingReplicas cfg c $$ [Hc]
  · iframe Hc
  iapply HΦ; itrivial

end proof

end github_com.despreston.go_craq

end Perennial
