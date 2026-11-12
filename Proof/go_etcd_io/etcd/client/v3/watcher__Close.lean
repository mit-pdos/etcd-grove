/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcher__Close.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__Close
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__close
public import Spec.errors.IsStatusErr

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 0 in
theorem watcher.Close.wp_proof
    (wp_close : watchGRPCStream.close.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    watcher.Close.spec (GF := GF) (hG := hG) := by
  intro V w
  wp_start as ⟨⟨%ce, #Hce, %Hcep⟩, #Hw⟩
  ihave #Hw' := Hw
  iunfold isClientWatcher at Hw'
  icases Hw' with ⟨%callSl, %vs, %Hwnn, #Hrem, #Hco, #Hvs, #Hok, #Hlg, #Hmu, #Hf, %Hlgb⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold watcherMu at HR
  icases HR with ⟨%m, Hst, HM⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst]
  · inext; unfold watcherMu; iexists map.nil; iframe Hst; ileft; ipureintro; rfl
  ihave Hnil : iprop(∃ e : GoInterface, err_ptr ↦ e ∗ statusErrOk e) $$ [err]
  · iexists _; iframe
    unfold statusErrOk
    iintro !> %e0 %h; cases h
  icases HM with (%Hn | ⟨%M, HM, #HMs⟩)
  · subst Hn
    icases Hnil with ⟨%e, err, #Hse⟩
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    wp_call
    try simp only [show (null : Loc) = map.nil from rfl, _root_.decide_true]
    wp_auto
    wp_apply wp_Is e (GoInterface.ok ce) (Or.inr (Or.inl ⟨ce, rfl, Hcep⟩)) $$ [] as %bIs -
    · iframe #
    cases bIs <;> (wp_auto; iapply HΦ; itrivial)
  · wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(∃ (v : Loc) (e : GoInterface),
        wgs_ptr ↦ v ∗ err_ptr ↦ e ∗ statusErrOk e)) _ _ _ m M (DFrac.own 1) $$ HM
    iintro %keys %Hkeys
    isplitl [wgs Hnil]
    · icases Hnil with ⟨%e, err, #Hse⟩
      iexists _, e; iframe; iframe #
    isplitr
    · imodintro
      iintro %i %key %v ⟨%Hki, %Hmv⟩ ⟨%v0, %e, Hws, err, #Hse⟩
      wp_auto
      ihave ⟨%G, %HG, #HG⟩ := BigSepM.bigSepM_lookup Hmv $$ HMs
      rw [← HG.1]
      wp_apply wp_close V G callSl $$ [] as %werr #Hwe
      · iframe #
      cases werr with
      | nil =>
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _, e
        iframe; iframe #
      | ok i =>
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _, _
        iframe; iframe #
    iintro ⟨%v, %e, Hws, err, #Hse⟩ HM
    wp_auto
    wp_apply wp_Is e (GoInterface.ok ce) (Or.inr (Or.inl ⟨ce, rfl, Hcep⟩)) $$ [] as %bIs -
    · iframe #
    cases bIs <;> (wp_auto; iapply HΦ; itrivial)

end proof

end EtcdGrove
end Perennial
