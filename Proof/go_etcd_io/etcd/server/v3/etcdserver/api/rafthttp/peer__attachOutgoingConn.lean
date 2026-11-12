/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__attachOutgoingConn.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__attachOutgoingConn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__attach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.peer.attachOutgoingConn.wp_proof
    (hAttach : rafthttp.streamWriter.attach.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.attachOutgoingConn.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid p conn
  wp_start as ⟨#Hp, Hc⟩
  ihave ⟨Hc, #Ht⟩ := outConnOk_fields _ _ _ _ _ $$ Hc
  iunfold peerStreams at Hp
  icases Hp with ⟨%lg, %cw2, %cw1, %Rr2, %Rr1, #Hlg, %Hlgnn, #Hw2, #Hsw2, #Hw1, #Hsw1⟩
  (try wp_auto)
  cases ty
  all_goals
    simp only [StreamTy.str]
    (try wp_auto)
  all_goals
    first
      | (wp_apply hAttach Rh _ lid pid Rr2 cw2 conn $$ [$Hc] as %b Hb; iframe #)
      | (wp_apply hAttach Rh _ lid pid Rr1 cw1 conn $$ [$Hc] as %b Hb; iframe #)
    (try wp_auto)
    cases b
    · -- not taken: closed, its writer given back
      simp only [Bool.false_eq_true, ↓reduceIte]
      ihave ⟨%cl, #Hcl, %Q, Hclr, HQ⟩ := outConnOk_close _ _ _ _ _ $$ Hb
      (try wp_auto)
      iunfold closeRight at Hclr
      icases Hclr with ⟨%ci, %Hci, Hclr⟩
      subst Hci
      (try wp_auto)
      rw [method_unfold (t := go.GoType.PointerType rafthttp.outgoingConn.ty) (m := go!"Close")]
      (try wp_auto)
      wp_apply Hclr $$ [$HQ]
      iintro %_
      (try wp_auto)
      iapply HΦ; itrivial
    · simp only [Bool.not_true]
      (try wp_auto)
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
