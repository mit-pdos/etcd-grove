/-
Proof of `Spec/go_etcd_io/etcd/client/v3/isHaltErr.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.isHaltErr
public import Spec.google_golang_org.grpc.status.FromError

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

theorem isHaltErr.wp_proof
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    isHaltErr.spec (GF := GF) (hG := hG) := by
  intro ci cd err
  wp_start as ⟨#HC, #Hse⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  iunfold _root_.Perennial.context.isContext at HC
  iunfold _root_.Perennial.context.isContextDef at HC
  iNamed HC
  wp_auto
  wp_apply HErr $$ %Broadcast.Pending as %ce -
  iclear HDeadline HDone HErr HValue HErrDone HDoneFresh HParentCC HClosedchan
  cases ce with
  | ok cei =>
    wp_auto
    iapply HΦ; ipureintro; intro h; cases h
  | nil =>
    wp_auto
    cases err with
    | nil =>
      wp_auto
      iapply HΦ; ipureintro; intro _; left; rfl
    | ok ei =>
      wp_auto
      wp_apply wp_FromError (GoInterface.ok ei) $$ [$Hst $Hse] as %ev %ok ⟨-, #HCode, -⟩
      wp_apply HCode
      wp_if_destruct
      · iapply HΦ; ipureintro; intro _; right; left; exact Hif
      · wp_apply HCode
        wp_if_destruct
        · iapply HΦ; ipureintro; intro _; right; right; exact Hif
        · iapply HΦ; ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
