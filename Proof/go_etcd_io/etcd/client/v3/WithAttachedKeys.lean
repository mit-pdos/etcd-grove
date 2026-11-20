/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithAttachedKeys.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithAttachedKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem WithAttachedKeys.wp_proof : WithAttachedKeys.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  unfold leaseOptSpec
  imodintro
  iintro %p %op
  wp_start as Hp
  wp_auto
  iapply HΦ
  iexact Hp

end proof

end EtcdGrove
end Perennial
