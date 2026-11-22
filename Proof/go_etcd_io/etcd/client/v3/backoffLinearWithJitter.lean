/-
Proof of `Spec/go_etcd_io/etcd/client/v3/backoffLinearWithJitter.lean`: the closure reads the two
captured variables (never written after: persistent) and calls `jitterUp`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.backoffLinearWithJitter
public import Spec.go_etcd_io.etcd.client.v3.jitterUp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open go_etcd_io.etcd.cache.v3 (backoffOk)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem backoffLinearWithJitter.wp_proof (wp_jitterUp : jitterUp.spec (GF := GF) (hG := hG)) :
    backoffLinearWithJitter.spec (GF := GF) (hG := hG) := by
  intro w j
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist jitterFraction
  ipersist waitBetween
  imodintro
  iapply HΦ
  unfold backoffOk
  iintro !> %a %Ψ HΨ
  wp_auto
  wp_apply wp_jitterUp w j as %r -
  iapply HΨ

end proof

end EtcdGrove
end Perennial
