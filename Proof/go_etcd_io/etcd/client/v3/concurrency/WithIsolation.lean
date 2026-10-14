/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/WithIsolation.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithIsolation

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem WithIsolation.wp_proof : WithIsolation.spec (GF := GF) (hG := hG) := by
  intro lvl
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist lvl
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold stmOptSpec
  imodintro
  iintro %p %o
  wp_start as Hp
  unfold stmOptionsOwn
  icases Hp with ⟨%ctx, %cs, %sl, Hp, Hsl, Hcap, #Hctx⟩
  wp_auto
  iapply HΦ
  iexists ctx, cs, sl
  iframe
  iexact Hctx

end proof

end concurrency
end EtcdGrove
end Perennial
