/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/WithAbortContext.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithAbortContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem WithAbortContext.wp_proof : WithAbortContext.spec (GF := GF) (hG := hG) := by
  intro ctx0 cs0
  wp_start as #Hctx0
  iapply wp_fupd
  wp_auto
  ipersist ctx
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
  iexists ctx0, cs0, sl
  iframe
  iexact Hctx0

end proof

end concurrency
end EtcdGrove
end Perennial
