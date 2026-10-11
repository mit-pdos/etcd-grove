/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/WithPrefetch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithPrefetch

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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem WithPrefetch.wp_proof : WithPrefetch.spec (GF := GF) (hG := hG) := by
  intro sl0 ks
  wp_start as #Hks
  iapply wp_fupd
  wp_auto
  ipersist keys
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
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hks] as %sl' ⟨Hsl', Hcap', -⟩
  (try wp_auto)
  iapply HΦ
  iexists ctx, cs, sl'
  iframe
  iexact Hctx

end proof

end concurrency
end EtcdGrove
end Perennial
