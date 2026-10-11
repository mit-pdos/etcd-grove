/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Compact.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Compact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.Compact.wp_proof : leasingKV.Compact.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx rev sl Φ
  iintro ⟨#Hpkg, #Hlkv⟩ HΦ
  rw [method_unfold]
  ihave #Hlkv' := Hlkv
  unfold isLeasingKV
  icases Hlkv' with ⟨%cl, %kv, %c, %cs, %cancel, %osl, -, -, #Hkv, -⟩
  ispecialize HΦ $$ %kv Hkv
  wp_auto
  wp_bind (App (App (App (Val #(methods kv.ty go!"Compact" kv.v)) (Val #ctx)) (Val #rev)) (Val #sl))
  iapply wp_wand $$ HΦ
  iintro %v ⟨%resp, %err, %Hv, HΦ⟩
  subst Hv
  wp_auto
  iexact HΦ

end proof

end leasing
end EtcdGrove
end Perennial
