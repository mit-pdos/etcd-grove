/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/parseKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.parseKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem parseKV.wp_proof : parseKV.spec (GF := GF) (hG := hG) := by
  intro l v σ
  wp_start as #Hkv
  iunfold kvValAt at Hkv
  icases Hkv with ⟨%keySl, %valSl, #Hk, #Hks, -, #Hm, -, #Hv, #Hvs, -⟩
  wp_auto
  wp_apply (wp_bytes_to_string keySl v.key DFrac.discard) $$ [$Hks] as -
  (try wp_auto)
  iapply HΦ
  iexists _
  iframe
  unfold kEvIs
  simp only
  isplitr
  · ipureintro; simp
  isplitl
  · iexact Hvs
  · ipureintro; trivial

end proof

end k8s
end EtcdGrove
end Perennial
