/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__filter.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__filter

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

theorem watchChan.filter.wp_proof : watchChan.filter.spec (GF := GF) (hG := hG) := by
  intro Obj S wc p sel emp x o rv
  unfold selPredOkW
  wp_start as ⟨#Hp, ⟨%Hsel, #Hmatch, #Hempty⟩, Hx⟩
  wp_auto
  wp_apply Hempty $$ [$Hp] as #Hp
  cases emp
  · wp_auto
    wp_apply Hmatch $$ %rfl [$Hp] [$Hx] as #Hp Hx
    iapply HΦ; iexact Hx
  · wp_auto
    rw [Hsel.2 rfl o]
    iapply HΦ; iexact Hx

end proof

end k8s
end EtcdGrove
end Perennial
