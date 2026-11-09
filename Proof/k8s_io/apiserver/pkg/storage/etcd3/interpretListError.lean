/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/interpretListError.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretListError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewResourceExpired

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

theorem interpretListError.wp_proof
    (wp_NewResourceExpired : apierrors.NewResourceExpired.spec (GF := GF) (hG := hG)) :
    interpretListError.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ c err ck kp
  wp_start as #Herr
  ihave #Prt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave #Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Prt
  icases Hri with ⟨-, ⟨%eCP, #HeCP, -, -, %HtCP⟩, -⟩
  obtain ⟨x, hx⟩ := HtCP
  ihave #Herr' := Herr
  iunfold kClientErr at Herr'
  icases Herr' with ⟨%hce, -, -⟩
  wp_auto
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
