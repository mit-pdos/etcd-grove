/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__Stop.lean` (k8s 7f-5b). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__Stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem watchChan.Stop.wp_proof : watchChan.Stop.spec (GF := GF) (hG := hG) := by
  intro wc cf γc γ cd
  wp_start as ⟨#Hcf, #Hcs, Hl⟩
  ihave Hst : |==> kStopped (GF := GF) γ $$ [Hl]
  · icases Hl with (Hl | #Hs)
    · unfold kLive kStopped
      imod dghostVar_update true γ.stop false $$ Hl with Hl
      iapply dghostVar_persist $$ Hl
    · imodintro; iexact Hs
  imod Hst with #Hst
  iunfold context.cancelSpec at Hcs
  wp_auto
  wp_bind (App (Val #cf) (Val #()))
  iapply Hcs
  · imodintro; unfold kCancelPD; ileft; iexact Hst
  inext
  iintro -
  wp_auto
  iapply HΦ
  iexact Hst

end proof

end k8s
end EtcdGrove
end Perennial
