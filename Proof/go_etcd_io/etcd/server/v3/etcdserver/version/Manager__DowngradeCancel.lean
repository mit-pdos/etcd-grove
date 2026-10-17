/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/Manager__DowngradeCancel.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeCancel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.version

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

theorem version.Manager.DowngradeCancel.wp_proof :
    version.Manager.DowngradeCancel.spec (GF := GF) (hG := hG) := by
  intro m vs RE CVR EP CP ctx
  wp_start as ⟨#Hf, #Hs, #Hsrv, HCP⟩
  iunfold version.isServer at Hsrv
  icases Hsrv with ⟨%si, %Hsi, #HLR, -, #HDI, -, #HCA⟩
  subst Hsi
  iunfold version.versionFacts at Hf
  iunfold dgErrVar at Hf
  icases Hf with ⟨-, -, ⟨%eN, #HeN⟩, -⟩
  (try wp_auto)
  wp_apply HLR $$ %ctx as %err Herr
  cases err with
  | ok ei =>
    (try wp_auto)
    iapply HΦ
    ileft
    iframe Herr HCP
    ipureintro
    intro h; cases h
  | nil =>
    (try wp_auto)
    wp_apply HDI as %di ⟨%Hdi, %d, Hd⟩
    (try wp_auto)
    rcases d with ⟨tvs, en⟩
    cases en
    · (try wp_auto)
      iapply HΦ
      iright; ileft
      iframe Herr HCP
      iunfold dgErrIs
      iexists eN
      iframe HeN
      ipureintro; rfl
    · (try wp_auto)
      wp_apply HCA $$ %ctx [HCP] as %err' -
      · iexact HCP
      iapply HΦ
      iright; iright
      iexact Herr

end proof

end EtcdGrove
end Perennial
