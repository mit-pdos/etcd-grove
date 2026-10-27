/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__autoSync.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__autoSync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.autoSync.wp_proof : Client.autoSync.spec (GF := GF) (hG := hG) := by
  intro c cfg
  wp_start as ⟨#Hcfg, %Hz⟩
  iStructNamed Hcfg
  wp_auto
  rw [Hz]
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
