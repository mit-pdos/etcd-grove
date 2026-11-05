/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/cluster3/NewClient.lean`. Lean-first (no
Rocq counterpart). The bridges' slice, then `etcdstart.NewClients` of it at the caller's watch
environment; its result returned.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.NewClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClients

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

theorem NewClient.wp_proof (wp_NewClients : etcdstart.NewClients.spec (GF := GF) (hG := hG)) :
    NewClient.spec (GF := GF) (hG := hG) := by
  intro cfg lg V Hcfg Htb Hlg
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := GoString) (l := bridges cfg)
  try (isplitr; (ipureintro; rfl))
  iintro %epsp ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  wp_apply (wp_NewClients _ (bridges cfg) lg V Htb Hlg Hcfg.plainBridges) $$ [] as %cl %cerr Hcl
  · iframe #
  (try wp_auto)
  iapply HΦ
  iexact Hcl

end proof

end cluster3
end EtcdGrove
end Perennial
