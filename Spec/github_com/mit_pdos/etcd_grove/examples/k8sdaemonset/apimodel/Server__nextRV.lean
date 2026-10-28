/-
`s.nextRV()`, under the lock: the next version and its decimal form, recorded as issued; one receipt more (which bounds the counter).
Lean-first (no Rocq counterpart); phase 3 of `notes/k8s-daemonset-plan.md` (the model API server's
specs, D50's internal layer).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

abbrev Server.nextRV.spec : Prop :=
  ∀ [ApiDeps] (s : Loc) (rvs : GoMap) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ s.[apimodel.Server, go!"rev"] ↦ n ∗
      s.[apimodel.Server, go!"rvs"] ↦□ rvs ∗ rvs ↦$ issuedMap n.toNat ∗ ⧗ (n.toNat - 1) ∗
      ⌜1 ≤ n.toNat ∧ receiptBound GF ≤ 2 ^ 63⌝ }}
    (App (Val (s @!! go.GoType.PointerType apimodel.Server.ty @!! go!"nextRV")) (Val #()))
  {{ RET (PairV #(n + W64 1) #(rvStr (n + W64 1))); s.[apimodel.Server, go!"rev"] ↦ (n + W64 1) ∗
      rvs ↦$ issuedMap (n.toNat + 1) ∗ ⧗ n.toNat ∗ ⌜(n + W64 1).toNat = n.toNat + 1⌝ }}

end spec

end apimodel
end EtcdGrove
end Perennial
