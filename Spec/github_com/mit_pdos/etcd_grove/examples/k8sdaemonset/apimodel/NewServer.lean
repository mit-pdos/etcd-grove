/-
`NewServer(cfg)`: a new empty server (`St.empty`), whose state's clients' half it hands out. Its premise bounds the receipts (`receiptBound GF ≤ 2 ^ 63`: fewer writes than versions).
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

abbrev NewServer.spec : Prop :=
  ∀ [ApiDeps] (cfg : apimodel.Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel ∗ ⌜receiptBound GF ≤ 2 ^ 63⌝ }}
    (App (Val (@! apimodel.NewServer)) (Val #cfg))
  {{ (s : Loc) (γ : ApiNames), RET #s; isServer s γ cfg ∗ apiState γ St.empty }}

end spec

end apimodel
end EtcdGrove
end Perennial
