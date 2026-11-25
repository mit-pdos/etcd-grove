/- `ended(why)` (`examples/etcd/dist/client/client.go`). Lean-first (no Rocq counterpart); #50 N9a (the same statement as N9b's, `etcd-safe-n9b`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base


@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- `ended(why)` returns a result with `Checked` unset. -/
abbrev ended.spec : Prop :=
  ∀ (why : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! client.ended)) (Val #why))
  {{ (r : client.Result), RET #r; ⌜r.Checked' = false⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
