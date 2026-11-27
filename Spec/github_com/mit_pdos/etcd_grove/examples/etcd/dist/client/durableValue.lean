/- `durableValue(i)` (`examples/etcd/dist/client/durable.go`): `v` and the byte `i`. Lean-first (no Rocq counterpart); #50 N9a. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVWorkDefs

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

/-- `durableValue(i)`, `i ≥ 0`, returns `durVal i`. -/
abbrev durableValue.spec : Prop :=
  ∀ (i : w64), 0 ≤ sint.Z i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! client.durableValue)) (Val #i))
  {{ (s : GoString), RET #s; ⌜s = durVal (sint.nat i)⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
