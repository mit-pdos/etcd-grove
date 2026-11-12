/- Lean-first (no Rocq counterpart).

`normalize(cfg)` (`examples/mvccfull/config.go`): the configuration clamped (`normalizeM`): a
depth of at least `1`, a non-negative `MaxVal`, at most `511` watchers.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- `normalize(cfg)`'s result. -/
def normalizeM [GooseExts] (cfg : Config) : Config :=
  { cfg with
    Depth' := if sint.Z cfg.Depth' < 1 then W64 1 else cfg.Depth'
    MaxVal' := if sint.Z cfg.MaxVal' < 0 then W64 0 else cfg.MaxVal'
    Watchers' := if 511 < sint.Z cfg.Watchers' then W64 511 else cfg.Watchers' }

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev normalize.spec : Prop :=
  ∀ (cfg : Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.normalize)) (Val #cfg))
  {{ RET #(normalizeM cfg); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
