/- Lean-first (no Rocq counterpart).

`drawConfig(prefix)` (`examples/mvccfull/config.go`): any configuration with the prefix `prefix`
(every other field any value), with its weight slices new (`mixOwn`, at the read weights `wr`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev drawConfig.spec : Prop :=
  ∀ (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.drawConfig)) (Val #pfx))
  {{ (cfg : Config) (wr : List w64), RET #cfg; ⌜cfg.Prefix' = pfx⌝ ∗ mixOwn cfg.Mix' wr }}

end spec

end mvccfull
end EtcdGrove
end Perennial
