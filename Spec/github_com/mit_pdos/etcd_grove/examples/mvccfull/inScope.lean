/- Lean-first (no Rocq counterpart).

`inScope(cfg)` (`examples/mvccfull/config.go`): whether `cfg` is in `Run`'s scope; when it answers
`true`, `runCfgOk cfg wr` holds of the read weights `wr` (read only). The check is exactly
`runCfgOk` (`ScopeLemmas.lean`, `runCfgOk_of`; the converse, which the proof does not need, is what
makes the program cover every configuration `Run.spec` admits).
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
abbrev inScope.spec : Prop :=
  ∀ (cfg : Config) (wr : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      cfg.Mix'.Read' ↦*{dq} wr }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.inScope)) (Val #cfg))
  {{ (b : Bool), RET #b; cfg.Mix'.Read' ↦*{dq} wr ∗ ⌜b = true → runCfgOk cfg wr⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
