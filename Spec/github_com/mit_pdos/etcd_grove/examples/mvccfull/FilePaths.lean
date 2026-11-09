/- Lean-first (no Rocq counterpart).

`FilePaths(cfg)` (`examples/mvccfull/mvccfull.go`): every file a run of `cfg` may create
(`filePathsM`): the two members' and one per snapshot install, `1` to `cfg.Ops`. For
`cfg.Ops < 2^63 - 1` (at the largest `int` Go's loop counter wraps and the loop never ends).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

/-- The files of a run of `cfg`. -/
def filePathsM [GooseExts] (cfg : Config) : List GoString :=
  [memberPathM cfg.Prefix' 0, memberPathM cfg.Prefix' 1] ++
    (List.range' 1 (sint.nat cfg.Ops')).map (buildPathM cfg.Prefix')

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev FilePaths.spec : Prop :=
  ∀ (cfg : Config), sint.Z cfg.Ops' < 2 ^ 63 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths)) (Val #cfg))
  {{ (s : GoSlice), RET #s; s ↦* filePathsM cfg }}

end spec

end mvccfull
end EtcdGrove
end Perennial
