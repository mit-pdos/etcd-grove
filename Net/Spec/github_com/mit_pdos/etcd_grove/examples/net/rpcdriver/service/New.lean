/- Lean-first (no Rocq counterpart).

`service.New()`: a service that has run no request, for the request ids' ghost map `γid` the caller
chose (`isSvc γid s`: its mutex's invariant holds the empty map of runs). Proved in
`Net/Proof/.../rpcdriver/service/New.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : service.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  ∀ (γid : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service }}
    (App (Val (@! service.New)) (Val #()))
  {{ (s : Loc), RET #s; ⌜s ≠ null⌝ ∗ isSvc γid s }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service
end Perennial
