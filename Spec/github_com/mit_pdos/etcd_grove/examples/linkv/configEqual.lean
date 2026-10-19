/- Lean-first (no Rocq counterpart).

`configEqual(a, b)` (linkv.go): whether two configurations hold the same contents (`cfgOwn`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- See the file header. -/
abbrev configEqual.spec : Prop :=
  ∀ (a b : kvConfig) (ga gb : GCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      cfgOwn a ga ∗ cfgOwn b gb }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.configEqual)) (Val #a))
      (Val #b))
  {{ RET #(decide (ga = gb)); True }}

end spec

end linkv
end EtcdGrove
end Perennial
