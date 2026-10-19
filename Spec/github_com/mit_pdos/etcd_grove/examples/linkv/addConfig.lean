/- Lean-first (no Rocq counterpart).

`addConfig(s, c)` (linkv.go): `s`, or `s` with `c` appended if no configuration of `s` holds the
same contents (`addConfigL`); the configurations of `s` are held by `cfgOwn`.
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
abbrev addConfig.spec : Prop :=
  ∀ (s : GoSlice) (cs : List kvConfig) (gs : List GCfg) (c : kvConfig) (g : GCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv ∗
      s ↦* cs ∗ ownSliceCap kvConfig s (DFrac.own 1) ∗
      ([∗list] c';g' ∈ cs;gs, cfgOwn c' g') ∗ cfgOwn c g }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.addConfig)) (Val #s)) (Val #c))
  {{ (s' : GoSlice) (cs' : List kvConfig), RET #s';
      s' ↦* cs' ∗ ownSliceCap kvConfig s' (DFrac.own 1) ∗
      [∗list] c';g' ∈ cs';addConfigL gs g, cfgOwn c' g' }}

end spec

end linkv
end EtcdGrove
end Perennial
