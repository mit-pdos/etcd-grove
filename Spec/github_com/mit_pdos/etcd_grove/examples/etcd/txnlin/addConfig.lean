/- Lean-first (no Rocq counterpart).

`addConfig(s, c)` (etcd_txnlin.go): `s`, or `s` with `c` appended if no configuration of `s`
equals it (`addConfigL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.txnlin


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

/-- See the file header. -/
abbrev addConfig.spec : Prop :=
  ∀ (s : GoSlice) (cs : List mcfg) (gs : List GCfg) (c : mcfg) (g : GCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
      s ↦* cs ∗ ownSliceCap mcfg s (DFrac.own 1) ∗
      ([∗list] c';g' ∈ cs;gs, cfgOwn c' g') ∗ cfgOwn c g }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.addConfig)) (Val #s)) (Val #c))
  {{ (s' : GoSlice) (cs' : List mcfg), RET #s';
      s' ↦* cs' ∗ ownSliceCap mcfg s' (DFrac.own 1) ∗
      [∗list] c';g' ∈ cs';addConfigL gs g, cfgOwn c' g' }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
