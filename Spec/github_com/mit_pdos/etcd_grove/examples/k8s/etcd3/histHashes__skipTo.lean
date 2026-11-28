/- Lean-first (no Rocq counterpart).

`(*histHashes).skipTo(c, t)` (export.go, notes/k8s-dist-k9.md §2.4): `c` at the revision `t`
(`skipToL`: a foreign store per revision appended, the items unchanged), or `c` if it is at `t` or
beyond. `HWf` gives a non-nil history and that the foreign stores `gaps[base]` caches (keyed by the
history alone) hold the configuration's items.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3
  (mstore mcfg hnode Input histHashes cfgSet)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev histHashes.skipTo.spec : Prop :=
  ∀ (hh : Loc) (c : mcfg) (g : GCfg) (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hhOwn hh ∗ cfgOwn c g ∗ ⌜HWf g.st ∧ uint.nat t < 2 ^ 63⌝ }}
    (App (App (Val (hh @!! go.GoType.PointerType histHashes.ty @!! go!"skipTo")) (Val #c)) (Val #t))
  {{ (c' : mcfg), RET #c'; cfgOwn c' ⟨skipToL g.st (uint.nat t), g.pend⟩ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
