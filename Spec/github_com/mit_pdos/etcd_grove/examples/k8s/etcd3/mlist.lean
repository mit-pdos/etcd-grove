/- Lean-first (no Rocq counterpart).

`mlist(in, c)` (k8setcd3.go): `mlistL x g.st` (`KList.lean`), the Model's list on the
configuration `c`: too-large above the store's revision; else the loop on the store read (the
current one, or the history's at the requested revision for a past read). Its premise: the
stores' item counts fit the loop's `int64` counters.

Its callees outside the driver (`storage.PrepareKey`, the driver-specialized
`storage.SelectionPredicate.Matches` and `storage.PrepareContinueToken`) are hypotheses of its
proof (Q7e-3b-2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev mlist.spec : Prop :=
  ∀ (x : Input) (c : mcfg) (g : GCfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ cfgOwn c g ∗
      ⌜∀ s ∈ g.st.st :: g.st.hist, s.items.length < 2 ^ 62⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mlist)) (Val #x)) (Val #c))
  {{ RET #(mlistL x g.st); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
