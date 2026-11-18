/- Lean-first (no Rocq counterpart).

`initialEvents(in, st)` (watch.go): `initialEventsL` (`KWatch.lean`): an Added event for each item of
the store in the watch's scope that its predicate matches, in key order.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev initialEvents.spec : Prop :=
  ∀ (x : Input) (st : mstore) (g : GSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ storeOwn st g }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialEvents)) (Val #x)) (Val #st))
  {{ (s : GoSlice), RET #s; wevsOwnM s (initialEventsL x g) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
