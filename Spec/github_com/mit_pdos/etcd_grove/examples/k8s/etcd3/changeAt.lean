/- Lean-first (no Rocq counterpart).

`changeAt(prev, cur, r)` (watch.go): `changeAtL` (`KWatch.lean`): the first key whose item differs
between the two stores, with its items there.
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
abbrev changeAt.spec : Prop :=
  ∀ (p c : mstore) (gp gc : GSt) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      storeOwn p gp ∗ storeOwn c gc }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.changeAt)) (Val #p)) (Val #c)) (Val #r))
  {{ (ch : change) (ok : Bool), RET (PairV #ch #ok);
      ⌜match changeAtL gp.items gc.items (uint.nat r) with
        | some x => ok = true ∧ chgOf ch = x
        | none => ok = false⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
