/- Lean-first (no Rocq counterpart).

`toEvent(in, ch)` (watch.go): `toEventL` (`KWatch.lean`): the change's event for the watch's
predicate, if any.
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
abbrev toEvent.spec : Prop :=
  ∀ (x : Input) (ch : change),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toEvent)) (Val #x)) (Val #ch))
  {{ (ev : WEvent) (ok : Bool), RET (PairV #ev #ok);
      ⌜match toEventL x (chgOf ch) with
        | some e => ok = true ∧ wevOf ev = e
        | none => ok = false⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
