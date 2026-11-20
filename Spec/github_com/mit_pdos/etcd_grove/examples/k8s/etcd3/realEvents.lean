/- Lean-first (no Rocq counterpart).

`realEvents(in, evs)` (`realcheck.go`): a watch's received events as the maintainers' validator is given
them (`realEventsL`: cut after the first Error event, D7g-2; none for a watch-list with no bookmark left,
D7g-3), read-only (`evsRO`) as the received ones are.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev realEvents.spec : Prop :=
  ∀ (x : Input) (sl : GoSlice) (rs : List REv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ evsRO sl rs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realEvents)) (Val #x)) (Val #sl))
  {{ (r : GoSlice), RET #r; evsRO r (realEventsL x rs) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
