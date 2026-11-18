/- Lean-first (no Rocq counterpart).

`checkedEvents(all, rv)` (watch.go): the events that are not errors (`keptL`), or false if one is
bad or a kept one is above `rv` (`rejectsL`). Its premise: every event's type below `2^63` (the Go
function compares types as `int`s; `decodeWEvents`' are below `256`).
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
abbrev checkedEvents.spec : Prop :=
  ∀ (s : GoSlice) (all : List WEv) (rv : w64),
  (∀ e ∈ all, e.t < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ wevsOwn s all }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.checkedEvents)) (Val #s)) (Val #rv))
  {{ (s' : GoSlice) (ok : Bool), RET (PairV #s' #ok);
      if rejectsL all (uint.nat rv) then ⌜ok = false⌝ else ⌜ok = true⌝ ∗ wevsOwnM s' (keptL all) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
