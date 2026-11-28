/- Lean-first (no Rocq counterpart).

`reliableOk(in, req, evs, c)` (watch.go): `reliableOkL` (`KWatch.lean`): the events over the revisions
they mark are the changes' events in scope. Its premises: the configuration's revision, the request's
and every event's below `2^63` (the Go function's `rv+1`, `req+1` and `c.st.rv+1` do not overflow;
`watchOk` drops an event above the configuration's revision before, and the driver's inputs ask for
a revision below `2^63`, `InOk`).

`reliableOkIdx` (export.go) is `reliableOk` with the history read through a view (`viewFrom`): `reliableOk`'s spec, with
`viewFrom`'s premise added (the history shorter than `2^63`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HView

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
abbrev reliableOkIdx.spec : Prop :=
  ∀ (x : Input) (req : w64) (s : GoSlice) (evs : List WEv) (c : mcfg) (g : GCfg),
  g.st.hist.length < 2 ^ 63 →
  uint.Z g.st.st.rv < 2 ^ 63 → uint.Z req < 2 ^ 63 →
  (∀ e ∈ evs, uint.Z e.o.ResourceVersion' < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      wevsOwn s evs ∗ cfgOwn c g }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableOkIdx)) (Val #x)) (Val #req)) (Val #s)) (Val #c))
  {{ RET #(reliableOkL x (uint.nat req) evs g.st); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
