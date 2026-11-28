/- Lean-first (no Rocq counterpart).

`watchListOk(in, req, evs, c)` (watch.go): `watchListOkL` (`WDefs.lean`). Its premises: the
configuration's revision, the request's below `2^63`, and every event's at most the configuration's
(`checkedEvents` before).

`watchListOkIdx` (export.go) is `watchListOk` with the history read through a view (`viewFrom`): `watchListOk`'s spec, with
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
abbrev watchListOkIdx.spec : Prop :=
  ∀ (x : Input) (req : w64) (s : GoSlice) (evs : List WEv) (c : mcfg) (g : GCfg),
  g.st.hist.length < 2 ^ 63 →
  uint.Z g.st.st.rv < 2 ^ 63 → uint.Z req < 2 ^ 63 →
  (∀ e ∈ evs, uint.nat e.o.ResourceVersion' ≤ uint.nat g.st.st.rv) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      wevsOwn s evs ∗ cfgOwn c g }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchListOkIdx)) (Val #x)) (Val #req)) (Val #s)) (Val #c))
  {{ RET #(watchListOkL x (uint.nat req) evs g.st); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
