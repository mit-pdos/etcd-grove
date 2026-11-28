/- Lean-first (no Rocq counterpart).

`initialPrefixOk(in, req, evs, c)` (watch.go): `initialPrefixOkL` (`KWatch.lean`): the events are a
prefix of the initial events at some revision from the requested one to the configuration's. Its
premise: the configuration's revision below `2^63` (the loop up to it ends).

`initialPrefixOkIdx` (export.go) is `initialPrefixOk` with the history read through a view (`viewFrom`): `initialPrefixOk`'s spec, with
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
abbrev initialPrefixOkIdx.spec : Prop :=
  ∀ (x : Input) (req : w64) (s : GoSlice) (evs : List WEv) (c : mcfg) (g : GCfg),
  g.st.hist.length < 2 ^ 63 →
  uint.Z g.st.st.rv < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      wevsOwn s evs ∗ cfgOwn c g }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialPrefixOkIdx)) (Val #x)) (Val #req)) (Val #s)) (Val #c))
  {{ RET #(initialPrefixOkL x (uint.nat req) evs g.st); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
