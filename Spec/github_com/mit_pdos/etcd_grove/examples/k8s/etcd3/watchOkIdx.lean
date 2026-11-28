/- Lean-first (no Rocq counterpart).

`watchOk(in, out, c)` (watch.go): `watchOkL` (`KWatch.lean`), the check of the watch `in` with output
`out` against the configuration's history. Its premises: the configuration's revision below `2^63`
(a store revision, `HistWf`), and the watch's minimum resource version, if it parses, below `2^63`
(`InOk`).

`watchOkIdx` (export.go) is `watchOk` with the history read through a view (`viewFrom`): `watchOk`'s spec, with
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
abbrev watchOkIdx.spec : Prop :=
  ∀ (x : Input) (y : Output) (c : mcfg) (g : GCfg),
  g.st.hist.length < 2 ^ 63 →
  uint.Z g.st.st.rv < 2 ^ 63 → (∀ n, parseRVD x.MinRV' = some n → uint.Z n < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ cfgOwn c g }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOkIdx)) (Val #x)) (Val #y)) (Val #c))
  {{ RET #(watchOkL x y g.st); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
