/- Lean-first (no Rocq counterpart).

`wantEventsIdx(in, lo, hi, c)` (export.go): `wantEvents`' spec (`eventsInL`), the history read
through a view (`viewFrom`), whose premise it adds: the history shorter than `2^63`.
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
abbrev wantEventsIdx.spec : Prop :=
  ∀ (x : Input) (lo hi : w64) (c : mcfg) (g : GCfg),
  g.st.hist.length < 2 ^ 63 → uint.Z hi ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ cfgOwn c g }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.wantEventsIdx)) (Val #x)) (Val #lo)) (Val #hi)) (Val #c))
  {{ (s : GoSlice), RET #s; wevsOwnM s (eventsInL x g.st.hist (uint.nat lo) (uint.nat hi)) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
