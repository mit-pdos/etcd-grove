/- Lean-first (no Rocq counterpart).

`evRange(evs)` (watch.go): `evRangeL` (`KWatch.lean`): the revisions the events mark, for events
whose revisions are below `2^63` (`rv+1` does not overflow).
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
abbrev evRange.spec : Prop :=
  ∀ (s : GoSlice) (evs : List WEv),
  (∀ e ∈ evs, uint.Z e.o.ResourceVersion' < 2 ^ 63) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ wevsOwn s evs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.evRange)) (Val #s))
  {{ (lo hi : w64), RET (PairV #lo #hi);
      ⌜evs ≠ [] → evRangeL evs = some (uint.nat lo, uint.nat hi)⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
