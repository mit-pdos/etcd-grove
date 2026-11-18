/- Lean-first (no Rocq counterpart).

`reliableLo(in, req, lo)` (watch.go): `reliableLoL` (`WDefs.lean`): the start of the window the
request pins, for a request below `2^63` (`req+1` does not overflow).
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
abbrev reliableLo.spec : Prop :=
  ∀ (x : Input) (req lo : w64),
  uint.Z req < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableLo)) (Val #x)) (Val #req)) (Val #lo))
  {{ (l : w64), RET #l; ⌜uint.nat l = reliableLoL x (uint.nat req) (uint.nat lo)⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
