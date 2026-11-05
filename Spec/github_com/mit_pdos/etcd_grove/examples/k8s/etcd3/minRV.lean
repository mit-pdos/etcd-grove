/- Lean-first (no Rocq counterpart).

`minRV(m, d, c, hasC)` (k8setcd3.go; stage 7b): `minRVL`, a `Get`'s minimum resource version.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev minRV.spec : Prop :=
  ∀ (m d : w64) (c : Obj) (hasC : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.minRV)) (Val #m)) (Val #d)) (Val #c)) (Val #hasC))
  {{ RET #(minRVL m d c hasC); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
