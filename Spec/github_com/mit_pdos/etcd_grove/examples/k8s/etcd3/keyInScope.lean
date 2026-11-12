/- Lean-first (no Rocq counterpart).

`keyInScope(key, recursive, k)` (k8setcd3.go): `keyInScopeL` (`KList.lean`): the store key `k`
is selected by a list of `key` (exact if not recursive, else under `key` with the `/` boundary).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev keyInScope.spec : Prop :=
  ∀ (key : GoString) (r : Bool) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyInScope)) (Val #key)) (Val #r)) (Val #k))
  {{ RET #(keyInScopeL key r k); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
