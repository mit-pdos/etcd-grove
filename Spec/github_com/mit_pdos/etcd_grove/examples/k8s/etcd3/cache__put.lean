/- Lean-first (no Rocq counterpart).

`(*cache).put(id, o)` (k8setcd3.go; stage 7b): makes the cached object `o` (`cachedObjOk`) client
`id`'s.
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
abbrev cache.put.spec : Prop :=
  ∀ (c : StoreCfg GF DObj) (tbl : Loc) (id : w64) (o : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ isCache c tbl ∗ cachedObjOk c o }}
    (App (App (Val (tbl @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache.ty @!! go!"put")) (Val #id)) (Val #o))
  {{ RET #(); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
