/- Lean-first (no Rocq counterpart).

`(*cache).get(id)` (k8setcd3.go; stage 7b): client `id`'s cached object, if any (a cached object
of the store `c`, `cachedObjOk`).
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
abbrev cache.get.spec : Prop :=
  ∀ (c : StoreCfg GF DObj) (tbl : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ isCache c tbl }}
    (App (Val (tbl @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache.ty @!! go!"get")) (Val #id))
  {{ (o : Obj) (ok : Bool), RET (PairV #o #ok); if ok then cachedObjOk c o else iprop(True) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
