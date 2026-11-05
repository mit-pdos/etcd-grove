/- Lean-first (no Rocq counterpart).

`Gen(tbl, id)` (k8s_etcd3.go): `genFrom` of a random number and client `id`'s cached object in the
table `tbl` (`isCache c tbl`): an input `Gen` may return, its cached object one of the store `c`
(`cachedIn`): boxed, `Apply`'s input (`kInOk c`), as `Check`'s closure gives `lintest.genSpec`
(stage 7b: the table).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Gen.spec : Prop :=
  ∀ (c : StoreCfg GF DObj) (tbl : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      isCache c tbl }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Gen)) (Val #tbl))
      (Val #id))
  {{ (x : Input), RET #x; ⌜GenIn x⌝ ∗ cachedIn c x }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
