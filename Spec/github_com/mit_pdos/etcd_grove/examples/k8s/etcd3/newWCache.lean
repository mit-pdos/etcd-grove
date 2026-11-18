/- Lean-first (no Rocq counterpart).

`newWCache(unary, total)` (k8setcd3.go; stage E of 7f-6): an empty table of cached objects whose
clients from `unary` on are watchers (`isCache c`, for any store `c`: no entry yet).
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
abbrev newWCache.spec : Prop :=
  ∀ (c : StoreCfg GF DObj) (unary total : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newWCache)) (Val #unary))
      (Val #total))
  {{ (tbl : Loc), RET #tbl; isCache c tbl }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
