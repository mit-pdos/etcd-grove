/- Lean-first (no Rocq counterpart).

`genFrom(n, id, c, hasC)` (k8s_etcd3.go): an input `Gen` may return (`GenIn`: a workload key, one of
the four kinds, ...), whose cached object, if it uses one, is the client's `c` (stage 7b).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev genFrom.spec : Prop :=
  ∀ (n id : w64) (c : Obj) (hasC : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genFrom))
      (Val #n)) (Val #id)) (Val #c)) (Val #hasC))
  {{ (x : Input), RET #x; ⌜GenIn x ∧ (x.UseCached' = true → hasC = true ∧ x.Cached' = c)⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
