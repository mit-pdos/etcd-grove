/- Lean-first (no Rocq counterpart).

`withPre(in, uid, rv, c, hasC)` (k8setcd3.go; stage 7b): `withPreL`, the input with the cached
object's preconditions.
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev withPre.spec : Prop :=
  ∀ (x : Input) (uid rv : Bool) (c : Obj) (hasC : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.withPre)) (Val #x)) (Val #uid)) (Val #rv)) (Val #c))
      (Val #hasC))
  {{ RET #(withPreL x uid rv c hasC); True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
