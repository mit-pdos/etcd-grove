/- Lean-first (no Rocq counterpart).

`realRequest(in)` (`realcheck.go`): the maintainers' `Request` of the driver's unary input `in`, whose fields
an update writes fit an object (`inFits`, `tryUpdateFor`'s premise): `reqRep r x` (its view: the list's key
and options, the create's object, the delete's and the update's preconditions and closures, the get's
options) and `reqPin r x` (the captured cells of its closure).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealAgreeReq

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev realRequest.spec : Prop :=
  ∀ (x : Input), inFits x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realRequest)) (Val #x))
  {{ (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request), RET #r;
      reqRep r x ∗ reqPin r x }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
