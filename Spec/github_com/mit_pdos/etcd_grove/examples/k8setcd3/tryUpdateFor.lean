/- Lean-first (no Rocq counterpart).

`tryUpdateFor(in)` (k8setcd3.go): a `GuaranteedUpdate`'s `tryUpdate`, its closure's spec
(`tryUpdateD`: `updated`'s answer, with no TTL).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Callbacks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Obj)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev tryUpdateFor.spec : Prop :=
  ∀ (inp : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.tryUpdateFor)) (Val #inp))
  {{ (uf : GoFunc), RET #uf; tryUpdateD inp uf }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
