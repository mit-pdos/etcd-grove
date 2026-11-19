/- Lean-first (no Rocq counterpart).

`validateFor(rejects, reject)` (k8setcd3.go): a `Delete`'s `validateDeletion`, a closure (not the
nil func) with its spec (`validateD`: `nil`, or `errDeleteRejected`'s error on an object on the node `reject` if `rejects`) and its captured cells (`validatePin`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClosPin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev validateFor.spec : Prop :=
  ∀ (has : Bool) (reject : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.validateFor)) (Val #has)) (Val #reject))
  {{ (vf : GoFunc), RET #vf; ⌜vf ≠ func.nil⌝ ∗ validateD has reject vf ∗ validatePin has reject vf }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
