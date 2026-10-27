/- Lean-first (no Rocq counterpart).

`validateFor(reject)` (k8setcd3.go): a `Delete`'s `validateDeletion`, its closure's spec
(`validateD`: `nil`, or `errDeleteRejected`'s error on an object of value `reject`).
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
abbrev validateFor.spec : Prop :=
  ∀ (reject : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.validateFor)) (Val #reject))
  {{ (vf : GoFunc), RET #vf; validateD reject vf }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
