/- Lean-first (no Rocq counterpart).

`updated(in, o)` (k8setcd3.go): `errUpdateRejected`'s error on an object on the node `in.Reject` if
`in.HasReject` (`rejects`), otherwise a new object, `updGo in o` (`in`'s value, node and app, and
the key's namespace and name for an object with no name, unless `in.NoOp`; `o`'s UID and resource
version kept).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Callbacks

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
abbrev updated.spec : Prop :=
  ∀ (inp : Input) (p : Loc) (dq : DFrac) (v : Obj),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ p ↦{dq} v }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.updated)) (Val #inp))
      (Val #p))
  {{ (q : Loc) (err : GoInterface), RET (PairV #q #err); p ↦{dq} v ∗
      (if rejects inp.HasReject' inp.Reject' v.Node' then
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ err
      else ⌜err = GoInterface.nil ∧ q ≠ null⌝ ∗ q ↦ updGo inp v) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
