/- Lean-first (no Rocq counterpart).

`updated(in, o)` (k8setcd3.go): `errUpdateRejected`'s error on an object of value `in.Reject`
(`rejects`), otherwise a new object, `o` with the value `in.Val` unless `in.NoOp` (`o`'s resource version kept).
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
abbrev updated.spec : Prop :=
  ∀ (inp : Input) (p : Loc) (dq : DFrac) (name vl : GoString) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      p ↦{dq} Obj.mk name vl n }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.updated)) (Val #inp))
      (Val #p))
  {{ (q : Loc) (err : GoInterface), RET (PairV #q #err); p ↦{dq} Obj.mk name vl n ∗
      (if rejects inp.Reject' vl then
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ err
      else ⌜err = GoInterface.nil ∧ q ≠ null⌝ ∗
        q ↦ Obj.mk name (if inp.NoOp' then vl else inp.Val') n) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
