/-
`cPost_if`, out of `Apply.lean`'s proof so that the apply function's variants (`ApplyFnAdmin`,
`ApplyFnKVL`, `ApplyRec`) import it without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `cPost v3 Pre Post φ` is `if v3 then Post ∨ (Pre ∗ ⌜φ⌝) else Pre`. -/
theorem cPost_if (v3 : Bool) (Pre Post : IProp GF) (φ : Prop) :
    apply.cPost v3 Pre Post φ ⊢ (if v3 then iprop(Post ∨ (Pre ∗ ⌜φ⌝)) else Pre) := by
  cases v3 <;> simp only [apply.cPost, Bool.false_eq_true, ↓reduceIte] <;> iintro H <;> iexact H

end proof

end EtcdGrove
end Perennial
