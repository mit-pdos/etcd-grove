/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`r.Update(q)` (witness.go): the compare-and-swap. If the store still holds the state the read
saw (by identity, so, by `whsRO_agree`, the same state `σ`), it now holds `q`'s, `σ'`, and the
caller's view shift `P σ ={⊤ ∖ N}=∗ P σ' ∗ Ψ` has run, under the lock; otherwise it returns raft's
`ErrWitnessStateModified` (non-nil) and hands the shift back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.DefsWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

abbrev witnessRead.Update.spec : Prop :=
  ∀ (r s : Loc) (P : WHS → IProp GF) (p : Loc) (σ : WHS) (N : Namespace) (q : Loc) (σ' : WHS)
    (Ψ : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ isWRead r s P p σ ∗ whsRO q σ' ∗ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Ψ) }}
    (App (Val (r @!! go.GoType.PointerType rWReadTy @!! go!"Update")) (Val #q))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ Ψ) ∨ (⌜err ≠ interface.nil⌝ ∗ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Ψ)) }}

end spec

end kv
end EtcdGrove
end Perennial
