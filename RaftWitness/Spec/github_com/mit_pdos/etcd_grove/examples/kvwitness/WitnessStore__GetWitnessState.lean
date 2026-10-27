/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`s.GetWitnessState()` (witness.go): a read of the state stored, under the lock: the caller's view
shift runs on the state's ghost counterpart there; the read (`isWRead`) is of that state. The
interface value it returns is the read's (`*witnessRead`); it never fails.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.DefsWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

abbrev WitnessStore.GetWitnessState.spec : Prop :=
  ∀ (s : Loc) (P : WHS → IProp GF) (N : Namespace) (Ψ : WHS → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ isWStore s P ∗ (∀ σ, P σ ={⊤ \ ↑N}=∗ P σ ∗ Ψ σ) }}
    (App (Val (s @!! go.GoType.PointerType rWStoreTy @!! go!"GetWitnessState")) (Val #()))
  {{ (sv : GoInterface) (err : GoInterface), RET (PairV #sv #err);
      ⌜err = interface.nil⌝ ∗ ∃ (r p : Loc) (σ : WHS),
        ⌜sv = interface.mkOk (go.GoType.PointerType rWReadTy) #r⌝ ∗ isWRead r s P p σ ∗ Ψ σ }}

end spec

end kvwitness
end EtcdGrove
end Perennial
