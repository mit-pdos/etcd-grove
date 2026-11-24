/- Lean-first (no Rocq counterpart).

**The right to initialize, from the empty package state**: what a closed theorem's program starts
with (a fresh Go process, `packageState = ∅`) gives `ownInitializing`, which a generated
`wp_initialize'` takes. Moved here from `examples/lib/etcdstart/Adequacy.lean` (2026-11-24), so that
the osfs examples' crash theorems use it without importing etcd's adequacy.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section adequacy
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The right to initialize, from the empty package state.** -/
theorem ownInitializing_of_empty [hG : HeapGS .hasLC GF] (getInit : GoString → IProp GF) :
    ownGoState (∅ : GMap GoString Bool) ⊢ ownInitializing getInit := by
  iintro Hgs
  rw [ownInitializing_unseal]
  unfold ownInitializingDef
  iexists ∅
  iframe Hgs
  imodintro
  iapply BigSepM.bigSepM_empty.2
  itrivial

end adequacy

end EtcdGrove
end Perennial
