/- Lean-first (no Rocq counterpart).

The proof of `NewKV`: a Go map, a ghost variable for the abstract state split in halves, and a
mutex whose invariant holds the map and the lock's half.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.NewKV

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.prophkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

theorem NewKV.wp_proof : NewKV.spec (GF := GF) := by
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %mref Hm
  imod (ghostVar_alloc (GF := GF) (∅ : GMap GoString GoString)) with ⟨%γ, Hγ⟩
  icases (ghostVar_split_half γ 1 (∅ : GMap GoString GoString)).1 $$ Hγ with ⟨Hγ1, Hγ2⟩
  imod (github_com.goose_lang.primitive.init_Mutex (kvLockInv mref γ) ⊤ «$v0_ptr»)
    $$ «$v0» [Hm Hγ1] with #Hmu
  · inext; unfold kvLockInv kvState; iexists ∅; iframe Hm; iexact Hγ1
  ipersist «$r0»
  imodintro
  iapply HΦ
  unfold isKV kvState
  iframe Hγ2
  iexists «$v0_ptr», mref
  iframe «$r0» Hmu

end proof

end prophkv
end EtcdGrove
end Perennial
