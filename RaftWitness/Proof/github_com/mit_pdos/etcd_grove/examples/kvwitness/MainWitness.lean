/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/MainWitness.lean`. Lean-first
(2026-10-20, W4): `Main`'s (`Main.lean`), on `StartClusterWitness([]uint64{1, 2}, 3)`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.MainWitness
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.StartClusterWitness
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Alloc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

/-- The namespace of `MainWitness`'s clock's invariant. -/
abbrev kvClockWN : Namespace := nroot.@"kv_clock"

theorem lintestN_kvClockWN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kvClockWN :=
  mask_ndot_ne' nroot "lintest" "kv_clock" (by decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem MainWitness.wp_proof
    (wp_StartClusterWitness : ∀ [KVStor GF], kv.StartClusterWitness.spec (GF := GF) (hG := hG))
    (wp_Check : ∀ [KVStor GF], kv.Check.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG)) :
    MainWitness.spec (GF := GF) (hG := hG) := by
  intro Hrb
  wp_start as #Hcc
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorRec) with ⟨%γreg, Hreg⟩
  letI : KVStor GF := ⟨γreg⟩
  imod kvStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %vsl ⟨Hvsl, -⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementExpression go.uint64 #(W64 1)),
      KeyedElement none (ElementExpression go.uint64 #(W64 2))] = 2 := rfl
  have Hl : (([W64 1, zero_val w64].set (sint.nat (W64 (0 + 1))) (W64 2))) = [W64 1, W64 2] := rfl
  rw [Hsz, Hl]
  imod ownSlice_persist _ _ _ $$ Hvsl with #Hvsl
  wp_apply (wp_StartClusterWitness _ (by omega)) $$ [$HstorInv $Hvsl]
    as %ksl ⟨%γr, %rs, Hks, %Hlen, #Hrs, Hval⟩
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  wp_apply wp_CounterClock kvClockWN Hrb as %f ⟨%clockVal, #Hclk, Ht0⟩
  have Hne : rs ≠ [] := by intro h; rw [h] at Hlen; cases Hlen
  wp_apply wp_Check γr ksl rs clockVal (W64 0) ↑kvClockWN f (W64 4) (W64 25)
    lintestN_kvClockWN Hne (by decide) (by decide) (by decide) (by decide) $$ [Hval Ht0]
    as %r %Hr
  · iframe
    iframe #
  subst Hr
  wp_auto
  iapply HΦ
  itrivial

end proof

end kv
end EtcdGrove
end Perennial
