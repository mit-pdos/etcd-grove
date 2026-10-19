/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/Main.lean`. Lean-first (no Rocq
counterpart).

`StartCluster` and `Check` are specified at any storage registry (`∀ [KVStor GF]`): the proof
allocates the registry (`kvStorInv_alloc`) and instantiates them at it. `StartCluster([]uint64{1,
2, 3})` gives the replicas (made persistent here, `↦*□`) and the client's half of the store's
state, at the empty store; `lintest.CounterClock()` a clock (its invariant at `kvClockN`, apart
from the driver's `lintestN`); `Check(kvs, clock, 4, 25)` then answers `Ok`, so the panic branch
is not taken. `receiptBound GF ≤ 2^63` gives `StartCluster`'s `≤ 2^64 - 2` and the clock's.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.StartCluster
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

/-- The namespace of `Main`'s clock's invariant. -/
abbrev kvClockN : Namespace := nroot.@"kv_clock"

theorem lintestN_kvClockN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kvClockN :=
  mask_ndot_ne' nroot "lintest" "kv_clock" (by decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem Main.wp_proof
    (wp_StartCluster : ∀ [KVStor GF], kv.StartCluster.spec (GF := GF) (hG := hG))
    (wp_Check : ∀ [KVStor GF], kv.Check.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
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
      KeyedElement none (ElementExpression go.uint64 #(W64 2)),
      KeyedElement none (ElementExpression go.uint64 #(W64 3))] = 3 := rfl
  have Hl : (([W64 1, zero_val w64, zero_val w64].set (sint.nat (W64 (0 + 1))) (W64 2)).set
      (sint.nat (W64 (0 + 1 + 1))) (W64 3)) = [W64 1, W64 2, W64 3] := rfl
  rw [Hsz, Hl]
  imod ownSlice_persist _ _ _ $$ Hvsl with #Hvsl
  wp_apply (wp_StartCluster _ (by omega)) $$ [$HstorInv $Hvsl]
    as %ksl ⟨%γr, %rs, Hks, %Hlen, #Hrs, Hval⟩
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  wp_apply wp_CounterClock kvClockN Hrb as %f ⟨%clockVal, #Hclk, Ht0⟩
  have Hne : rs ≠ [] := by intro h; rw [h] at Hlen; cases Hlen
  wp_apply wp_Check γr ksl rs clockVal (W64 0) ↑kvClockN f (W64 4) (W64 25)
    lintestN_kvClockN Hne (by decide) (by decide) (by decide) (by decide) $$ [Hval Ht0]
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
