/-
The trust boundary of the `cellmint` cell: the Hoare triples of its operations, as axioms, as
`rate.Limiter`'s and `bytes.Buffer`'s are (`Defs.lean` states them; a `Cell` is safe for
concurrent use, so the operations are not translated through their mutex but trusted).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section trusted
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Readings of a cell agree**: two `seen` facts for the same cell carry the same value. -/
axiom cellmint.seen_agree (γ : CellNames) (v w : w64) :
    ⊢ seen (GF := GF) γ v -∗ seen γ w -∗ ⌜v = w⌝

axiom cellmint.New.wp_proof : cellmint.New.spec (GF := GF) (hG := hG)
axiom cellmint.Lock.wp_proof : cellmint.Lock.spec (GF := GF) (hG := hG)
axiom cellmint.Unlock.wp_proof : cellmint.Unlock.spec (GF := GF) (hG := hG)
axiom cellmint.Get.wp_proof : cellmint.Get.spec (GF := GF) (hG := hG)
axiom cellmint.Set.wp_proof : cellmint.Set.spec (GF := GF) (hG := hG)
axiom cellmint.Snapshot.wp_proof : cellmint.Snapshot.spec (GF := GF) (hG := hG)

end trusted

end EtcdGrove
end Perennial
