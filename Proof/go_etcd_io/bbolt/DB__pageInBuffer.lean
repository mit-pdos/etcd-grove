/-
The proof of `Spec/go_etcd_io/bbolt/DB__pageInBuffer.lean`: U4 (`notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem DB.pageInBuffer.wp_proof : DB.pageInBuffer.spec (GF := GF) (hG := hG) := by
  intro db b id Hlt Hlen Hpos
  wp_start as #Hps
  wp_auto
  have hz : sint.Z (id * W64 4096) = ((id.toNat * 4096 : Nat) : Int) := by word
  have hb : sint.Z b.len = (b.len.toNat : Int) := by word
  rw [hz, hb, ite_eq_left_of_eq_true _ _ (eq_true (⟨by omega, by omega⟩ : _ ∧ _)),
    sliceIndexRef_byte _ _ Hpos (by omega)]
  wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
