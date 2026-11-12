/- Lean-first (no Rocq counterpart). The proof of `rng.genKey`: `intn(len(keys))`, then the key
at that index converted to bytes. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem rng.genKey.wp_proof (wp_intn : rng.intn.spec (GF := GF) (hG := hG)) :
    rng.genKey.spec (GF := GF) (hG := hG) := by
  intro r g
  wp_start as Hr
  ihave Hmi : (mvccrandInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold mvccrandInit at Hmi
  icases Hmi with ⟨⟨%ks, #Hks, #Hksl⟩, -⟩
  ihave %Hksn := ownSlice_len $$ Hksl
  have hks6 : sint.Z ks.len = 6 := by
    have h := Hksn.1; simp only [keyList, List.length_cons, List.length_nil] at h
    have h4 : sint.nat ks.len = (sint.Z ks.len).toNat := rfl
    have := Hksn.2; omega
  wp_auto
  wp_apply wp_intn r g ks.len (by omega) $$ [$Hr] as %x ⟨Hr, %Hx⟩
  have hxl : (sint.Z x).toNat < keyList.length := by simp [keyList]; omega
  have hb : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z ks.len := ⟨Hx.1, by omega⟩
  (try wp_auto)
  (try simp only [hb, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index ks (sint.Z x) keyList DFrac.discard (keyList[(sint.Z x).toNat]'hxl)
    Hx.1 $$ [Hksl] as -
  · iframe #; ipureintro; exact List.getElem?_eq_getElem hxl
  (try wp_auto)
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, Hcap⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; exact List.getElem_mem hxl

end proof

end mvccrand
end EtcdGrove
end Perennial
