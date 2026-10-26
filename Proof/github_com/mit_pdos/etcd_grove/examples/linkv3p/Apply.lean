/-
Lean-first (no Rocq counterpart).

The proof of `Apply` (the partition plan's S3a, 2026-10-20): `RandomUint64` modulo the slice's
length (non-zero: the slice is non-empty) picks an index in range; the client at it has linkvtxn's
`Apply.spec`'s premises (`clientOk`, out of the `[∗list]`), and linkvtxn's `Apply` runs the
operation with the caller's atomic update, as the closure in linkvtxn's `Check` passes it through.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Apply
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem Apply.wp_proof (wp_Apply : linkvtxn.Apply.spec (GF := GF) (hG := hG)) :
    Apply.spec (GF := GF) (hG := hG) := by
  intro _ CRE CEC γ cls clis hAs hne
  iintro #Hpkg #Plkv #Pcli #Hcls #Hok
  iintro %i
  imodintro
  iintro %Φ Hin HAU
  ihave %Hl := ownSlice_len $$ Hcls
  have hlen : clis.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  wp_func_call
  wp_call
  (try wp_auto)
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n -
  (try wp_auto)
  -- `n % len(clis)`: the length is not zero
  have hpos : 0 < sint.Z cls.len := by
    obtain ⟨h1, h2⟩ := Hl
    unfold sint.nat at h1
    show 0 < BitVec.toInt cls.len
    omega
  have hz : ¬ uint.Z cls.len = 0 := by word
  rw [if_neg hz]
  (try wp_auto)
  -- `clis[n % len(clis)]`: the remainder is below the length
  have h1 : uint.Z cls.len = sint.Z cls.len := by word
  have hposN : 0 < cls.len.toNat := by
    have : 0 < uint.Z cls.len := by word
    exact_mod_cast this
  have hu : uint.Z (n % cls.len) < uint.Z cls.len := by
    have h := Nat.mod_lt n.toNat hposN
    rw [← BitVec.toNat_umod] at h
    exact_mod_cast h
  have hs : sint.Z (n % cls.len) = uint.Z (n % cls.len) := by word
  have hbnd : 0 ≤ sint.Z (n % cls.len) ∧ sint.Z (n % cls.len) < sint.Z cls.len := by
    rw [hs, ← h1]
    exact ⟨by word, hu⟩
  have hidx : 0 ≤ sint.Z (n % cls.len) ∧ (sint.Z (n % cls.len)).toNat < clis.length := by
    have hb : 0 ≤ BitVec.toInt (n % cls.len) ∧ BitVec.toInt (n % cls.len) < BitVec.toInt cls.len :=
      hbnd
    have hl : clis.length = (BitVec.toInt cls.len).toNat := Hl.1
    show 0 ≤ BitVec.toInt (n % cls.len) ∧ (BitVec.toInt (n % cls.len)).toNat < clis.length
    omega
  simp only [hbnd, _root_.and_self, ↓reduceIte]
  list_elem clis (sint.Z (n % cls.len)).toNat as cl
  wp_apply wp_load_slice_index _ (sint.Z (n % cls.len)) clis _ cl hidx.1 $$ [] as -
  · iframe #; ipureintro; exact Hcl_lookup
  (try wp_auto)
  -- the client's premises, out of the list
  ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ c => clientOk (GF := GF) γ c) Hcl_lookup) $$ Hok
  iunfold clientOk at Hc
  icases Hc with ⟨%ms, %V, %hms, #Hncl, #Hone, #Hregs, #Hinvs⟩
  ihave #HA := wp_Apply γ cl ms V hAs hms $$ Plkv Pcli Hncl Hone Hregs Hinvs
  -- `linkvtxn.Apply(cl, input)`, with the caller's update
  wp_bind (App (App (Val _) (Val _)) (Val _))
  iapply HA $$ %i Hin
  inext
  imod HAU with ⟨%S, Hs, Hc⟩
  imodintro
  iexists S
  iframe Hs
  iintro %S' %o Hb
  imod Hc $$ Hb with HQ
  imodintro
  iintro Hio
  ihave HQ := HQ $$ Hio
  wp_auto
  iexact HQ

end proof

end linkv3p
end EtcdGrove
end Perennial
