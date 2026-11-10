/- Lean-first (no Rocq counterpart). The proof of `runner.genKey` (`choose` below the keys' length,
the keys not empty, the key converted to a fresh slice): proved. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.genKey.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG)) :
    runner.genKey.spec (GF := GF) (hG := hG) := by
  intro x ks
  wp_start as Hks
  iunfold runnerKeys at Hks
  icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hne⟩
  ihave %Hksn := ownSlice_len $$ Hksl
  wp_auto
  wp_apply wp_choose keys.len as %c %Hc
  have hpos : 0 < sint.Z keys.len := by
    have : ks.length ≠ 0 := by simpa using Hne
    have h4 : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
    have := Hksn.1; have := Hksn.2; omega
  have hcl : (sint.Z c).toNat < ks.length := by
    have h4 : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
    have := Hksn.1; have := Hc.2.1 hpos; omega
  have hb : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z keys.len := ⟨Hc.1, Hc.2.1 hpos⟩
  (try wp_auto)
  (try simp only [hb, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index keys (sint.Z c) ks DFrac.discard (ks[(sint.Z c).toNat]'hcl)
    Hc.1 $$ [Hksl] as -
  · iframe #; ipureintro; exact List.getElem?_eq_getElem hcl
  (try wp_auto)
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, Hcap⟩
  (try wp_auto)
  iapply HΦ
  iexists _
  iframe
  ipureintro; exact List.getElem_mem hcl

end proof

end mvccfull
end EtcdGrove
end Perennial
