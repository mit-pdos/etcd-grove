/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__IsJointConfig`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__IsJointConfig

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem State.IsJointConfig.wp_proof : State.IsJointConfig.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi⟩
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hm, #Hpm, %Hrc⟩
  -- server i's pointer, from the servers' list
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 Hi
  icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s j))) (List.getElem?_eq_some_iff.2 ⟨hk, hki⟩)) $$ Hsrvs with ⟨%q, %Hq, #Hsv⟩
  have Hii : W64 (Int.ofNat (uint.nat i)) = i := by apply BitVec.eq_of_toNat_eq; simp
  rw [Hii] at Hq
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  wp_apply wp_map_lookup1 $$ [HS] as -
  · iexact HS
  rw [Hq]
  simp only [Option.getD_some]
  iunfold serverRO at Hsv
  icases Hsv with ⟨%gs, %mm, #Hq', %Hpure, #Hlog, #Hvr, #Hvg, #Hmm, %Hmi, #Hcfg, #Hdur⟩
  icases typedPointsto_split _ _ _ $$ Hq' with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hqf
  wp_auto
  iunfold configRO at Hcfg
  icases Hcfg with ⟨%a, %b, %Hab, #Ha, #Hb, #Hl⟩
  icases typedPointsto_split _ _ _ $$ Config with Hcf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  icases array_acc _ 1 _ _ _ b (by decide) (by rw [Hab]; rfl) $$ Joint with ⟨Hb0, -⟩
  rw [show sint.Z (W64 1) = 1 from rfl]
  iunfold setRO at Hb
  icases Hb with ⟨%xs, #Hxs, %Hxm⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  wp_auto
  have : (!decide (b.len = W64 0)) = st.isJointConfig (uint.nat i) := by
    unfold State.isJointConfig
    rw [← Hxm]
    cases xs with
    | nil =>
      have : b.len = W64 0 := by simp at Hxl; word
      simp [this]
    | cons x xs =>
      have : b.len ≠ W64 0 := by
        intro e; have h1 := Hxl.1; simp only [List.length_cons] at h1
        rw [e, show sint.nat (W64 0) = 0 from rfl] at h1; omega
      rw [decide_eq_false this]; rfl
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
