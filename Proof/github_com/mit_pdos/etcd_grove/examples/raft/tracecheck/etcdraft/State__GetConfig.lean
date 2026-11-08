/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08): the proof of `State__GetConfig`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig

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

theorem State.GetConfig.wp_proof : State.GetConfig.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi⟩
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, #Hsrvs, #Hm, #Hpm, %Hrc⟩
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
  icases array_acc _ 0 _ _ _ a (Int.le_refl _) (by rw [Hab]; rfl) $$ Joint with ⟨Ha0, -⟩
  rw [show sint.Z (W64 0) = 0 from rfl]
  wp_auto
  iapply HΦ
  unfold State.getConfig
  iexact Ha

end proof

end Etcdraft
end EtcdGrove
end Perennial
