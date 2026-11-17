/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08): the proof of `State__mut`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server__copy

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

theorem State.mut.wp_proof
    (wp_Server_copy : Server.copy.spec (GF := GF) (hG := hG)) :
    State.mut.spec (GF := GF) (hG := hG) := by
  intro p st M i
  wp_start as ⟨Hst, %Hi⟩
  iunfold stateOwn at Hst
  icases Hst with ⟨%g, %sm, Hp, #Hsrv, Hm, %Hkeys, %Hnd, Hsrvs, #Hb1, #Hb2, %Hrc⟩
  ihave %Hbnd : ⌜∀ j ∈ st.server, j < 2 ^ 64⌝ $$ [Hsrv]
  · iunfold setRO at Hsrv
    icases Hsrv with ⟨%xs, -, %Hxs⟩
    ipureintro; intro j hj
    rw [← Hxs, List.mem_map] at hj
    obtain ⟨x, -, rfl⟩ := hj
    exact x.isLt
  have Hinj : ∀ j ∈ st.server, W64 (Int.ofNat j) = i → j = uint.nat i := by
    intro j hj h
    rw [← h, uint_nat_W64_of_lt j (Hbnd j hj)]
  obtain ⟨l1, l2, Hsplit⟩ := List.append_of_mem Hi
  have hnd' := Hnd
  rw [Hsplit] at hnd'
  have hi1 : uint.nat i ∉ l1 := by
    intro h
    exact (List.nodup_append.1 hnd').2.2 _ h _ List.mem_cons_self rfl
  have hi2 : uint.nat i ∉ l2 := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
  have Hii : W64 (Int.ofNat (uint.nat i)) = i := by apply BitVec.eq_of_toNat_eq; simp
  rw [Hsplit]
  icases BigSepL.bigSepL_append.1 $$ Hsrvs with ⟨H1, H2⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hi0, H2⟩
  icases Hi0 with ⟨%q0, %Hq0, Hs0⟩
  -- server `i` may be a copy already (a second `mut` of `i` on one clone, as `reconfigure` and
  -- `ApplySimpleConfChange` do): frozen first, then copied again (review round 4 of layer C, F1)
  ihave Hs0 : |==> serverRO q0 (st.s (uint.nat i)) $$ [Hs0]
  · by_cases hiM : uint.nat i ∈ M
    · simp only [hiM, ite_true]; iapply serverOwn_persist; iexact Hs0
    · simp only [hiM, ite_false]; imodintro; iexact Hs0
  imod Hs0
  rw [Hii] at Hq0
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpnn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hm] as Hm
  · iexact Hm
  rw [Hq0]
  simp only [Option.getD_some]
  wp_apply wp_Server_copy $$ [Hs0] as %c Hc
  · iexact Hs0
  wp_auto
  wp_apply wp_mapInsert $$ [Hm] as Hm
  · iexact Hm
  wp_auto
  ihave Hp : p ↦ ({ g with S' := g.S' } : G.State) $$ [-HΦ Hm Hc H1 H2]
  · iapply typedPointsto_combine _ _ _ Hpnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe Hc
  iunfold stateOwnHole
  iexists g, (<[i := c]> sm)
  rw [Hsplit] at Hkeys ⊢
  iframe Hp Hm Hsrv Hb1 Hb2
  isplitr
  · ipureintro; intro k
    by_cases hk : k = i
    · subst hk; rw [GMap.lookup_insert]; simp only [Option.isSome_some, true_iff]; exact (Hkeys _).1 (by rw [Hq0]; rfl)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact Hkeys k
  isplitr
  · ipureintro; exact hnd'
  isplitr
  · ipureintro; rw [Hii, GMap.lookup_insert]
  isplitl [H1 H2]
  · iapply BigSepL.bigSepL_append.2
    isplitl [H1]
    · iapply (BigSepL.bigSepL_mono (fun {_ j} hj => ?_)) $$ H1
      have hji : j ≠ uint.nat i := fun h => hi1 (h ▸ List.mem_of_getElem? hj)
      have hw : W64 (Int.ofNat j) ≠ i := fun h =>
        hji (Hinj j (by rw [Hsplit]; exact List.mem_append_left _ (List.mem_of_getElem? hj)) h)
      simp only [hji, ite_false, GMap.lookup_insert_ne _ _ (Ne.symm hw)]
      exact .rfl
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · simp only [ite_true]; iempintro
    iapply (BigSepL.bigSepL_mono (fun {_ j} hj => ?_)) $$ H2
    have hji : j ≠ uint.nat i := fun h => hi2 (h ▸ List.mem_of_getElem? hj)
    have hw : W64 (Int.ofNat j) ≠ i := fun h =>
      hji (Hinj j (by rw [Hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_getElem? hj))) h)
    simp only [hji, ite_false, GMap.lookup_insert_ne _ _ (Ne.symm hw)]
    exact .rfl
  ipureintro; exact Hrc

end proof

end Etcdraft
end EtcdGrove
end Perennial
