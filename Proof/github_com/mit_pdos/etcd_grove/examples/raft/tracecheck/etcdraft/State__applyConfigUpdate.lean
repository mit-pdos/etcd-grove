/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__applyConfigUpdate`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__applyConfigUpdate
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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

theorem State.applyConfigUpdate.wp_proof (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.applyConfigUpdate.spec (GF := GF) (hG := hG) := by
  intro p st M i k
  wp_start as ⟨Hst, %Hi, %Hk1, %Hk2⟩
  wp_auto
  mut_open p, st, M, i, Hst
  ihave #Hcl0 := Hcl
  iunfold logRO at Hcl0
  icases Hcl0 with ⟨%es, #Hes, #Hel⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hell := BigSepL2.bigSepL2_length $$ Hel
  wp_auto
  have hlen : sint.Z gc.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hs1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
  have hi1 : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gc.Log'.len := by
    rw [hs1]; constructor <;> omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi1)]
  have hn : (sint.Z (k - W64 1)).toNat < es.length := by rw [Hell, hs1]; omega
  obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z (k - W64 1)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hn⟩
  obtain ⟨y, Hy⟩ : ∃ y, (st.s (uint.nat i)).log[(sint.Z (k - W64 1)).toNat]? = some y :=
    ⟨_, List.getElem?_eq_getElem (Hell ▸ hn)⟩
  ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hx Hy $$ Hel
  iunfold entryRO at Hxy
  icases Hxy with ⟨%Hxy1, #Hval⟩
  wp_apply wp_load_slice_index _ (sint.Z (k - W64 1)) es DFrac.discard x hi1.1 $$ [Hes] as -
  · isplitr
    · iexact Hes
    ipureintro; exact Hx
  try wp_auto
  obtain ⟨nc, ln, hncl⟩ : ∃ nc ln, (match y.value with | .conf nc ln => (nc, ln) | _ => ([], [])) = (nc, ln) :=
    ⟨_, _, rfl⟩
  ihave #Hcfg : iprop(setRO (GF := GF) x.Value'.NewConf' nc ∗ setRO x.Value'.Learners' ln) $$ [Hval]
  · cases hv : y.value with
    | val n =>
      simp only [hv, Prod.mk.injEq] at hncl
      obtain ⟨rfl, rfl⟩ := hncl
      iunfold valueRO at Hval
      icases Hval with ⟨-, #H1, #H2⟩
      iframe H1 H2
    | emptySeq =>
      simp only [hv, Prod.mk.injEq] at hncl
      obtain ⟨rfl, rfl⟩ := hncl
      iunfold valueRO at Hval
      icases Hval with ⟨-, #H1, #H2⟩
      iframe H1 H2
    | conf a b =>
      simp only [hv, Prod.mk.injEq] at hncl
      obtain ⟨rfl, rfl⟩ := hncl
      iunfold valueRO at Hval
      icases Hval with ⟨-, #H1, #H2⟩
      iframe H1 H2
  icases Hcfg with ⟨#Hnc, #Hln⟩
  ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) DfracDiscarded
  ihave #Hcfg' : configRO (GF := GF)
      { Joint' := array.mk 2 (((List.replicate 2 (zero_val GoSlice)).set 0 x.Value'.NewConf').set
          (sint.nat (W64 (0 + 1))) slice.nil), Learners' := x.Value'.Learners' }
      { incoming := nc, outgoing := [], learners := ln } $$ []
  · iunfold configRO
    iexists x.Value'.NewConf', slice.nil
    isplitr
    · ipureintro; rfl
    iframe Hnc Hln
    iunfold setRO
    iexists []
    iframe Hnil
    ipureintro; rfl
  close_copy' ({ gc with Config' := { Joint' := array.mk 2 (((List.replicate 2 (zero_val GoSlice)).set 0
      x.Value'.NewConf').set (sint.nat (W64 (0 + 1))) slice.nil), Learners' := x.Value'.Learners' } } : G.Server),
    (fun v => { v with config := { incoming := nc, outgoing := [], learners := ln } }), Hcf
    with Hcl Hcr Hcg Hcfg' Hcd
  iapply HΦ
  have hk1 : sint.nat k - 1 = (sint.Z (k - W64 1)).toNat := by
    rw [hs1]; have : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    omega
  have : st.applyConfigUpdate (uint.nat i) (sint.nat k) =
      st.upd (uint.nat i) (fun v => { v with config := { incoming := nc, outgoing := [], learners := ln } }) := by
    unfold State.applyConfigUpdate
    rw [hk1, Hy]
    cases hv : y.value <;> simp only [hv, Prod.mk.injEq] at hncl <;> obtain ⟨rfl, rfl⟩ := hncl <;>
      simp only [Option.map_some, hv]
  rw [this]
  iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
