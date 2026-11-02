/-
Port of `election_proof/proof_newLogWithSize.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.newLogWithSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem newLogWithSize.wp_proof : newLogWithSize.spec (GF := GF) (hG := hG) := by
  intro si lg maxSize sn lok R b last Hlg Hmax Hbl Hl64
  subst Hlg
  wp_start as ⟨HR, #HFirstIndex, #HLastIndex, #Hlg⟩
  wp_auto
  wp_apply_raw HFirstIndex $$ [$HR]
  inext
  iintro HR
  wp_auto
  wp_apply_raw HLastIndex $$ [$HR]
  inext
  iintro HR
  wp_auto
  irename «$r0» => Hl
  generalize «$r0_ptr» = l at *
  have hbl : (b : Int) + 1 < 2 ^ 64 := by omega
  have Hb1 : W64 ((b : Int) + 1) - W64 1 = W64 (b : Int) := by
    apply BitVec.eq_of_toNat_eq; word
  have Hip : uint.Z (W64 (last : Int) + W64 1) = (last : Int) + 1 := by word
  iapply HΦ $$ %l %(W64 (last : Int) + W64 1)
  iframe HR
  isplitr
  · ipureintro; exact Hip
  iexists _
  iframe Hl
  isplitr
  · ipureintro
    exact ⟨rfl, Hb1, Hb1, Hb1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  iintro %σ %c %a %Hσ Hl #Hsto HStorage
  obtain ⟨Hpb, Hlen, Hidx, Hpend, Hfr1, Hfr2, Hsg, Hba, Hac, Hcl, Hfla, Hdt⟩ := Hσ
  have hP := uint_nat_eq σ.prev.index'
  have hc := uint_nat_eq c
  have ha := uint_nat_eq a
  have hf := uint_nat_eq σ.fl
  ihave HSt := lentStor_close (b := false) rfl sn (interface.ok si) σ $$ HStorage
  ihave #Hus := (ownSnap_None (GF := GF) null).2 $$ %rfl
  ihave #Hpk := pendKsn_none (GF := GF) null []
  ihave #Hkc := ksnCerts_nil (GF := GF) sn
  ihave #Hen := entsPts_nil (GF := GF) DFrac.discard
  ihave Hcap := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave #Hlv : isLoggerVal (GF := GF) (interface.ok lok) $$ []
  · unfold isLoggerVal; iexists lok; iframe Hlg; ipureintro; rfl
  unfold ownRaftLog
  iexists _, σ
  simp only [named, List.append_nil]
  iframe Hl Hsto HSt Hus Hpk Hkc Hen Hcap Hlv
  ipureintro
  and_intros
  all_goals (try dsimp only)
  all_goals (try simp only [List.length_nil, Nat.cast_zero, Int.add_zero, List.append_nil,
    List.take_nil, Hip, Hpend])
  have HipN : uint.nat (W64 (last : Int) + W64 1) = last + 1 := by
    have := uint_nat_eq (W64 (last : Int) + W64 1); omega
  all_goals (try first
    | with_reducible rfl | exact trivial | exact Hidx | exact List.prefix_refl _
    | (apply BitVec.eq_of_toNat_eq; rfl)
    | (simp only [List.length_nil, Nat.cast_zero]; omega)
    | (simp only [List.length_nil, Nat.cast_zero, Int.add_zero]; omega)
    | (simp; omega)
    | (intro _; exact trivial)
    | (intro h; cases h; done)
    | (intro h; exact absurd rfl h)
    | (intro _ e0 h; cases h)
    | (intro e0 h; rw [Hpend] at h; cases h)
    | (intro _; have : uint.Z (W64 0) = 0 := rfl; omega)
    | (intro _; refine ⟨by simp [storApp, Hpend], fun _ => by simp [storApp, Hpend], fun _ => rfl,
        by simp [storApp, Hpend]⟩)
    | (intro _; refine ⟨Hfr2, by omega, fun _ h => by cases h⟩)
    | (exact rfl)
    | omega)
  · intro _; rfl
  · intro i t h
    obtain ⟨h1, h2⟩ := Hdt i t h
    refine ⟨by show (i : Int) ≤ uint.Z c; omega, fun hp => ?_, by show i ≤ uint.nat c; omega⟩
    simp only at hp
    have hW : uint.Z (W64 (i : Int)) = i := uint_Z_W64 _ (by omega) (by have := uint_Z_lt c; omega)
    have := h2 (by show b ≤ i; omega)
    show plogTermAt σ.prev (σ.ents ++ []) (W64 (i : Int)) = some t
    rw [List.append_nil]
    unfold plogTermAt
    rw [if_neg (by omega)]
    exact this

end proof

end EtcdGrove
end Perennial
