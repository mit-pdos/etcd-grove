/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/commitment__recalculate.lean (241f27e).
-/
/-
The proof of `commitment__recalculate` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.commitment__recalculate
public import Dsverify.Spec.github_com.hashicorp.raft.sortUint64s
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.commitment.recalculate.wp_proof
    (wp_sortUint64s : github_com.hashicorp.raft.sortUint64s.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.commitment.recalculate.spec (GF := GF) (hG := hG) :=
  fun γ i T cm => by
  wp_start as Hinv
  unfold commitInv
  icases Hinv with ⟨%ch, %mi, %mm, %ci, %si, %n0, %p, %e, Hch, #Hchn, Hmi, Hmm, Hcc, #He, %Hdom3, #Hacks, Hci, #Hcio, #Hsip, #Hn0, %Hsi, #Hl, #HInv⟩
  obtain ⟨Hek, Hdom, Hvb⟩ := Hdom3
  wp_auto
  wp_apply (wp_map_len_lt (K := SID) (V := w64) mi mm _) $$ [$Hmm] as ⟨Hmm, %Hsz⟩
  wp_if_destruct
  · iapply HΦ
    iexists ch, mi, mm, ci, si, n0, p, e
    iframe; iframe #
    ipureintro; exact ⟨⟨Hek, Hdom, Hvb⟩, Hsi⟩
  wp_apply (wp_map_len_lt (K := SID) (V := w64) mi mm _) $$ [$Hmm] as ⟨Hmm, -⟩
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 (GMap.size mm)) (by word)) as %sl0 ⟨Hsl0, Hcap0, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := SID) (V := w64) (fun keys (k : Int) => iprop(⌜0 ≤ k⌝ ∗ ∃ sl : GoSlice,
      matched_ptr ↦ sl ∗ sl ↦* (keys.take k.toNat).map (fun j => (mm !! j).getD (W64 0)) ∗
      ownSliceCap w64 sl (DFrac.own 1) ∗ ∃ x : w64, idx_ptr ↦ x))) $$ Hmm
  iintro %keys %Hkeys
  isplitl [matched Hsl0 Hcap0 idx]
  · isplitr; · ipureintro; omega
    iexists sl0; iframe
  isplitr
  · imodintro
    iintro %k %key %v ⟨%hk1, %hk2⟩ ⟨%hk0, %sl, matched, Hsl, Hcap, %x, idx⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [v]
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hs1, Hs1cap⟩
    wp_auto
    wp_apply (wp_slice_append (V := w64) (t := go.uint64) sl _ _ [v] (DFrac.own 1))
      $$ [Hsl Hcap Hs1] as %sl' ⟨Hsl', Hcap', -⟩
    · iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; omega
    iexists sl'
    iframe
    have hk : k.toNat < keys.length := (List.getElem?_eq_some_iff.mp hk1).1
    have hk0' : (k + 1).toNat = k.toNat + 1 := by omega
    rw [hk0', List.take_succ, List.map_append, List.getElem?_eq_getElem hk]
    have hkey : keys[k.toNat] = key := by
      have := (List.getElem?_eq_some_iff.mp hk1).2; exact this
    simp only [Option.toList_some, List.map_cons, List.map_nil, hkey, hk2, Option.getD_some]
    iframe
  iintro ⟨-, %sl, matched, Hsl, Hcap, %x, idx⟩ Hmm
  obtain ⟨Hmem, Hklen, Hknd⟩ := Hkeys
  rw [show (((GMap.size mm : Nat) : Int)).toNat = keys.length by omega, List.take_length]
  imod llogIdx_cfgValid γ ⊤ (by solve_ndisj) T p e Hek $$ [HInv He] with %Hval
  · iframe #
  have hkv : keys.length = (γ.cv e.data).length := by
    refine ((List.perm_ext_iff_of_nodup Hknd Hval.2.1).mpr ?_).length_eq
    intro x; rw [Hmem]; exact Hdom x
  wp_auto
  wp_apply wp_sortUint64s $$ [$Hsl] as %xs' ⟨Hsl, %Hperm, %Hsorted⟩
  · ipureintro; simp only [List.length_map]; omega
  ihave %Hsll := ownSlice_len $$ Hsl
  have hxl : xs'.length = keys.length := by rw [← Hperm.length_eq, List.length_map]
  have hn1 : 1 ≤ xs'.length := by
    rw [hxl, Hklen]
    rcases Nat.eq_zero_or_pos (GMap.size mm) with h | h
    · exfalso; apply Hif; rw [h]; rfl
    · exact h
  have hlenZ : sint.Z sl.len = (xs'.length : Int) := by
    have h := Hsll; word
  have hidx : sint.Z (BitVec.sdiv (sl.len - W64 1) (W64 2)) = (Nat.cast ((xs'.length - 1) / 2) : Int) := by
    have : sint.Z (BitVec.sdiv (sl.len - W64 1) (W64 2)) = (sint.Z sl.len - 1) / 2 := by word
    rw [this, hlenZ]; omega
  list_elem xs' ((xs'.length - 1) / 2) as q
  rw [if_pos (show 0 ≤ sint.Z (BitVec.sdiv (sl.len - W64 1) (W64 2)) ∧
      sint.Z (BitVec.sdiv (sl.len - W64 1) (W64 2)) < sint.Z sl.len by rw [hidx]; omega)]
  wp_apply (wp_load_slice_index sl (sint.Z (BitVec.sdiv (sl.len - W64 1) (W64 2))) xs' (DFrac.own 1) q
    (by rw [hidx]; omega)) $$ [Hsl] as Hsl
  · iframe; ipureintro; rw [hidx, Int.toNat_natCast]; exact Hq_lookup
  wp_if_destruct
  · wp_if_destruct
    · -- the quorum's match index is past the commit index and the election-time log: commit
      have hk : n0 < uint.nat q := by word
      have hmono : ∀ m : w64, uint.Z q ≤ uint.Z m → uint.nat q ≤ uint.nat m ∧ 0 < uint.nat m := by
        intro m h; constructor <;> word
      let f : SID → w64 := fun j => (mm !! j).getD (W64 0)
      let Q := keys.filter (fun j => decide (uint.Z q ≤ uint.Z (f j)))
      have hquo := quorum_of_sorted keys f xs' Hperm Hsorted q Hq_lookup
      have hQmem : ∀ j ∈ Q, ∃ m, mm !! j = some m ∧ uint.Z q ≤ uint.Z m := by
        intro j hj
        have hj' := List.mem_filter.mp hj
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp ((Hmem j).mp hj'.1)
        refine ⟨m, hm, ?_⟩
        have := hj'.2; simp only [f, hm, Option.getD_some, decide_eq_true_eq] at this; exact this
      have hQ : isQuorumOf (γ.cv e.data) Q := by
        refine ⟨Hknd.filter _, ?_, ?_⟩
        · intro j hj
          obtain ⟨m, hm, -⟩ := hQmem j hj
          exact (Hdom j).mp (by rw [hm]; rfl)
        · rw [← hkv, ← hxl]; exact hquo
      ihave #Hacks' := acks_of_matches γ T mm Q (uint.nat q) (by
        intro j hj
        obtain ⟨m, hm, hqm⟩ := hQmem j hj
        exact ⟨m, hm, (hmono m hqm).1, (hmono m hqm).2⟩) $$ Hacks
      imod commit_or_snap γ ⊤ (by solve_ndisj) T (uint.nat q) n0 p i e Q hQ hk
        $$ [$HInv $Hl $Hn0 $Hcc $He $Hacks'] with ⟨Hcc, %k', %p', %Hk', #Hcommit⟩
      ihave ⟨%γc, #Hbag⟩ := notifyChan_bag ch $$ Hchn
      wp_apply wp_asyncNotifyCh $$ [$Hbag]
      ihave #Hcq : iprop(⌜q = W64 0⌝ ∨ (⌜n0 < uint.nat q⌝ ∗ ∃ k p, ⌜uint.nat q ≤ k⌝ ∗ commitIs γ T k p)) $$ []
      · iright; isplitr; · ipureintro; exact hk
        iexists k', p'; isplitr; · ipureintro; exact Hk'
        iexact Hcommit
      iapply HΦ
      iexists ch, mi, mm, q, si, n0, p, e
      iframe; iframe #
      ipureintro; exact ⟨⟨Hek, Hdom, Hvb⟩, Hsi⟩
    · iapply HΦ
      iexists ch, mi, mm, ci, si, n0, p, e
      iframe; iframe #
      ipureintro; exact ⟨⟨Hek, Hdom, Hvb⟩, Hsi⟩
  · iapply HΦ
    iexists ch, mi, mm, ci, si, n0, p, e
    iframe; iframe #
    ipureintro; exact ⟨⟨Hek, Hdom, Hvb⟩, Hsi⟩

end proof

end Perennial
