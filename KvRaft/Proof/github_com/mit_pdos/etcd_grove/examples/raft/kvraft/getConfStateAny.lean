/-
Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/getConfStateAny.lean`: the four
`getIDs.specAny`, each given whatever the one before left (a nil rest after a failure: `slice.nil ↦* []`),
then, all four `ok` and a byte left, the struct as `getConfState.wp_proof` builds it.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getConfStateAny
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getIDsAny

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- What a caller chaining decoders keeps of `getIDs.specAny`'s post: the rest holds some bytes, and
the ids some list when `ok`. -/
theorem getIDs_post_any (b ids rest : GoSlice) (dq : DFrac) (bs : List w8) (ok : Bool) :
    (if ok then ∃ (xs : List w64) (r : List w8), ⌜bs = encIDs xs ++ r⌝ ∗ ids ↦* xs ∗
        rest ↦*{dq} r ∗ (rest ↦*{dq} r -∗ b ↦*{dq} bs)
      else ⌜rest = slice.nil⌝ ∗ b ↦*{dq} bs : IProp GF) ⊢
    ∃ r : List w8, rest ↦*{dq} r ∗ (if ok then ∃ xs : List w64, ids ↦* xs else True) := by
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨%Hn, -⟩
    subst Hn
    iexists []
    isplitl
    · iapply ownSlice_nil
    itrivial
  | true =>
    simp only [↓reduceIte]
    iintro ⟨%xs, %r, -, Hids, Hr, -⟩
    iexists r
    iframe

theorem getConfState.wp_proofAny (wp_getIDs : getIDs.specAny (GF := GF) (hG := hG)) :
    getConfState.specAny (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  try wp_auto
  wp_apply wp_getIDs b dq bs $$ [$Hb] as %sv %r1 %ok1 H1
  icases getIDs_post_any _ _ _ _ _ _ $$ H1 with ⟨%b1, Hr1, Hsv⟩
  try wp_auto
  wp_apply wp_getIDs r1 dq b1 $$ [$Hr1] as %sl %r2 %ok2 H2
  icases getIDs_post_any _ _ _ _ _ _ $$ H2 with ⟨%b2, Hr2, Hsl⟩
  try wp_auto
  wp_apply wp_getIDs r2 dq b2 $$ [$Hr2] as %so %r3 %ok3 H3
  icases getIDs_post_any _ _ _ _ _ _ $$ H3 with ⟨%b3, Hr3, Hso⟩
  try wp_auto
  wp_apply wp_getIDs r3 dq b3 $$ [$Hr3] as %sn %r4 %ok4 H4
  icases getIDs_post_any _ _ _ _ _ _ $$ H4 with ⟨%b4, Hr4, Hsn⟩
  try wp_auto
  cases ok1 <;> cases ok2 <;> cases ok3 <;> cases ok4
  all_goals try wp_auto
  all_goals try (iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial)
  simp only [↓reduceIte]
  icases Hsv with ⟨%xs1, Hsv⟩
  icases Hsl with ⟨%xs2, Hsl⟩
  icases Hso with ⟨%xs3, Hso⟩
  icases Hsn with ⟨%xs4, Hsn⟩
  ihave %Hl4 := ownSlice_len _ _ _ $$ Hr4
  ihave %Hw4 := ownSlice_wf _ _ _ $$ Hr4
  cases b4 with
  | nil =>
    have Hz : sint.Z r4.len = 0 := by have := Hl4.1; have := Hl4.2; simp at *; word
    rw [decide_eq_true (by rw [Hz]; decide)]
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  | cons a r =>
  have Hl4' : sint.Z r4.len = 1 + r.length := by
    have h := Hl4.1
    simp only [List.length_cons] at h
    have := Hl4.2
    have : ((r.length + 1 : Nat) : Int) = sint.Z r4.len := by rw [h]; word
    omega
  rw [decide_eq_false (by rw [Hl4']; show ¬ (_ < (1 : Int)); omega)]
  try wp_auto
  rw [ite_eq_left (by rw [Hl4']; refine ⟨by decide, ?_⟩; show (0 : Int) < _; omega)]
  wp_apply wp_load_slice_index r4 (sint.Z (W64 0)) _ _ a
    (by decide) $$ [$Hr4] as Hr4
  · ipureintro; rfl
  try wp_auto
  rw [ite_eq_left (by rw [Hl4']; refine ⟨by decide, ?_, Hl4' ▸ Hw4.2⟩; show (1 : Int) ≤ _; omega)]
  icases (ownSlice_split_all (W64 1) r4 dq _
    ⟨by decide, by rw [Hl4']; show (1 : Int) ≤ _; omega⟩).1 $$ Hr4 with ⟨-, Hr4⟩
  simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
  iapply wp_fupd
  try wp_auto
  ihave %Hn4 := typedPointsto_not_null $$ «$v4»
  imod cellRO_alloc _ _ $$ «$v4» with #cA
  imod csPts_of_struct _
      (⟨zeroValDef, sv, sl, so, sn, «$v4_ptr», slice.nil, 0⟩ : raftpb.ConfState)
      (ConfStateM.mk xs1 xs2 xs3 xs4 (decide (a = W8 1))) ⊤ rfl $$ [-HΦ Hr4] with Hcs
  · iframe; iexact cA
  simp only [decide_eq_true Hn4]
  imodintro
  iapply HΦ
  simp only [↓reduceIte]
  iexists _, r
  iframe

end proof

end kvraft
end EtcdGrove
end Perennial
