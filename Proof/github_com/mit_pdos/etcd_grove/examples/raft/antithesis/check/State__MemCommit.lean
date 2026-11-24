/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.MemCommit` (B 139).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__MemCommit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.MemCommit.wp_proof (wp_commit : Event.commit.spec (GF := GF) (hG := hG)) :
    State.MemCommit.spec (GF := GF) (hG := hG) := by
  intro p s n c
  wp_start as ⟨#Hs, %Hn⟩
  obtain ⟨Hn0, Hlt, Hc⟩ := Hn
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases queueRO_at g.Queue' s.queue n ⟨Hn0, by rw [HWf.len_queue]; exact Hlt⟩ $$ HQueue with ⟨%qv, #Hqa, #Hq⟩
  iunfold qitemsRO at Hq
  icases Hq with ⟨%items, #Hitems, #Hb⟩
  ihave %Hil := ownSlice_len $$ Hitems
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hb
  unfold State.memCommit at Hc
  wp_auto
  wp_apply wp_load_at _ _ qv Hn0 $$ [Hqa]
  · iexact Hqa
  try wp_auto
  cases hq : s.queue[sint.nat n]! with
  | nil =>
    rw [hq] at Hc Hbl
    simp only [List.getLast?_nil] at Hc
    cases Hc
    have h0 : sint.Z qv.len = 0 := by rw [List.length_nil] at Hbl; have := Hil.1; rw [Hbl] at this; word
    rw [show qv.len = W64 0 by word]
    icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn0, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex with ⟨%ci, #Hci, %Hci⟩
    wp_auto
    wp_apply wp_load_at _ _ ci Hn0 $$ [Hci]
    · iexact Hci
    try wp_auto
    iapply HΦ; ipureintro; exact Hci
  | cons x xs =>
    rw [hq] at Hc Hbl
    obtain ⟨y, hy⟩ : ∃ y, (x :: xs).getLast? = some y := ⟨_, List.getLast?_eq_some_getLast (by simp)⟩
    rw [hy] at Hc
    simp only at Hc
    have hlen : items.length = xs.length + 1 := by rw [Hbl]; rfl
    have hpos : 0 < sint.Z qv.len := by have := Hil.1; rw [hlen] at this; word
    wp_if_destruct
    · exact absurd (by word) (show ¬ sint.Z qv.len = 0 by omega)
    try wp_auto
    have hk : sint.nat (qv.len - W64 1) = xs.length := by have := Hil.1; rw [hlen] at this; word
    have hyk : (x :: xs)[xs.length]! = y := by
      rw [List.getLast?_eq_getElem?] at hy
      simp at hy
      rw [List.getElem!_eq_getElem?_getD]; simp [hy]
    icases bigSepL2_at (fun i x => qitemRO (GF := GF) i x) items (x :: xs) xs.length (by simp) $$ Hb with ⟨%gi, %Hgi, #Hi⟩
    rw [← hyk] at Hc
    iunfold qitemRO at Hi
    icases Hi with ⟨#He, #-⟩
    rw [← hk] at Hgi
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (qv.len - W64 1) ∧ sint.Z (qv.len - W64 1) < sint.Z qv.len by word))]
    icases ownSlice_elem_acc (sint.Z (qv.len - W64 1)) gi qv DFrac.discard items (by word)
      (by rw [show (sint.Z (qv.len - W64 1)).toNat = sint.nat (qv.len - W64 1) by word]; exact Hgi) $$ Hitems
      with ⟨Hel, -⟩
    iStructNamed Hel
    try wp_auto
    wp_apply wp_commit gi.Ev' _ c $$ [He] as %u %Hu
    · iframe He; ipureintro; exact Hc
    try wp_auto
    iapply HΦ; ipureintro; exact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
