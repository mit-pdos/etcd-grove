/-
The proof of `writeAll` (`KvRaft/Spec/.../kvraft/writeAll.lean`): a loop over `c.Write(b)`
(`net.Conn.Write.spec`), `b` re-sliced past what each call wrote; each call's writer predicate is
the caller's `P` after the bytes written so far, its accessor the caller's. The invariant: `b` is a
suffix `rem` of the caller's bytes, `w ++ rem = bs`, with `P w none`, and a wand that gives the
caller's slice back from `b`'s.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.writeAll
public import KvRaft.Spec.net.Conn__Write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem writeAll.wp_proof (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG)) :
    writeAll.spec (GF := GF) (hG := hG) := by
  intro c cn s a b0 bs dq ed P
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, Hb, #Hed, HP, #Hacc⟩
  subst Hct
  wp_auto
  ihave HI : (∃ (cur : GoSlice) (w rem : List w8),
      "b" ∷ b_ptr ↦ cur ∗ "Hcur" ∷ cur ↦*{dq} rem ∗
      "Hback" ∷ (cur ↦*{dq} rem -∗ b0 ↦*{dq} bs) ∗ "HP" ∷ P w none ∗
      "%Hw" ∷ ⌜w ++ rem = bs⌝ : IProp GF) $$ [b Hb HP]
  · iexists b0, [], bs
    iframe b Hb HP
    isplitl
    · iintro H; iexact H
    · ipureintro; rfl
  wp_for HI
  ihave %Hlen := ownSlice_len $$ Hcur
  ihave %Hwf := ownSlice_wf $$ Hcur
  wp_if_destruct
  · -- the loop body: a write of `rem`
    (try wp_auto)
    wp_apply wp_Write t cn s a la ra cur rem dq ed (fun w' res => P (w ++ w') res) $$ [Hcur HP]
      as %n %err ⟨%w', %res, HP, Hcur, %Hout, HE⟩
    · iframe Hc Hcur Hed
      rw [List.append_nil]
      iframe HP
      imodintro
      iintro %w'' %rs %Hrs HP
      imod Hacc $$ %(w ++ w'') %rs %(by rw [List.append_assoc, Hrs, Hw]) HP
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %k %res %d' %Hwo HE HD
      rw [← List.append_assoc]
      iapply Hcl $$ %k %res %d' %Hwo HE HD
    obtain ⟨Hpre, Hn, Hnone, -⟩ := Hout
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hre
    cases res with
    | none =>
      have hw' : w' = rem := Hnone rfl
      subst hw'
      obtain rfl := Hre.1 rfl
      wp_auto
      have hn : sint.Z n = sint.Z cur.len := by rw [Hn]; word
      rw [if_pos (show 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z cur.len ∧ sint.Z cur.len ≤ sint.Z cur.cap
        from ⟨by word, by omega, Hwf.2⟩)]
      icases (ownSlice_split_all n cur dq w' ⟨by word, by omega⟩).1 $$ Hcur with ⟨H1, H2⟩
      have hnn : sint.nat n = w'.length := by
        rw [Hlen.1]; show (sint.Z n).toNat = (sint.Z cur.len).toNat; rw [hn]
      rw [hnn, List.take_length, List.drop_length]
      wp_auto
      wp_for_post
      iframe
      iexists (slice.slice cur w8 n cur.len), (w ++ w'), []
      iframe b H2 HP
      isplitl [H1 Hback]
      · iintro H2
        iapply Hback
        iapply (ownSlice_split_all n cur dq w' ⟨by word, by omega⟩).2
        rw [hnn, List.take_length, List.drop_length]
        iframe H1 H2
      · ipureintro; rw [List.append_nil]; exact Hw
    | some e =>
      obtain ⟨pe, rfl⟩ := Hre.2 (by simp)
      wp_auto
      wp_for_post
      iapply HΦ
      iexists (w ++ w'), (some e)
      ihave Hb := Hback $$ Hcur
      iframe HP Hb
      ipureintro
      refine ⟨⟨rem.drop w'.length, ?_⟩, fun h => by cases h⟩
      obtain ⟨t', rfl⟩ := Hpre
      rw [← Hw, List.append_assoc, List.drop_left]
  · -- the loop ends: nothing left
    have hz : cur.len = W64 0 := by
      rcases Classical.em (cur.len = W64 0) with h | h
      · exact h
      · exact absurd (by rw [decide_eq_false h]; rfl) Hif
    rw [if_pos (by simp [hz])]
    wp_auto
    iapply HΦ
    iexists w, none
    ihave Hb := Hback $$ Hcur
    iframe HP Hb
    have hr : rem = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1, hz]; rfl)
    subst hr
    rw [List.append_nil] at Hw
    ipureintro
    exact ⟨Hw ▸ List.prefix_refl _, fun _ => Hw⟩

end proof

end kvraft
end EtcdGrove
end Perennial
