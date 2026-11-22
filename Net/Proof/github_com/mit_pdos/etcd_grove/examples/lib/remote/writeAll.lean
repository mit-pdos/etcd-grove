/-
The proof of `writeAll` (`Net/Spec/.../lib/remote/writeAll.lean`): a loop over `c.Write(b)`
(`net.Conn.Write.spec` with the writer predicate `writeP` and the law `write_acc`), each call
writing a prefix of the bytes left, then `b = b[n:]`; the invariant: the writer has written a
prefix `w` of `bs` after `W0`, and `b` is the rest of the original slice (`bs.drop w.length`), with
a wand giving the original slice back.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.writeAll
public import Net.Spec.net.Conn__Write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem writeAll.wp_proof (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG)) :
    writeAll.spec (GF := GF) (hG := hG) := by
  intro c cn s a P W0 b bs dq ed
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, Hb, #Hed, Htok, #HP⟩
  subst Hct
  wp_auto
  ihave HI : (∃ (b' : GoSlice) (w : List w8), "b" ∷ b_ptr ↦ b' ∗
      "Hb" ∷ b' ↦*{dq} bs.drop w.length ∗
      "Hback" ∷ (b' ↦*{dq} bs.drop w.length -∗ b ↦*{dq} bs) ∗
      "Htok" ∷ sendTok (Gg := hG.goose_globalGS) cn s P (W0 ++ w) ∗
      "%Hw" ∷ ⌜w <+: bs⌝ : IProp GF) $$ [b Hb Htok]
  · iexists b, []
    simp only [List.length_nil, List.drop_zero, List.append_nil]
    iframe b Hb Htok
    isplitl []
    · iintro H; iexact H
    · ipureintro; exact List.nil_prefix
  wp_for HI
  wp_if_destruct
  · -- the loop body: a write of the rest
    have hrest : (W0 ++ w) ++ bs.drop w.length = W0 ++ bs := by
      obtain ⟨t', rfl⟩ := Hw; simp
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    wp_apply wp_Write t cn s a la ra b' (bs.drop w.length) dq ed (writeP cn s P (W0 ++ w))
        $$ [Hb Htok] as %n %err ⟨%w2, %res, Htok, Hb, %Hw2, #HE⟩
    · iframe Hc Hb Hed
      isplitl [Htok]
      · iapply writeP_init $$ Htok
      · iapply write_acc cn s P (W0 ++ w) (bs.drop w.length)
        rw [hrest]; iexact HP
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨hw2, hn, hnone, -⟩ := Hw2
    unfold writeP
    cases res with
    | some k =>
      -- the write failed: return false
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_for_post
      ihave Hb := Hback $$ Hb
      iapply HΦ
      iexists w ++ w2
      rw [← List.append_assoc]
      iframe Hb Htok
      ipureintro
      refine ⟨?_, fun h => by cases h⟩
      obtain ⟨t', ht⟩ := hw2
      refine ⟨t', ?_⟩
      obtain ⟨t'', rfl⟩ := Hw
      simp only [List.drop_left] at ht
      rw [List.append_assoc, ht]
    | none =>
      have hw2r := hnone rfl
      have herr := Hne.1 rfl
      subst herr hw2r
      dsimp only
      wp_auto
      -- everything was written: `b = b[n:]` is empty
      have hwb : w ++ bs.drop w.length = bs := by obtain ⟨t', rfl⟩ := Hw; simp
      have hnl : sint.nat n = (bs.drop w.length).length := by
        rw [hn, Hlen.1]; word
      have hnZ : sint.Z n = sint.Z b'.len := by
        have := Hlen.1; rw [← hnl] at this; word
      rw [ite_eq_left ⟨by omega, by omega, Hwf.2⟩]
      icases (ownSlice_split_all n b' dq _ ⟨by omega, by omega⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
      wp_auto
      wp_for_post
      iframe
      iexists (slice.slice b' w8 n b'.len), w ++ bs.drop w.length
      have hd1 : (bs.drop w.length).drop (sint.nat n) = [] := by rw [hnl, List.drop_length]
      have hd2 : bs.drop (w ++ bs.drop w.length).length = [] := by rw [hwb]; simp
      rw [hd1] at *
      rw [hd2, ← List.append_assoc, hwb]
      iframe b Hb2 Htok
      isplitl [Hb1 Hback]
      · iintro H2
        ihave H := ownSlice_combine n b' dq ((bs.drop w.length).take (sint.nat n)) [] (W64 0)
          b'.len ⟨by rw [List.length_take, ← hnl, Nat.min_self, show sint.nat (W64 0) = 0 from rfl,
            Nat.sub_zero], by decide, by word, by omega⟩
          $$ Hb1 H2
        ihave H := (ownSlice_trivial_slice b' dq _).2 $$ H
        iapply Hback
        rw [List.append_nil, List.take_of_length_le (by omega)]
        iexact H
      · ipureintro; exact List.prefix_refl _
  · -- the loop ends: nothing is left
    have h0 : b'.len = W64 0 := by
      apply Classical.byContradiction; intro h; apply Hif; rw [decide_eq_false h]; rfl
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    simp only [h0, _root_.decide_true, Bool.not_true, ↓reduceIte]
    wp_auto
    ihave Hb := Hback $$ Hb
    iapply HΦ
    iexists w
    have hw : w = bs := by
      rw [h0] at Hlen
      have : (bs.drop w.length).length = 0 := by rw [Hlen.1]; rfl
      obtain ⟨t', rfl⟩ := Hw
      simp at this; subst this; simp
    subst hw
    iframe Hb Htok
    ipureintro; exact ⟨List.prefix_refl _, fun _ => rfl⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
