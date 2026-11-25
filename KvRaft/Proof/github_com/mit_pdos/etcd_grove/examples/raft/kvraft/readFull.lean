/-
The proof of `readFull` (`KvRaft/Spec/.../kvraft/readFull.lean`): a loop over `c.Read(b)`
(`net.Conn.Read.spec`), `b` re-sliced past what each read returned; each read's update made from
the caller's accessor at `m = len(b)`, its result `P (got ++ r.got)` with what `ReadOutcome` says
of the count (`readOutcome_got_le`: at most `m` bytes, and some when `m > 0`). The invariant: `b`
is the rest `rem` of the caller's slice, after the bytes `got` read so far, with `P got`, and a wand
that gives the caller's slice back, `got` followed by whatever `b` then holds.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.readFull
public import KvRaft.Spec.net.Conn__Read
public import GooseLang.Ext.Net.Stream

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
variable [package_sem' : net.Assumptions]

/-- The step past `k` bytes of `cur`: its suffix `cur[k:]` holds the rest, and gives back, with the
first `k` bytes, a slice the old wand takes. -/
theorem readFull_advance (b0 cur : GoSlice) (k : w64) (got xs rem : List w8) (L : Nat)
    (hx : xs.length = sint.nat k) (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z cur.len)
    (hL : xs.length + rem.length = L) :
    (cur ↦* (xs ++ rem) ∗
      (∀ ys : List w8, ⌜ys.length = L⌝ -∗ cur ↦* ys -∗ b0 ↦* (got ++ ys)) : IProp GF) ⊢
      slice.slice cur w8 k cur.len ↦* rem ∗
        (∀ ys : List w8, ⌜ys.length = rem.length⌝ -∗ slice.slice cur w8 k cur.len ↦* ys -∗
          b0 ↦* ((got ++ xs) ++ ys)) := by
  iintro ⟨Hcur, Hback⟩
  icases (ownSlice_split_all k cur _ (xs ++ rem) hk).1 $$ Hcur with ⟨H1, H2⟩
  rw [← hx, List.take_left, List.drop_left]
  iframe H2
  iintro %ys %hys H2
  rw [List.append_assoc]
  iapply Hback $$ %(xs ++ ys) %(by simp [hys]; omega)
  iapply (ownSlice_split_all k cur _ (xs ++ ys) hk).2
  rw [← hx, List.take_left, List.drop_left]
  iframe H1 H2

theorem readFull.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    readFull.spec (GF := GF) (hG := hG) := by
  intro c cn s a b0 bs0 P eof ed
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, Hb, #Heof, #Hed, HP, #Hacc⟩
  subst Hct
  wp_auto
  ihave HI : (∃ (cur : GoSlice) (got rem : List w8),
      "b" ∷ b_ptr ↦ cur ∗ "Hcur" ∷ cur ↦* rem ∗
      "Hback" ∷ (∀ ys : List w8, ⌜ys.length = rem.length⌝ -∗ cur ↦* ys -∗ b0 ↦* (got ++ ys)) ∗
      "HP" ∷ P got ∗ "%Hg" ∷ ⌜got.length + rem.length = bs0.length⌝ : IProp GF) $$ [b Hb HP]
  · iexists b0, [], bs0
    iframe b Hb HP
    isplitl
    · iintro %ys %- H; rw [List.nil_append]; iexact H
    · ipureintro; simp
  wp_for HI
  ihave %Hlen := ownSlice_len $$ Hcur
  ihave %Hwf := ownSlice_wf $$ Hcur
  wp_if_destruct
  · -- the loop body: a read into `cur`
    (try wp_auto)
    wp_apply wp_Read t cn s a la ra cur rem eof ed
        (fun r => iprop(P (got ++ r.got) ∗
          ⌜r.got.length ≤ cur.len.toNat ∧ (r = .bytes [] → cur.len.toNat = 0)⌝)) $$ [Hcur HP]
      as %k %err ⟨%r, %bs', ⟨HP, %Hrl0⟩, Hcur, %Hout, HE⟩
    · iframe Hc Hcur Heof Hed
      imod Hacc $$ %got %(cur.len.toNat) HP with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r %d' %Hrd HE HD
      imod Hcl $$ %r %d' %Hrd HE HD with HP
      imodintro
      iframe HP
      ipureintro
      exact readOutcome_got_le Hrd
    obtain ⟨Hrl, Hr0⟩ := Hrl0
    have hcl : BitVec.toNat cur.len = rem.length := by rw [Hlen.1]; word
    rw [hcl] at Hrl Hr0
    have hc0 : rem.length ≠ 0 := by
      intro h
      have hz : cur.len = W64 0 := by
        have : sint.nat cur.len = 0 := by rw [← Hlen.1, h]
        word
      rw [decide_eq_true hz] at Hif
      exact false_neq_true Hif
    cases r with
    | bytes bsr =>
      obtain ⟨hk, rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      simp only [ReadRes.got] at Hrl
      rw [show (ReadRes.bytes bsr).got = bsr from rfl]
      have hb1 : 1 ≤ bsr.length := by
        rcases bsr with _ | ⟨x, bsr⟩
        · exact absurd (Hr0 rfl) hc0
        · simp
      have hkn : sint.nat k = bsr.length := by rw [hk]; omega
      have hk0 : k ≠ W64 0 := by
        intro h; rw [h] at hkn; have : sint.nat (W64 0) = 0 := rfl; omega
      rw [List.take_of_length_le Hrl]
      (try wp_auto)
      rw [decide_eq_false hk0]
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z cur.len ∧ sint.Z cur.len ≤ sint.Z cur.cap
        from ⟨by word, by word, Hwf.2⟩)]
      wp_auto
      wp_for_post
      iframe
      icases readFull_advance (GF := GF) b0 cur k got bsr (rem.drop bsr.length) rem.length
          hkn.symm ⟨by word, by word⟩ (by simp; omega) $$ [Hcur Hback] with ⟨H2, Hback⟩
      · iframe Hcur Hback
      iexists (slice.slice cur w8 k cur.len), (got ++ bsr), (rem.drop bsr.length)
      iframe b H2 Hback HP
      ipureintro; simp; omega
    | eof =>
      obtain ⟨rfl, hb'⟩ := Hout
      subst bs'
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      cases err with
      | nil =>
        -- a nil `io.EOF` would not end the loop: it goes on
        wp_auto
        rw [if_pos (by exact ⟨by decide, Hwf.1, Hwf.2⟩)]
        wp_auto
        wp_for_post
        iframe
        icases readFull_advance (GF := GF) b0 cur (0 : w64) got [] rem rem.length
            rfl ⟨by decide, Hwf.1⟩ (by simp) $$ [Hcur Hback] with ⟨H2, Hback⟩
        · rw [List.nil_append]; iframe Hcur Hback
        iexists (slice.slice cur w8 (0 : w64) cur.len), (got ++ []), rem
        iframe b H2 Hback
        rw [List.append_nil]
        iframe HP
        ipureintro; omega
      | ok i =>
        wp_auto
        wp_for_post
        iapply HΦ
        ihave Hb := Hback $$ %rem %rfl Hcur
        iexists got, (got ++ rem)
        iframe HP Hb
        ipureintro
        refine ⟨by simp; omega, List.prefix_append _ _, ?_⟩
        intro h; cases h
    | err e =>
      obtain ⟨rfl, hb'⟩ := Hout
      subst bs'
      simp only [net.ReadErr]
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      wp_auto
      wp_for_post
      iapply HΦ
      ihave Hb := Hback $$ %rem %rfl Hcur
      iexists got, (got ++ rem)
      iframe HP Hb
      ipureintro
      refine ⟨by simp; omega, List.prefix_append _ _, ?_⟩
      intro h; cases h
  · -- the loop ends: `b` is empty, the caller's slice full
    have hz : cur.len = W64 0 := by
      rcases Classical.em (cur.len = W64 0) with h | h
      · exact h
      · exact absurd (by rw [decide_eq_false h]; rfl) Hif
    rw [if_pos (by simp [hz])]
    wp_auto
    iapply HΦ
    have hr : rem = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1, hz]; rfl)
    subst hr
    ihave Hb := Hback $$ %([] : List w8) %(by simp) Hcur
    iexists got, (got ++ [])
    iframe HP Hb
    ipureintro
    simp only [List.append_nil, List.length_nil, Nat.add_zero] at Hg ⊢
    exact ⟨Hg, List.prefix_refl _, fun _ => trivial⟩

end proof

end kvraft
end EtcdGrove
end Perennial
