/-
The proof of `readFull` (`Net/Spec/.../lib/remote/readFull.lean`), `wire.ReadFull`'s proof
(`Net/Proof/.../net/wire/ReadFull.lean`) for the reader predicate `recvTokL cn s P (R ++ got)`: a
loop over `c.Read(buf[n:])` (`net.Conn.Read.spec`), each read's update the law `read_au` at
`m = len(buf[n:])`, its result `recvTokL cn s P (R ++ got ++ r.got)` with what `ReadOutcome` says
of the count (`readOutcome_got_le`: at most `m` bytes, and some since `m > 0`); the invariant: the
reader has read `got` after `R`, the first `n` bytes of `buf`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.readFull
public import Net.Spec.net.Conn__Read

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
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS]

theorem buf_rejoin (buf : GoSlice) (k : w64) (xs ys : List w8) (hx : xs.length = sint.nat k)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len) :
    slice.slice buf w8 (W64 0) k ↦* xs -∗ slice.slice buf w8 k buf.len ↦* ys -∗
      (buf ↦* (xs ++ ys) : IProp GF) := by
  iintro H1 H2
  iapply (ownSlice_trivial_slice buf (DFrac.own 1) (xs ++ ys)).2
  iapply ownSlice_combine k buf (DFrac.own 1) xs ys (W64 0) buf.len
    ⟨by rw [hx]; word, by decide, hk.1, hk.2⟩ $$ H1 H2

theorem readFull.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    readFull.spec (GF := GF) (hG := hG) := by
  intro c cn s a P R buf bs0 eof ed
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, Hbuf, #Heof, #Hed, HP⟩
  subst Hct
  wp_auto
  ihave %Hlen0 := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave HI : (∃ (k : w64) (bsn got : List w8),
      "n" ∷ n_ptr ↦ k ∗ "Hbuf" ∷ buf ↦* bsn ∗ "HP" ∷ recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ got) ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len ∧ bsn.length = bs0.length ∧
        got.length = sint.nat k ∧ bsn.take (sint.nat k) = got⌝ : IProp GF)
      $$ [n Hbuf HP]
  · iexists W64 0, bs0, []
    rw [List.append_nil]
    iframe n Hbuf HP
    ipureintro
    exact ⟨by decide, by word, rfl, rfl, by simp⟩
  wp_for HI
  wp_if_destruct
  · -- the loop body: a read into `buf[k:]`
    obtain ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩ := Hinv
    rw [ite_eq_left ⟨Hk0, Hkl, Hwf.2⟩]
    icases (ownSlice_split_all k buf _ bsn ⟨Hk0, Hkl⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    wp_auto
    wp_apply wp_Read t cn s a la ra (slice.slice buf w8 k buf.len) (bsn.drop (sint.nat k)) eof ed
        (fun r => iprop(recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ (got ++ r.got)) ∗
          ⌜r.got.length ≤ (slice.slice buf w8 k buf.len).len.toNat ∧
            (r = .bytes [] → (slice.slice buf w8 k buf.len).len.toNat = 0)⌝)) $$ [Hb2 HP]
      as %k' %err ⟨%r, %bs', ⟨HP, %Hrl0⟩, Hb2, %Hout, HE⟩
    · ihave #Hio := net.connAt_io _ _ _ _ _ _ $$ Hc
      ihave #Hpoll := net.connAt_poll _ _ _ _ _ _ $$ Hc
      (try iframe Hio); (try iframe Hpoll); iframe Hc Hb2 Heof Hed
      imod read_au cn s P (R ++ got) ((slice.slice buf w8 k buf.len).len.toNat) $$ HP
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r %d' %Hrd HE HD
      imod Hcl $$ %r %d' %Hrd HE HD with ⟨HP, -⟩
      imodintro
      rw [← List.append_assoc]
      iframe HP
      ipureintro
      exact readOutcome_got_le Hrd
    have hdl : (bsn.drop (sint.nat k)).length = sint.nat buf.len - sint.nat k := by
      rw [List.length_drop, Hbl, Hlen0.1]
    have hsl : (slice.slice buf w8 k buf.len).len = buf.len - k := rfl
    have hlenk : BitVec.toNat (buf.len - k) = sint.nat buf.len - sint.nat k := by word
    obtain ⟨Hrl, Hr0⟩ := Hrl0
    rw [hsl, hlenk] at Hrl Hr0
    cases r with
    | bytes bs =>
      obtain ⟨hk', rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      simp only [ReadRes.got] at Hrl
      rw [show (ReadRes.bytes bs).got = bs from rfl]
      have hb1 : 1 ≤ bs.length := by
        rcases bs with _ | ⟨b, bs⟩
        · have := Hr0 rfl; word
        · simp
      have hbl : bs.length ≤ (bsn.drop (sint.nat k)).length := by rw [hdl]; omega
      have hk'' : sint.nat k' = bs.length := by rw [hk']; omega
      have hkk : sint.nat (k + k') = sint.nat k + bs.length := by
        have : sint.nat k + sint.nat k' ≤ sint.nat buf.len := by rw [hk'']; word
        have : 1 ≤ sint.nat k' := by rw [hk'']; exact hb1
        rw [← hk'']; word
      rw [List.take_of_length_le hbl]
      wp_auto
      wp_for_post
      iframe
      iexists (k + k'), (bsn.take (sint.nat k) ++ (bs ++ (bsn.drop (sint.nat k)).drop bs.length)),
        got ++ bs
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      iframe n Hbuf HP
      ipureintro
      have hlt : (bsn.take (sint.nat k)).length = sint.nat k := by simp; omega
      refine ⟨by word, by word, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_take, List.length_drop]; omega
      · simp only [List.length_append, Hgl, hkk]
      · rw [hkk, List.take_append, hlt, show sint.nat k + bs.length - sint.nat k = bs.length by omega,
          List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil,
          List.take_of_length_le (show (bsn.take (sint.nat k)).length ≤ sint.nat k + bs.length
            by rw [hlt]; omega), Hgt]
    | eof =>
      obtain ⟨rfl, rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      have hk0 : k + 0 = k := BitVec.add_zero k
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      rw [List.take_append_drop]
      cases err with
      | nil =>
        -- a nil `io.EOF` would not end the loop: it goes on
        wp_auto
        wp_for_post
        iframe
        iexists (k + 0), bsn, got
        rw [hk0]
        iframe n Hbuf HP
        ipureintro; exact ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩
      | ok i =>
        have hne : k + 0 ≠ buf.len := by rw [hk0]; intro h; subst h; omega
        wp_auto
        rw [decide_eq_false hne]
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iexists got, bsn
        iframe HP Hbuf
        ipureintro
        refine ⟨Hbl, ⟨bsn.drop (sint.nat k), by rw [← Hgt, List.take_append_drop]⟩, ?_⟩
        intro h; cases h
    | err e =>
      obtain ⟨rfl, rfl⟩ := Hout
      simp only [net.ReadErr]
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      ihave Hbuf := buf_rejoin buf k _ _ (by simp; word) ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      rw [List.take_append_drop]
      wp_auto
      wp_for_post
      iapply HΦ
      have hne : k + 0 ≠ buf.len := by
        intro h; rw [show k + 0 = k from BitVec.add_zero k] at h; subst h; omega
      rw [decide_eq_false hne]
      iexists got, bsn
      iframe HP Hbuf
      ipureintro
      refine ⟨Hbl, ⟨bsn.drop (sint.nat k), by rw [← Hgt, List.take_append_drop]⟩, ?_⟩
      intro h; cases h
  · -- the loop ends: `buf` is full
    obtain ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩ := Hinv
    have hk : sint.Z k = sint.Z buf.len := by omega
    have hkn : sint.nat k = bs0.length := by
      rw [Hlen0.1]; show (sint.Z k).toNat = (sint.Z buf.len).toNat; rw [hk]
    (try wp_auto)
    iapply HΦ
    iexists got, bsn
    iframe HP Hbuf
    ipureintro
    have hg : got = bsn := by rw [← Hgt, List.take_of_length_le (by omega)]
    subst hg
    exact ⟨Hbl, List.prefix_refl _, fun _ => rfl⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
