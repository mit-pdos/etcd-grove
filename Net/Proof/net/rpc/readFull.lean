/-
The proof of `readFull` (`Net/Spec/net/rpc/readFull.lean`), after `wire.ReadFull`'s: a loop over
`r.Read(b[n:])` (`net.Conn.Read.spec`), each read's update made from the caller's accessor at
`m = len(b[n:])`; the invariant: `P got` with `got` the first `n` bytes of `b`. The errors: the
`Read`'s error compared against `io.EOF` (an `*errors.errorString`, never the `Read`'s
`*OpError`).
-/
module

public import Net.Spec.net.rpc.readFull
public import Net.Spec.net.Conn__Read
public import GooseLang.Ext.Net.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The two parts of `b` split at `k`, joined back (as `wire.ReadFull`'s proof). -/
theorem buf_rejoin (b : GoSlice) (k : w64) (xs ys : List w8) (hx : xs.length = sint.nat k)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z b.len) :
    slice.slice b w8 (W64 0) k ↦* xs -∗ slice.slice b w8 k b.len ↦* ys -∗
      (b ↦* (xs ++ ys) : IProp GF) := by
  iintro H1 H2
  iapply (ownSlice_trivial_slice b (DFrac.own 1) (xs ++ ys)).2
  iapply ownSlice_combine k b (DFrac.own 1) xs ys (W64 0) b.len
    ⟨by rw [hx]; word, by decide, hk.1, hk.2⟩ $$ H1 H2

theorem readFull.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    readFull.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs0 first P F eof ueof ed
  wp_start as ⟨#Hc, Hbuf, #Hio, #Heof, #Hueof, #Hed, HP, #Hacc⟩
  ihave #HEOF := io.eof_of_init $$ Hio
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  icombine Heof Hxe gives %Heq
  subst Heq
  wp_auto
  ihave %Hlen0 := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave HI : (∃ (k : w64) (bsn got : List w8),
      "n" ∷ n_ptr ↦ k ∗ "Hbuf" ∷ b ↦* bsn ∗ "HP" ∷ P got ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z b.len ∧ bsn.length = bs0.length ∧
        got.length = sint.nat k ∧ bsn.take (sint.nat k) = got⌝ : IProp GF)
      $$ [n Hbuf HP]
  · iexists W64 0, bs0, []
    iframe n Hbuf HP
    ipureintro
    exact ⟨by decide, by word, rfl, rfl, by simp⟩
  wp_for HI
  wp_if_destruct
  · -- the loop body: a read into `b[k:]`
    obtain ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩ := Hinv
    have hlt : sint.Z k < sint.Z b.len := by assumption
    have hklt : sint.nat k < bsn.length := by
      have : sint.nat k = (sint.Z k).toNat := rfl
      have : sint.nat b.len = (sint.Z b.len).toNat := rfl
      omega
    rw [ite_eq_left ⟨Hk0, Hkl, Hwf.2⟩]
    icases (ownSlice_split_all k b _ bsn ⟨Hk0, Hkl⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    wp_auto
    wp_apply wp_Read t cn s a la ra (slice.slice b w8 k b.len) (bsn.drop (sint.nat k))
        (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun r => iprop(P (got ++ r.got) ∗ (⌜∀ bs, r ≠ .bytes bs⌝ -∗ F) ∗
          ⌜r.got.length ≤ (slice.slice b w8 k b.len).len.toNat ∧
            (r = .bytes [] → (slice.slice b w8 k b.len).len.toNat = 0)⌝)) $$ [Hb2 HP]
      as %k' %err ⟨%r, %bs', ⟨HP, HF, %Hrl0⟩, Hb2, %Hout, HE⟩
    · iframe Hc Hb2 Heof Hed
      imod Hacc $$ %got %((slice.slice b w8 k b.len).len.toNat) HP
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r %d' %Hrd HE HD
      imod Hcl $$ %r %d' %Hrd HE HD with ⟨HP, HF⟩
      imodintro
      iframe HP HF
      ipureintro
      exact readOutcome_got_le Hrd
    have hdl : (bsn.drop (sint.nat k)).length = sint.nat b.len - sint.nat k := by
      rw [List.length_drop, Hbl, Hlen0.1]
    have hsl : (slice.slice b w8 k b.len).len = b.len - k := rfl
    have hlenk : BitVec.toNat (b.len - k) = sint.nat b.len - sint.nat k := by word
    obtain ⟨Hrl, Hr0⟩ := Hrl0
    rw [hsl, hlenk] at Hrl Hr0
    have htk : (bsn.take (sint.nat k)).length = sint.nat k := by simp; omega
    have hk0 : k + 0 = k := BitVec.add_zero k
    have hne : k + 0 ≠ b.len := by
      rw [hk0]; intro h; rw [h] at hlt; exact Int.lt_irrefl _ hlt
    have hgot : got ≠ bsn := by
      intro h; rw [h] at Hgl; exact Nat.ne_of_gt hklt Hgl
    have hpre : got <+: bsn := ⟨bsn.drop (sint.nat k), by rw [← Hgt, List.take_append_drop]⟩
    cases r with
    | bytes bs =>
      obtain ⟨hk', rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      simp only [ReadRes.got] at Hrl
      rw [show (ReadRes.bytes bs).got = bs from rfl]
      have hb1 : 1 ≤ bs.length := by
        rcases bs with _ | ⟨x, bs⟩
        · have := Hr0 rfl; word
        · simp
      have hbl : bs.length ≤ (bsn.drop (sint.nat k)).length := by rw [hdl]; omega
      have hk'' : sint.nat k' = bs.length := by rw [hk']; omega
      have hkk : sint.nat (k + k') = sint.nat k + bs.length := by
        have : sint.nat k + sint.nat k' ≤ sint.nat b.len := by rw [hk'']; word
        have : 1 ≤ sint.nat k' := by rw [hk'']; exact hb1
        rw [← hk'']; word
      rw [List.take_of_length_le hbl]
      ihave Hbuf := buf_rejoin b k _ _ htk ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      wp_if_destruct
      · -- `b` is full: `nil`
        have Hfull : k + k' = b.len := by assumption
        have hfull : sint.nat k + bs.length = bsn.length := by
          rw [← hkk, Hfull, Hbl, Hlen0.1]
        have hlen' : (bsn.take (sint.nat k) ++ bs).length = bs0.length := by
          rw [List.length_append, htk, hfull, Hbl]
        have hdrop : (bsn.drop (sint.nat k)).drop bs.length = [] := by
          rw [List.drop_drop]; apply List.drop_of_length_le; exact Nat.le_of_eq hfull.symm
        rw [hdrop, List.append_nil]
        wp_for_post
        iapply HΦ
        iexists got ++ bs, bsn.take (sint.nat k) ++ bs
        iframe HP Hbuf
        isplitr
        · ipureintro
          exact ⟨hlen', by rw [Hgt]; exact List.prefix_refl _⟩
        ileft
        ipureintro
        exact ⟨rfl, by rw [Hgt]⟩
      · -- not yet: the next read
        wp_for_post
        iframe
        iexists (k + k'), (bsn.take (sint.nat k) ++ (bs ++ (bsn.drop (sint.nat k)).drop bs.length)),
          got ++ bs
        iframe n Hbuf HP
        ipureintro
        refine ⟨by word, by word, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_take, List.length_drop]; omega
        · simp only [List.length_append, Hgl, hkk]
        · rw [hkk, List.take_append, htk, show sint.nat k + bs.length - sint.nat k = bs.length by omega,
            List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil,
            List.take_of_length_le (show (bsn.take (sint.nat k)).length ≤ sint.nat k + bs.length
              by rw [htk]; omega), Hgt]
    | eof =>
      obtain ⟨rfl, rfl⟩ := Hout
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      ihave Hbuf := buf_rejoin b k _ _ htk ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      rw [List.take_append_drop]
      rw [decide_eq_false hne]
      wp_auto
      rw [hk0]
      by_cases hk : sint.Z (W64 0) < sint.Z k
      · rw [decide_eq_true hk]
        wp_auto
        wp_for_post
        iapply HΦ
        iexists got, bsn
        iframe HP Hbuf
        isplitr
        · ipureintro; exact ⟨Hbl, hpre⟩
        iright
        isplitr
        · ipureintro; exact hgot
        isplitr
        · unfold readErr
          iright; ileft; ipureintro; rfl
        iapply HF; ipureintro; intro _ h; cases h
      rw [decide_eq_false hk]
      have hk00 : sint.nat k = 0 := by
        have : sint.Z (W64 0) = 0 := by decide
        have : sint.nat k = (sint.Z k).toNat := rfl
        omega
      have hg0 : got = [] := by rw [← List.length_eq_zero_iff, Hgl, hk00]
      cases first
      · wp_auto
        wp_for_post
        iapply HΦ
        iexists got, bsn
        iframe HP Hbuf
        isplitr
        · ipureintro; exact ⟨Hbl, hpre⟩
        iright
        isplitr
        · ipureintro; exact hgot
        isplitr
        · unfold readErr
          iright; ileft; ipureintro; rfl
        iapply HF; ipureintro; intro _ h; cases h
      · wp_auto
        wp_for_post
        iapply HΦ
        iexists got, bsn
        iframe HP Hbuf
        isplitr
        · ipureintro; exact ⟨Hbl, hpre⟩
        iright
        isplitr
        · ipureintro; exact hgot
        isplitr
        · unfold readErr
          ileft; ipureintro; exact ⟨rfl, hg0, rfl⟩
        iapply HF; ipureintro; intro _ h; cases h
    | err e =>
      obtain ⟨rfl, rfl⟩ := Hout
      simp only [net.ReadErr]
      iclear Hacc
      ihave #HE := HE
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      unfold net.resErr
      icases HE with ⟨%e', #Hop, #Hk⟩
      unfold net.opErr
      icases Hop with ⟨%pe, %nw, %Herr, #Hpe⟩
      obtain ⟨rfl, Hnw⟩ := Herr
      rw [show ReadRes.got _ = [] from rfl, List.append_nil]
      ihave Hbuf := buf_rejoin b k _ _ htk ⟨Hk0, Hkl⟩ $$ Hb1 Hb2
      rw [List.take_append_drop]
      rw [decide_eq_false hne]
      wp_auto
      wp_for_post
      iapply HΦ
      iexists got, bsn
      iframe HP Hbuf
      isplitr
      · ipureintro; exact ⟨Hbl, hpre⟩
      iright
      isplitr
      · ipureintro; exact hgot
      isplitr
      · unfold readErr
        iright; iright
        iexists e
        unfold net.resErr net.opErr
        iexists e'
        iframe Hk
        iexists pe, nw
        iframe Hpe
        ipureintro; exact ⟨rfl, Hnw⟩
      iapply HF; ipureintro; intro _ h; cases h
  · -- the loop ends: `b` is full
    obtain ⟨Hk0, Hkl, Hbl, Hgl, Hgt⟩ := Hinv
    have hk : sint.Z k = sint.Z b.len := by omega
    have hkn : sint.nat k = bs0.length := by
      rw [Hlen0.1]; show (sint.Z k).toNat = (sint.Z b.len).toNat; rw [hk]
    (try wp_auto)
    iapply HΦ
    iexists got, bsn
    iframe HP Hbuf
    have hg : got = bsn := by rw [← Hgt, List.take_of_length_le (by omega)]
    subst hg
    isplitr
    · ipureintro; exact ⟨Hbl, List.prefix_refl _⟩
    ileft; ipureintro; exact ⟨rfl, rfl⟩

end proof

end net.rpc
end Perennial
