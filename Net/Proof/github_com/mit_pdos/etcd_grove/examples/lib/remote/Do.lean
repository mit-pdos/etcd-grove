/-
The proof of `Do` (`Net/Spec/.../lib/remote/Do.lean`). After `EncIn` (a request longer than
`maxLen` goes to `hang`), `tries` is `T` (1 for a write, `ReadTries` = 3 for a read: the `if` is
closed by `wp_wand_l`, so the rest is one proof). `NewProph` gives the typed prophecies `xs`
(txnlin's `typedProph`) and `ys`; `known` says whether `xs`'s head is some attempt `kt < T`, and the
caller's choice is applied at it and at the bytes `ys` says (`prophBytes ys`): a slot update
`slotUpd R i Φb` and, if `known`, a way from `Φb o` of an output whose bytes are those to `Φo o`
(`Φb` is `True` and `Ψ` returned if not `known`). The loop's invariant: the attempt counter `kv`,
the prophecies unresolved, and the owned update while `kv ≤ kt` (`kt` is 0 if not `known`). Attempt
`kv` carries the owned update if `kv = kt`, and otherwise the read's persistent one (`kv ≠ kt`, both
below `T`, so `T > 1`: a read). An answer that decodes to an output `ov o` resolves `xs` with `kv`:
so `known` and `kv = kt`, and the slot gave `Φb o`; then `ys` with the reply's length and bytes
(the inner loop), so `prophBytes ys` is the reply's bytes, `encOut (ov o)` (`repP`, at the store's fixed-value wire `RBase.svc`), and the choice
gives `Φo o`. An answer of the unknown output resolves `xs` with `T`: so not `known`, and `Ψ` is
returned; the loop's end resolves with `T`, not `known` either.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Do
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.attempt
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.hang
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Proph

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-! The reply's byte loop: its counter `j` stays below the reply's length `L < 2^63`. -/

theorem byteLoop_lt {L : Nat} {j n : w64} (hL : L < 2 ^ 63) (hjL : uint.nat j ≤ L)
    (hn : L = sint.nat n ∧ 0 ≤ sint.Z n) (hif : sint.Z j < sint.Z n) : uint.nat j < L := by
  obtain ⟨rfl, h2⟩ := hn
  word

theorem byteLoop_in {L : Nat} {j n : w64} (hL : L < 2 ^ 63) (hjL : uint.nat j ≤ L)
    (hn : L = sint.nat n ∧ 0 ≤ sint.Z n) (hif : sint.Z j < sint.Z n) :
    0 ≤ sint.Z j ∧ sint.Z j < sint.Z n := by
  obtain ⟨rfl, h2⟩ := hn
  constructor <;> word

theorem byteLoop_toNat {L : Nat} {j n : w64} (hL : L < 2 ^ 63) (hjL : uint.nat j ≤ L)
    (hn : L = sint.nat n ∧ 0 ≤ sint.Z n) : (sint.Z j).toNat = uint.nat j := by
  obtain ⟨rfl, h2⟩ := hn
  word

theorem byteLoop_succ {L : Nat} {j : w64} (hL : L < 2 ^ 63) (hj : uint.nat j < L) :
    uint.nat (j + W64 1) = uint.nat j + 1 := by
  word

theorem byteLoop_end {L : Nat} {j n : w64} (hL : L < 2 ^ 63) (hjL : uint.nat j ≤ L)
    (hn : L = sint.nat n ∧ 0 ≤ sint.Z n) (hif : ¬ sint.Z j < sint.Z n) : uint.nat j = L := by
  obtain ⟨rfl, h2⟩ := hn
  word

theorem byteLoop_len {L : Nat} {n : w64} (hL : L < 2 ^ 63)
    (hn : L = sint.nat n ∧ 0 ≤ sint.Z n) : uint.nat n = L := by
  obtain ⟨rfl, h2⟩ := hn
  word

theorem Do.wp_proof (wp_attempt : attempt.spec (GF := GF) (hG := hG) (I := I) (O := O))
    (wp_hang : hang.spec (GF := GF) (hG := hG))
    (wp_NewProph : github_com.goose_lang.primitive.NewProph.spec (GF := GF) (hG := hG))
    (wp_ResolveU64 : github_com.goose_lang.primitive.ProphId.ResolveU64.spec (GF := GF) (hG := hG)) :
    Do.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O) := by
  intro J R a i Φo Ψ cd d
  wp_start as ⟨#Hm, #Ha, #Hcd, Hbu, Hrd, Hch⟩
  iunfold codecOk at Hcd
  icases Hcd with ⟨#HEncIn, #HDecIn, #HEncOut, #HDecOut, #HIsRead, #HUnk, #HIsUnkO, #HIsUnkU⟩
  wp_auto
  wp_apply HEncIn $$ %i [] as %req Hreq
  ihave %Hrl := ownSlice_len $$ Hreq
  wp_if_destruct
  · wp_apply wp_hang as HF
    iexfalso
    iexact HF
  have Hlen : (R.encIn i).length ≤ maxLen := by
    have h1 := Hrl.1
    have : sint.nat req.len = uint.nat req.len := by word
    simp only [maxLen]; word
  wp_apply HIsRead $$ %i []
  obtain ⟨T, hT⟩ : ∃ T : Nat, T = if R.B.isWrite (R.mi i) = true then 1 else 3 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T ∧ T ≤ 3 := by split at hT <;> omega
  ihave #Hrlin : iprop(□ (⌜1 < T⌝ -∗ slotUpd (Gg := hG.goose_globalGS) R i (fun _ => iprop(True)))) $$ [Hrd]
  · cases hw : R.B.isWrite (R.mi i)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrd with #Hrd
      imodintro
      iintro -
      rw [slotUpd_read R hw]
      imodintro
      iexact Hrd
    · imodintro
      iintro %h
      exfalso
      simp [hT, hw] at h
  wp_bind (If _ _ _)
  iapply (wp_wand_l (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ tries_ptr ↦ W64 T)))
  isplitr [tries]
  rotate_left
  · cases hw : R.B.isWrite (R.mi i)
    · wp_auto
      have h3 : T = 3 := by simp [hT, hw]
      subst h3
      iframe tries
      ipureintro; rfl
    · wp_auto
      have h1 : T = 1 := by simp [hT, hw]
      subst h1
      iframe tries
      ipureintro; rfl
  iintro %v ⟨%Hv, tries⟩
  subst Hv
  wp_auto
  wp_apply (EtcdGrove.linkv.wp_NewProph_typed (τ := w64) wp_NewProph) as %p %xs Hp
  wp_apply (EtcdGrove.linkv.wp_NewProph_typed (τ := w64) wp_NewProph) as %q %ys Hq
  obtain ⟨known, kt, hkt, hkn, hku⟩ : ∃ (known : Bool) (kt : Nat), kt < T ∧
      (known = true → xs.head? = some (W64 kt)) ∧
      (known = false → ∀ k, k < T → xs.head? ≠ some (W64 k)) := by
    by_cases h : ∃ k, k < T ∧ xs.head? = some (W64 k)
    · obtain ⟨k, hk, hh⟩ := h
      exact ⟨true, k, hk, fun _ => hh, fun h => absurd h (by simp)⟩
    · exact ⟨false, 0, by omega, fun h => absurd h (by simp),
        fun _ k hk hh => h ⟨k, hk, hh⟩⟩
  iapply fupd_wp
  imod Hch $$ %known %(prophBytes ys) with Hk
  imodintro
  ihave ⟨%Φb, HX, HL, Hfin⟩ : iprop(∃ Φb : O → IProp GF, (if known then iprop(True) else Ψ) ∗
      slotUpd (Gg := hG.goose_globalGS) R i Φb ∗
      (⌜known = true⌝ -∗ ∀ o, ⌜R.encOut (R.ov o) = prophBytes ys⌝ -∗ Φb o -∗ £ 1 ={⊤}=∗ Φo o)) $$ [Hk]
  · cases known
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hk with ⟨HΨ, HL⟩
      iexists (fun _ => iprop(True))
      iframe HΨ
      cases hw : R.B.isWrite (R.mi i)
      · ihave HL' := Hrlin $$ %(by simp [hT, hw])
        iframe HL'
        iintro %h; cases h
      · rw [slotUpd_write R hw]
        iframe HL
        iintro %h; cases h
    · simp only [↓reduceIte]
      icases Hk with ⟨%Φb, HL, Hf⟩
      iexists Φb
      iframe HL
      iintro -
      iexact Hf
  ihave Hbu := budUnits_le (Gg := hG.goose_globalGS) a (m := T) (n := readTries)
    (by simp only [readTries]; omega) $$ Hbu
  ihave HI : iprop(∃ kv : w64, "k" ∷ k_ptr ↦ kv ∗ "%Hkv" ∷ ⌜0 ≤ sint.Z kv ∧ sint.Z kv ≤ T⌝ ∗
      "Hbu" ∷ budUnits (Gg := hG.goose_globalGS) a (T - uint.nat kv) ∗
      "HL" ∷ ((⌜uint.nat kv ≤ kt⌝ ∗
        slotUpd (Gg := hG.goose_globalGS) R i Φb) ∨
        ⌜kt < uint.nat kv⌝)) $$ [k HL Hbu]
  · iexists W64 0
    iframe k
    isplit
    · ipureintro; constructor <;> word
    isplitl [Hbu]
    · rw [show T - uint.nat (W64 0) = T by simp]
      iexact Hbu
    ileft
    iframe HL
    ipureintro; word
  irename «in» => Hin
  wp_for HI
  wp_if_destruct
  · -- an attempt: the update it carries
    have hkvT : uint.nat kv < T := by
      have hT' : sint.Z (W64 (T : Int)) = T := by
        have : T = 1 ∨ T = 2 ∨ T = 3 := by omega
        rcases this with h | h | h <;> subst h <;> rfl
      have h0 := Hkv.1
      have : uint.nat kv = (sint.Z kv).toNat := by word
      omega
    ihave ⟨%Φa, HLa, %hΦa, HL⟩ : iprop(∃ Φa : O → IProp GF, slotUpd (Gg := hG.goose_globalGS) R i Φa ∗
        ⌜known = true → uint.nat kv = kt → Φa = Φb⌝ ∗
        ((⌜uint.nat (kv + W64 1) ≤ kt⌝ ∗
          slotUpd (Gg := hG.goose_globalGS) R i Φb) ∨
          ⌜kt < uint.nat (kv + W64 1)⌝)) $$ [HL]
    · by_cases hk : uint.nat kv = kt
      · icases HL with (⟨-, HL⟩ | %h)
        · iexists _
          iframe HL
          isplit
          · ipureintro; intro hkn' _; simp [hkn']
          iright; ipureintro; word
        · exfalso; omega
      · ihave HLa := Hrlin $$ %(by omega)
        iexists (fun _ => iprop(True))
        iframe HLa
        isplit
        · ipureintro; intro _ h; exact absurd h hk
        icases HL with (⟨%h, HL⟩ | %h)
        · ileft; iframe HL; ipureintro; word
        · iright; ipureintro; word
    have hkv1 : uint.nat (kv + W64 1) = uint.nat kv + 1 := by
      have : uint.nat kv < 3 := by omega
      word
    rw [show T - uint.nat kv = (T - uint.nat (kv + W64 1)) + 1 by omega]
    rw [budUnits_succ]
    icases Hbu with ⟨Hu, Hbu⟩
    wp_apply wp_attempt (RBase.svc (Gg := hG.goose_globalGS) R) a i Φa req (DFrac.own 1) d Hlen
      $$ [Hreq HLa Hu] as %rep %ok ⟨Hreq, Hres⟩
    · iframe Hm Ha Hreq HLa Hu
    icases Hres with (%Hf | ⟨%Hok, Hv⟩)
    · subst Hf
      wp_auto
      wp_for_post
      iframe
      iexists kv + W64 1
      iframe
      ipureintro; word
    subst Hok
    wp_auto
    icases Hv with (⟨%o, Hrep, HΦa⟩ | ⟨%v, Hrep, %Hu⟩)
    · imod (ownSlice_persist (V := w8) rep (DFrac.own 1) (R.encOut (R.ov o))) $$ Hrep with #Hrep
      wp_apply HDecOut $$ %(R.ov o) %rep %DFrac.discard %(Or.inl ⟨o, rfl⟩) [Hrep] as %x %good %Hx
      · iexact Hrep
      cases good
      · wp_auto
        wp_for_post
        iframe
        iexists kv + W64 1
        iframe
        ipureintro; word
      rw [Hx rfl]
      wp_auto_lc 1
      irename Hlc1 => Hlcf
      wp_apply HIsUnkO $$ %o []
      wp_apply (EtcdGrove.linkv.wp_ptr_ResolveU64_typed wp_ResolveU64 p_ptr _ p xs _) $$ [p Hp]
        as %xs' ⟨%Hxs, -, -⟩
      · iframe
      cases known
      · exfalso
        apply hku rfl (uint.nat kv) hkvT
        rw [Hxs]; simp
      · have hk : uint.nat kv = kt := by
          have h := hkn rfl
          rw [Hxs] at h; simp at h
          subst h; word
        obtain rfl := hΦa rfl hk
        -- the answer's bytes: the second prophecy; the choice's update is eliminated at the end
        iapply wp_fupd
        ihave %Hrl := ownSlice_len $$ Hrep
        wp_apply (EtcdGrove.linkv.wp_ptr_ResolveU64_typed wp_ResolveU64 q_ptr _ q ys _) $$ [q Hq]
          as %ys0 ⟨%Hys, q, Hq⟩
        · iframe
        ihave HJ : (∃ (j : w64) (ysj : List w64), "j" ∷ j_ptr ↦ j ∗ "q" ∷ q_ptr ↦ q ∗
            "Hq" ∷ EtcdGrove.linkv.typedProph w64 q ysj ∗
            "%Hj" ∷ ⌜uint.nat j ≤ (R.encOut (R.ov o)).length ∧
              ys0 = ((R.encOut (R.ov o)).take (uint.nat j)).map (fun b => W64 (uint.Z b)) ++ ysj⌝
            : IProp GF) $$ [j q Hq]
        · iexists W64 0, ys0
          iframe
          ipureintro; simp
        wp_for HJ
        wp_if_destruct
        · have hj : uint.nat j < (R.encOut (R.ov o)).length :=
            byteLoop_lt (R.encOut_len _) Hj.1 Hrl Hif
          obtain ⟨b, hb⟩ : ∃ b, (R.encOut (R.ov o))[uint.nat j]? = some b :=
            ⟨_, List.getElem?_eq_getElem hj⟩
          have hs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rep.len :=
            byteLoop_in (R.encOut_len _) Hj.1 Hrl Hif
          rw [ite_eq_left hs]
          wp_apply wp_load_slice_index rep (sint.Z j) (R.encOut (R.ov o)) DFrac.discard b
            (by word) $$ [Hrep] as -
          · iframe Hrep
            ipureintro
            rw [byteLoop_toNat (R.encOut_len _) Hj.1 Hrl]; exact hb
          wp_apply (EtcdGrove.linkv.wp_ptr_ResolveU64_typed wp_ResolveU64 q_ptr _ q ysj _) $$ [q Hq]
            as %ysj' ⟨%Hysj, q, Hq⟩
          · iframe
          wp_for_post
          iframe
          iexists j + W64 1, ysj'
          iframe
          ipureintro
          have hsucc := byteLoop_succ (R.encOut_len _) hj
          refine ⟨by omega, ?_⟩
          rw [Hj.2, Hysj, hsucc,
            List.take_add_one, hb]
          simp
        · have hjl : uint.nat j = (R.encOut (R.ov o)).length :=
            byteLoop_end (R.encOut_len _) Hj.1 Hrl Hif
          have hbs : prophBytes ys = R.encOut (R.ov o) := by
            rw [Hys, Hj.2, hjl, List.take_of_length_le (Nat.le_refl _)]
            apply prophBytes_eq
            exact byteLoop_len (R.encOut_len _) Hrl
          wp_for_post
          imod Hfin $$ %(by trivial) %o %hbs.symm HΦa Hlcf with HΦo
          imodintro
          wp_auto
          iapply HΦ
          ileft
          iexists o
          iframe HΦo
          ipureintro; rfl
    · have Hu : v = R.unk i := Hu
      subst Hu
      imod (ownSlice_persist (V := w8) rep (DFrac.own 1) (R.encOut (R.unk i))) $$ Hrep with #Hrep
      wp_apply HDecOut $$ %(R.unk i) %rep %DFrac.discard %(Or.inr ⟨i, rfl⟩) [Hrep] as %x %good %Hx
      · iexact Hrep
      cases good
      · wp_auto
        wp_for_post
        iframe
        iexists kv + W64 1
        iframe
        ipureintro; word
      rw [Hx rfl]
      wp_auto
      wp_apply HIsUnkU $$ %i []
      wp_apply (EtcdGrove.linkv.wp_ptr_ResolveU64_typed wp_ResolveU64 p_ptr _ p xs _) $$ [p Hp]
        as %xs' ⟨%Hxs, -, -⟩
      · iframe
      cases known
      · wp_for_post
        iapply HΦ
        iright
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe HX
      · exfalso
        have h := hkn rfl
        rw [Hxs] at h; simp at h
        have : T = kt := by
          have := congrArg BitVec.toNat h
          simp at this
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
          exact this
        omega
  · -- no attempt answered
    wp_apply (EtcdGrove.linkv.wp_ptr_ResolveU64_typed wp_ResolveU64 p_ptr _ p xs _) $$ [p Hp]
      as %xs' ⟨%Hxs, -, -⟩
    · iframe
    cases known
    · wp_apply HUnk $$ %i []
      iapply HΦ
      iright
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe HX
    · exfalso
      have h := hkn rfl
      rw [Hxs] at h; simp at h
      have : T = kt := by
        have := congrArg BitVec.toNat h
        simp at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact this
      omega

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
