/-
The proof of `Do` (`Net/Spec/.../lib/remote/Do.lean`). After `EncIn` (a request longer than
`maxLen` goes to `hang`), `tries` is `T` (1 for a write, `ReadTries` = 3 for a read: the `if` is
closed by `wp_wand_l`, so the rest is one proof). `NewProph` gives the typed prophecy `xs`
(txnlin's `typedProph`); `known` says whether its head is some attempt `kt < T`, and the caller's
choice is applied at it: the update `lin R i Φk` (`Φk` is `Φo` if `known`, `True` else), and `Ψ`
if not `known`. The loop's invariant: the attempt counter `kv`, the prophecy unresolved, and the
owned update while `kv ≤ kt` (`kt` is 0 if not `known`). Attempt `kv` carries the owned update if
`kv = kt`, and otherwise the read's persistent one (`kv ≠ kt`, both below `T`, so `T > 1`: a read).
An answer that decodes to an output `ov o` resolves the prophecy with `kv`: so `known` and
`kv = kt`, and the slot gave `Φo o`; to the unknown output, with `T`: so not `known`, and `Ψ` is
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
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem Do.wp_proof (wp_attempt : attempt.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O))
    (wp_hang : hang.spec (GF := GF) (hG := hG))
    (wp_NewProph : github_com.goose_lang.primitive.NewProph.spec (GF := GF) (hG := hG))
    (wp_ResolveU64 : github_com.goose_lang.primitive.ProphId.ResolveU64.spec (GF := GF) (hG := hG)) :
    Do.spec (GF := GF) (hG := hG) (St := St) (I := I) (O := O) := by
  intro R a i Φo Ψ cd d
  wp_start as ⟨#Hm, #Ha, #Hcd, Hrd, Hch⟩
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
  obtain ⟨T, hT⟩ : ∃ T : Nat, T = if R.B.isWrite i = true then 1 else 3 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T ∧ T ≤ 3 := by split at hT <;> omega
  ihave #Hrlin : iprop(□ (⌜1 < T⌝ -∗ lin (Gg := hG.goose_globalGS) R i (fun _ => iprop(True)))) $$ [Hrd]
  · cases hw : R.B.isWrite i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrd with #Hrd
      imodintro
      iintro -
      iexact Hrd
    · imodintro
      iintro %h
      exfalso
      simp [hT, hw] at h
  wp_bind (If _ _ _)
  iapply (wp_wand_l (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ tries_ptr ↦ W64 T)))
  isplitr [tries]
  rotate_left
  · cases hw : R.B.isWrite i
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
  obtain ⟨known, kt, hkt, hkn, hku⟩ : ∃ (known : Bool) (kt : Nat), kt < T ∧
      (known = true → xs.head? = some (W64 kt)) ∧
      (known = false → ∀ k, k < T → xs.head? ≠ some (W64 k)) := by
    by_cases h : ∃ k, k < T ∧ xs.head? = some (W64 k)
    · obtain ⟨k, hk, hh⟩ := h
      exact ⟨true, k, hk, fun _ => hh, fun h => absurd h (by simp)⟩
    · exact ⟨false, 0, by omega, fun h => absurd h (by simp),
        fun _ k hk hh => h ⟨k, hk, hh⟩⟩
  iapply fupd_wp
  imod Hch $$ %known with Hk
  imodintro
  ihave ⟨HX, HL⟩ : iprop((if known then iprop(True) else Ψ) ∗
      lin (Gg := hG.goose_globalGS) R i (if known then Φo else fun _ => iprop(True))) $$ [Hk]
  · cases known
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hk
    · simp only [↓reduceIte]
      iframe Hk
  ihave HI : iprop(∃ kv : w64, "k" ∷ k_ptr ↦ kv ∗ "%Hkv" ∷ ⌜0 ≤ sint.Z kv ∧ sint.Z kv ≤ T⌝ ∗
      "HL" ∷ ((⌜uint.nat kv ≤ kt⌝ ∗
        lin (Gg := hG.goose_globalGS) R i (if known then Φo else fun _ => iprop(True))) ∨
        ⌜kt < uint.nat kv⌝)) $$ [k HL]
  · iexists W64 0
    iframe k
    isplit
    · ipureintro; constructor <;> word
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
    ihave ⟨%Φa, HLa, %hΦa, HL⟩ : iprop(∃ Φa : O → IProp GF, lin (Gg := hG.goose_globalGS) R i Φa ∗
        ⌜known = true → uint.nat kv = kt → Φa = Φo⌝ ∗
        ((⌜uint.nat (kv + W64 1) ≤ kt⌝ ∗
          lin (Gg := hG.goose_globalGS) R i (if known then Φo else fun _ => iprop(True))) ∨
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
    wp_apply wp_attempt R a i Φa req (DFrac.own 1) d Hlen $$ [Hreq HLa] as %rep %ok ⟨Hreq, Hres⟩
    · iframe Hm Ha Hreq HLa
    icases Hres with (%Hf | ⟨%v, %Hok, Hrep, Hv⟩)
    · subst Hf
      wp_auto
      wp_for_post
      iframe
      iexists kv + W64 1
      iframe
      ipureintro; word
    subst Hok
    wp_auto
    icases Hv with (⟨%o, %Ho, HΦa⟩ | %Hu)
    · subst Ho
      wp_apply HDecOut $$ %(R.ov o) %rep %(DFrac.own 1) %(Or.inl ⟨o, rfl⟩) [Hrep] as %x %good %Hx
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
        wp_for_post
        iapply HΦ
        ileft
        iexists o
        iframe HΦa
        ipureintro; rfl
    · subst Hu
      wp_apply HDecOut $$ %(R.unk i) %rep %(DFrac.own 1) %(Or.inr ⟨i, rfl⟩) [Hrep] as %x %good %Hx
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
