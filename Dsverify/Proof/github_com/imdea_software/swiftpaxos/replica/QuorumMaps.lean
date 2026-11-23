/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/QuorumMaps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`NewQuorum`, `NewQuorumsOfLeader`, `Quorum.Size`, `Quorum.Contains`, `Quorum.copy`: proofs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.quorum

theorem w32n_inj (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : w32n a = w32n b) :
    a = b := by
  unfold w32n at h
  have h1 : sint.Z (W32 (a : Int)) = a := sint_W32 _ (by omega) (by omega)
  have h2 : sint.Z (W32 (b : Int)) = b := sint_W32 _ (by omega) (by omega)
  rw [h] at h1; omega

theorem nodup_map_w32n (s : List Nat) (hnd : s.Nodup) (hs : ∀ x ∈ s, x < 2 ^ 31) :
    (s.map w32n).Nodup := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd ⊢
    refine ⟨?_, ih hnd.2 (fun x hx => hs x (by simp [hx]))⟩
    rintro ⟨b, hb, h⟩
    have := w32n_inj b a (hs b (by simp [hb])) (hs a (by simp)) h
    subst this; exact hnd.1 hb

theorem qRepr_size (m : GMap w32 Unit) (s : List Nat) (h : qRepr m s) (hnd : s.Nodup)
    (hs : ∀ x ∈ s, x < 2 ^ 31) : GMap.size m = s.length := by
  rw [GMap.size_eq_length m (s.map w32n) (nodup_map_w32n s hnd hs)]
  · simp
  intro k
  rw [h k]
  split <;> simp_all

end replica.quorum

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF]
variable [sem : go.Semantics] [replica.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]

set_option goose.wp.extras true

open replica.quorum

theorem replica.NewQuorum.wp_proof : replica.NewQuorum.spec := by
  intro size
  wp_start
  wp_auto
  wp_apply (wp_map_make2 (K := w32) (V := Unit)) as %q Hq
  iapply HΦ
  unfold qOwn
  iexists ∅
  iframe Hq
  ipureintro
  intro k; simp

theorem replica.NewQuorumsOfLeader.wp_proof : replica.NewQuorumsOfLeader.spec := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := Loc)) as %p Hp
  iapply HΦ
  unfold lqsOwn
  iexists ∅
  iframe Hp
  isplitr
  · ipureintro
    refine ⟨by decide, fun k => ?_⟩
    simp
  iclear Hpre «$res0»
  iapply BI.BigSepL.bigSepL_nil.2
  itrivial

theorem replica.Quorum.Size.wp_proof : replica.Quorum.Size.spec := by
  intro q dq s
  wp_start as ⟨Hq, %Hs⟩
  unfold qOwn
  icases Hq with ⟨%m, Hm, %Hrepr⟩
  wp_auto
  wp_apply (wp_map_len (K := w32) (V := Unit)) $$ [$Hm] as Hm
  rw [qRepr_size m s Hrepr Hs.1 Hs.2]
  iapply HΦ
  iexists m
  iframe Hm
  ipureintro; exact Hrepr

theorem replica.Quorum.Contains.wp_proof : replica.Quorum.Contains.spec := by
  intro q dq s r
  wp_start as Hq
  unfold qOwn
  icases Hq with ⟨%m, Hm, %Hrepr⟩
  wp_auto
  wp_apply (wp_map_lookup2 (K := w32) (V := Unit)) $$ [$Hm] as Hm
  have : (m !! r).isSome = decide (r ∈ s.map w32n) := by
    rw [Hrepr r]; split <;> simp_all
  rw [this, show ∀ P : Prop, [Decidable P] → decide (decide P = true) = decide P by
    intro P _; simp]
  iapply HΦ
  iexists m
  iframe Hm
  ipureintro; exact Hrepr

theorem replica.Quorum.copy.wp_proof (wp_NewQuorum : replica.NewQuorum.spec) :
    replica.Quorum.copy.spec := by
  intro q dq s
  wp_start as Hq
  unfold qOwn
  icases Hq with ⟨%m, Hm, %Hrepr⟩
  wp_auto
  wp_apply (wp_map_len (K := w32) (V := Unit)) $$ [$Hm] as Hm
  wp_apply wp_NewQuorum as %nql Hnq
  unfold qOwn
  icases Hnq with ⟨%m0, Hm0, %Hrepr0⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun keys i => iprop(
      ∃ (m' : GMap w32 Unit) (c : w32), nql ↦$ m' ∗ cmdId_ptr ↦ c ∗ nq_ptr ↦ nql ∗
        ⌜0 ≤ i ∧ ∀ k, m' !! k = if k ∈ keys.take i.toNat then some () else none⌝)) _ _ _ q m dq) $$ Hm
  iintro %keys %Hkeys
  isplitl [Hm0 cmdId nq]
  · iexists m0, _
    iframe Hm0 cmdId nq
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    rw [Hrepr0 k]; simp
  isplitr
  · imodintro
    iintro %i %key %v %Hi ⟨%m', %c, Hm', cmdId, nq, %Hm'⟩
    wp_auto
    wp_apply (wp_mapInsert (K := w32) (V := Unit)) $$ [$Hm'] as Hm'
    unfold forMapPostcondition
    iright; ileft
    isplitr; · ipureintro; rfl
    iexists _, _
    iframe Hm' cmdId nq
    ipureintro
    obtain ⟨hk, -⟩ := Hi
    obtain ⟨hi0, Hm'⟩ := Hm'
    refine ⟨by omega, fun k => ?_⟩
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk]
    by_cases hkk : key = k
    · subst hkk; simp
    · rw [GMap.lookup_insert_ne _ _ hkk, Hm' k]
      simp [Ne.symm hkk]
  iintro ⟨%m', %c, Hm', cmdId, nq, %Hm'⟩ Hm
  wp_auto
  iapply HΦ
  isplitl [Hm]
  · iexists m; iframe Hm; ipureintro; exact Hrepr
  iexists m'
  iframe Hm'
  ipureintro
  intro k
  rw [Hm'.2 k]
  rw [show (((GMap.size m : Nat) : Int)).toNat = keys.length by omega, List.take_length]
  have h1 := Hkeys.1 k
  have h2 := Hrepr k
  by_cases hk : k ∈ keys
  · have := h1.1 hk
    rw [if_pos hk]
    split
    · rfl
    · rename_i hn; rw [h2, if_neg hn] at this; simp at this
  · rw [if_neg hk]
    split
    · rename_i hn; exfalso; apply hk; apply h1.2; rw [h2, if_pos hn]; rfl
    · rfl

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

end
