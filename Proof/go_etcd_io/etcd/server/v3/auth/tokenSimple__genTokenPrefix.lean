/-
Proof of `tokenSimple.genTokenPrefix` (`server/auth/simple_token.go`) over its translated body
(prove-authcrypto, 2026-11-21; until then an axiom at the trust boundary, the code names only):
sixteen draws of `crypto/rand.Int(rand.Reader, big.NewInt(52))`, each indexing `letters`. Its
callees are Perennial's: `crypto/rand.Int` (its trusted model, `wp_Int`: a value in `[0, max)` and a
`nil` error for the package's own `Reader`), `math/big`'s `NewInt` and `Int.Int64` (proved).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenSimple__genTokenPrefix
public import Perennial.Spec.crypto.rand.Int
public import Perennial.Spec.math.big.NewInt
public import Perennial.Spec.math.big.Int__Int64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

/-- `letters` (`simple_token.go`): the 52 ASCII letters. -/
abbrev auth.lettersStr : GoString := go!"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

theorem auth.lettersStr_noSpace (j : Nat) (b : w8) (h : auth.lettersStr[j]? = some b) :
    b ≠ W8 32 := by
  have hm : b ∈ auth.lettersStr := List.mem_of_getElem? h
  have hn : W8 32 ∉ auth.lettersStr := by decide
  intro hb; subst hb; exact hn hm

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.tokenSimple.genTokenPrefix.wp_proof
    (wp_NewInt : math.big.NewInt.spec (GF := GF) (hG := hG))
    (wp_Int : crypto.rand.Int.spec (GF := GF) (hG := hG))
    (wp_Int64 : math.big.Int.Int64.spec (GF := GF) (hG := hG)) :
    auth.tokenSimple.genTokenPrefix.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as -
  ihave #Hrand : isPkgInit (PROP := IProp GF) pkg_id.crypto.rand $$ []
  · iPkgInit
  ihave #Hbig : isPkgInit (PROP := IProp GF) pkg_id.math.big $$ []
  · iPkgInit
  ihave #Hreader := crypto.rand.isInitialized_access $$ Hrand
  unfold crypto.rand.isInitialized
  icases Hreader with ⟨%rdr, #Reader⟩
  try wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 16)) $$ [] as %ret ⟨Hret, -⟩
  · ipureintro; word
  try wp_auto
  ihave HI : (∃ (i : w64) (bs : List w8),
      "i" ∷ i_ptr ↦ i ∗
      "ret" ∷ ret ↦* bs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 16 ∧ bs.length = 16 ∧ W8 32 ∉ bs⌝ : IProp GF) $$ [i Hret]
  · iexists W64 0, List.replicate 16 (zero_val w8)
    iframe
    ipureintro
    refine ⟨by word, by word, by simp, ?_⟩
    have hz : zero_val w8 = W8 0 := rfl
    rw [hz]; intro h; rw [List.mem_replicate] at h; exact absurd h.2 (by decide)
  wp_for HI
  wp_if_destruct
  · wp_apply wp_NewInt as %max Hmax
    wp_apply wp_Int _ _ _ ⟨by decide, by decide⟩ $$ [$Hrand $Reader $Hmax] as %v %z ⟨Hmax, Hv, %Hz⟩
    have h52 : sint.Z (W64 52) = 52 := by word
    try wp_auto
    wp_apply wp_Int64 _ _ (by omega) $$ [$Hv] as Hv
    try wp_auto
    obtain ⟨b, hb⟩ : ∃ b, auth.lettersStr[z.toNat]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by simp [auth.lettersStr]; omega)⟩
    have hz0 : 0 ≤ sint.Z (W64 z) := by word
    have hzn : sint.nat (W64 z) = z.toNat := by word
    have hb' := hb
    simp only [auth.lettersStr] at hb'
    rw [ite_eq_left_of_eq_true _ _ (eq_true hz0), hzn, hb']
    try wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ ret
    have hi16 : sint.Z i < 16 := by have : sint.Z (W64 16) = 16 := by word
                                    omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by have h1 := Hlen.1; rw [Hi.2.2.1] at h1; word⟩)]
    wp_apply wp_store_slice_index ret (sint.Z i) bs b $$ [ret] as ret
    · iframe; ipureintro
      have h1 := Hi.2.2.1
      constructor
      · exact Hi.1
      · rw [h1]; word
    try wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, bs.set (sint.Z i).toNat b
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hi.2.2.1], ?_⟩
    intro hm
    rcases List.mem_or_eq_of_mem_set hm with h | h
    · exact Hi.2.2.2 h
    · exact auth.lettersStr_noSpace _ _ hb h.symm
  · try wp_auto
    wp_apply wp_bytes_to_string _ _ _ $$ ret as ret
    try wp_auto
    iapply HΦ
    ipureintro
    exact ⟨rfl, Hi.2.2.2⟩

end proof

end EtcdGrove
end Perennial
