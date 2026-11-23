/-
`Gens()` (`kit.go`) meets remote's generator spec (`Gens.spec`, `Kit.lean`): the closure takes
client `c`'s counter under a `sync.Mutex` (lock invariant: the `next` slice, `NC` counters), and
every input `Gen(c, j)` makes is one the kit's store takes (`qInOk`: an 8-byte key
`"key0000" ++ digit`, a put's value `"v" ++ digit c ++ digits j`, nonempty, not `"nil"`, short).
Also the decimal helpers `digit`/`digits` (`bstr (toString n)`), which the configuration's
`config` and `String` use.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Kit
public import Dsverify.Proof.raxos.Smr.OpId

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

/-! ## Decimal strings -/

/-- A number below `10 ^ (k + 1)` has at most `k + 1` decimal digits. -/
theorem bstr_len_le : ∀ (k n : Nat), n < 10 ^ (k + 1) → (opid.bstr (toString n)).length ≤ k + 1
  | 0, n, h => by
    rw [opid.bstr_toString_rec, if_pos (by simpa using h)]; simp
  | k + 1, n, h => by
    rw [opid.bstr_toString_rec]
    split
    · simp
    · have := bstr_len_le k (n / 10) (by rw [Nat.pow_succ] at h; omega)
      simp; omega

theorem bstr_len_w64 (n : w64) : (opid.bstr (toString (uint.nat n))).length ≤ 20 :=
  bstr_len_le 19 _ (by
    have : uint.nat n < 18446744073709551616 := by word
    show uint.nat n < 100000000000000000000; omega)

section strs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- `digit(n)`: `n`'s last decimal digit. -/
theorem wp_digit (n : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.digit)) (Val #n))
    {{ RET #([W8 (uint.Z (W64 48 + n % W64 10))] : GoString); True }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w8) [W8 (uint.Z (W64 48 + n % W64 10))]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_bytes_to_string $$ Hsl as Hsl
  wp_end

theorem wp_digits_lt (N : Nat) : ∀ n : w64, uint.nat n < N →
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.digits)) (Val #n))
    {{ RET #(opid.bstr (toString (uint.nat n))); True }} := by
  induction N with
  | zero => intro n h; omega
  | succ N ih =>
    intro n hn
    wp_start
    wp_auto
    wp_if_destruct
    · wp_apply wp_digit
      rw [opid.bstr_toString_rec, if_pos (by word)]
      have : (W8 (uint.Z (W64 48 + n % W64 10)) : w8) = BitVec.ofNat 8 (48 + uint.nat n) := by
        word
      rw [this]
      wp_end
    · wp_apply ih (n / W64 10) (by word)
      wp_apply wp_digit
      rw [opid.bstr_toString_rec (uint.nat n), if_neg (by word)]
      have h1 : uint.nat (n / W64 10) = uint.nat n / 10 := by word
      have h2 : (W8 (uint.Z (W64 48 + n % W64 10)) : w8) =
          BitVec.ofNat 8 (48 + uint.nat n % 10) := by
        word
      rw [h1, h2]
      wp_end

/-- `digits(n)`: `n` in decimal. -/
theorem wp_digits (n : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.digits)) (Val #n))
    {{ RET #(opid.bstr (toString (uint.nat n))); True }} :=
  wp_digits_lt (uint.nat n + 1) n (by omega)

/-- `mix(c, r)`: some number. -/
theorem wp_mix (c r : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! raxos.examples.quepaxanet.mix)) (Val #c)) (Val #r))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  wp_end

/-- `Gen(c, j)`: an input the kit's store takes (`qInOk`). -/
theorem wp_Gen (c j : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! raxos.examples.quepaxanet.Gen)) (Val #c)) (Val #j))
    {{ (x : In), RET #x; ⌜qInOk (kin x)⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_mix as %x -
  wp_apply wp_digit
  have hkey : (go!"key0000" ++ [W8 (uint.Z (W64 48 + x % W64 2 % W64 10))] : GoString).length
      = 8 := rfl
  generalize (go!"key0000" ++ [W8 (uint.Z (W64 48 + x % W64 2 % W64 10))] : GoString) = K
    at hkey ⊢
  wp_if_destruct
  · wp_apply wp_digit
    wp_apply wp_digits
    have hlen := bstr_len_w64 j
    generalize opid.bstr (toString (uint.nat j)) = D at hlen ⊢
    iapply HΦ
    ipureintro
    refine ⟨⟨hkey, fun _ => ⟨by simp [kin], ?_⟩⟩, ?_⟩
    · intro h
      have := congrArg List.head? h
      simp [kin] at this
    · simp [kin]; omega
  · iapply HΦ
    ipureintro
    refine ⟨⟨hkey, fun h => by simp [kin] at h⟩, ?_⟩
    simp [kin]; omega

end strs

/-! ## `Gens` -/

section gens
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- `Gens`' lock invariant: the counters, one per client. -/
def gensInv (sl : GoSlice) : IProp GF :=
  iprop(∃ l : List w64, sl ↦* l ∗ ⌜l.length = 6⌝)

theorem mod6_bounds (id : w64) : 0 ≤ sint.Z (id % W64 6) ∧ sint.Z (id % W64 6) < 6 := by
  constructor <;> word

theorem gens_idx (id : w64) (sl : GoSlice) (l : List w64) (Hl : l.length = 6)
    (Hsll : l.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) :
    (0 ≤ sint.Z (id % W64 6) ∧ sint.Z (id % W64 6) < sint.Z sl.len) ∧
      (sint.Z (id % W64 6)).toNat < l.length ∧
      (0 ≤ sint.Z (id % W64 6) ∧ sint.Z (id % W64 6) < (l.length : Int)) := by
  have hm := mod6_bounds id
  obtain ⟨h1, h2⟩ := Hsll
  have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg h2
  refine ⟨⟨hm.1, by omega⟩, by omega, hm.1, by omega⟩

/-- **`Gens()` meets remote's generator spec.** -/
theorem gens_proof : Gens.spec (GF := GF) (hG := hG) := by
  wp_start as #Hpkg
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := w64) (W64 6)) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  iapply fupd_wp
  imod sync.init_Mutex (gensInv sl) ⊤ mu_ptr $$ mu [Hsl] with #Hmu
  · inext
    unfold gensInv
    iexists _
    iframe Hsl
    ipureintro; rfl
  imodintro
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_store
  wp_pures
  ipersist next
  wp_auto
  iapply HΦ
  unfold EtcdGrove.lintest.genSpec
  iintro %id
  iintro !> %Φ' %Hid HΦ'
  wp_pures
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  unfold gensInv
  icases HR with ⟨%l, Hsl, %Hl⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨hb, hlt, hlt'⟩ := gens_idx id sl l Hl Hsll
  rw [ite_eq_left hb]
  have hlt : (sint.Z (id % W64 6)).toNat < l.length := by rw [Hl]; omega
  list_elem l (sint.Z (id % W64 6)).toNat as x
  wp_apply wp_load_slice_index sl (sint.Z (id % W64 6)) l _ x hb.1 $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; exact Hx_lookup
  wp_auto
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index sl (sint.Z (id % W64 6)) l (x + W64 1) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; exact hlt'
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hsl]
  · iexists _
    iframe Hsl
    ipureintro; simp [Hl]
  wp_apply wp_Gen as %g %Hg
  iapply HΦ'
  iintro !>
  ipureintro
  exact ⟨⟨kin g, Hg⟩, rfl⟩

end gens

end raxos.examples.quepaxanet
end Perennial
