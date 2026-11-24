/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kv/MainN.lean`. Lean-first (no Rocq
counterpart; 2026-11-15, kvraftN: `Main.lean`'s proof, over the voters `1 … k`).

The loop builds the voters `kvBootVoters k` (`1 … k`, kvreconf's `bootVoters`), which raft takes for
`1 ≤ k < 2^62` (`kvBootVoters_ok`). `StartCluster` and `Check` are specified at any storage registry
(`∀ [KVStor GF]`): the proof allocates the registry (`kvStorInv_alloc`) and instantiates them at it.
`StartCluster(voters)` gives the `k` replicas and the client's half of the store's state at the
empty store; `lintest.CounterClock()` a clock (its invariant at `kvClockN`); `Check(kvs, clock, 4, 25)`
then answers `Ok`, so the panic branch is not taken.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kv.MainN
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kv.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kv.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.CounterClock
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kv.Alloc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

/-- The namespace of `MainN`'s clock's invariant. -/
abbrev kvClockN : Namespace := nroot.@"kv_clock"

theorem lintestN_kvClockN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kvClockN :=
  mask_ndot_ne' nroot "lintest" "kv_clock" (by decide)

/-- The voters `1 … k`. -/
def kvBootVoters (k : Nat) : List w64 := (List.range k).map (fun i : Nat => W64 ((i : Int) + 1))

theorem kvBootVoters_length (k : Nat) : (kvBootVoters k).length = k := by simp [kvBootVoters]

theorem kvBootVoters_mem (k : Nat) (hk : k < 2 ^ 62) (x : w64) :
    x ∈ kvBootVoters k ↔ 1 ≤ uint.nat x ∧ uint.nat x ≤ k := by
  simp only [kvBootVoters, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; constructor <;> word
  · rintro ⟨h1, h2⟩; exact ⟨uint.nat x - 1, by omega, by word⟩

theorem kvBootVoters_nodup (k : Nat) (hk : k < 2 ^ 62) : (kvBootVoters k).Nodup := by
  unfold kvBootVoters
  rw [List.Nodup, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := k))
  intro a b ha hb hne h
  simp only [List.mem_range] at ha hb
  have := congrArg (fun x : w64 => uint.nat x) h
  apply hne
  word

/-- The voters `1 … k` are what raft takes, for `1 ≤ k < 2^62`. -/
theorem kvBootVoters_ok (k : Nat) (h1 : 1 ≤ k) (hk : k < 2 ^ 62) : KvVotersOk (kvBootVoters k) where
  ne := by intro h; have := kvBootVoters_length k; rw [h] at this; simp at this; omega
  nodup := kvBootVoters_nodup k hk
  zero := by rw [kvBootVoters_mem k hk]; intro ⟨h, _⟩; simp at h
  len := by rw [kvBootVoters_length]; omega
  ids := by
    intro id hid; rw [kvBootVoters_mem k hk] at hid
    constructor <;> (intro h; subst h; simp at hid; omega)

theorem kvBootVoters_snoc (k : w64) (h1 : 1 ≤ uint.nat k) (hk : uint.nat k < 2 ^ 62) :
    kvBootVoters (uint.nat k - 1) ++ [k] = kvBootVoters (uint.nat k) := by
  obtain ⟨m, hm⟩ : ∃ m, uint.nat k = m + 1 := ⟨uint.nat k - 1, by omega⟩
  rw [hm, show m + 1 - 1 = m from by omega]
  simp only [kvBootVoters, List.range_succ, List.map_append, List.map_singleton]
  congr 2; word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]

theorem MainN.wp_proof
    (wp_StartCluster : ∀ [KVStor GF], raft_kv.StartCluster.spec (GF := GF) (hG := hG))
    (wp_Check : ∀ [KVStor GF], raft_kv.Check.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG)) :
    MainN.spec (GF := GF) (hG := hG) := by
  intro k Hrb
  wp_start as #Hcc
  try wp_auto
  -- the range check: `k` outside `[1, 1000]` returns at once
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  have Hk1 : 1 ≤ uint.Z k := by word
  have Hk : uint.Z k < 2 ^ 62 := by word
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := KVStorRecT) with ⟨%γreg, Hreg⟩
  letI : KVStor GF := ⟨γreg⟩
  imod kvStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  try wp_auto
  -- the voters `1 … k`
  ihave IH : iprop(∃ (i : w64) (sv : GoSlice),
      "id" ∷ id_ptr ↦ i ∗ "voters" ∷ voters_ptr ↦ sv ∗
      "Hsv" ∷ sv ↦* kvBootVoters (uint.nat i - 1) ∗ "Hsvc" ∷ ownSliceCap w64 sv (DFrac.own 1) ∗
      "%Hi" ∷ ⌜1 ≤ uint.nat i ∧ uint.nat i ≤ uint.nat k + 1⌝) $$ [id voters]
  · iexists W64 1, slice.nil
    iframe id voters
    simp only [named, show uint.nat (W64 1) - 1 = 0 from rfl, show kvBootVoters 0 = [] from rfl]
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · try wp_auto
    wp_apply wp_slice_literal (V := w64) [i]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hsvc $Hsl1] as %sv' ⟨Hsv, Hsvc, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, sv'
    have Hi1 : uint.nat (i + W64 1) - 1 = uint.nat i := by word
    rw [Hi1, ← kvBootVoters_snoc i Hi.1 (by word)]
    iframe
    ipureintro; constructor <;> word
  have Hik : uint.nat i = uint.nat k + 1 := by word
  rw [Hik, show uint.nat k + 1 - 1 = uint.nat k from by omega]
  try wp_auto
  imod ownSlice_persist _ _ _ $$ Hsv with #Hvsl
  wp_apply (wp_StartCluster _ _ (kvBootVoters_ok (uint.nat k) (by word) (by word)) (by omega))
    $$ [$HstorInv $Hvsl]
    as %ksl ⟨%γr, %rs, Hks, %Hlen, #Hrs, Hval⟩
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  wp_apply wp_CounterClock kvClockN (by omega) as %f ⟨%clockVal, #Hclk, Ht0⟩
  have Hne : rs ≠ [] := by
    intro h; rw [h, kvBootVoters_length] at Hlen; simp at Hlen; word
  wp_apply wp_Check γr ksl rs clockVal (W64 0) ↑kvClockN f (W64 4) (W64 25)
    lintestN_kvClockN Hne (by decide) (by decide) (by decide) (by decide) $$ [Hval Ht0]
    as %r %Hr
  · iframe
    iframe #
  subst Hr
  wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kv
end EtcdGrove
end Perennial
