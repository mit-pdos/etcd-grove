/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/Threads/QBank.lean (241f27e).
-/
/-
A **quarter bank** (decision D15): ghost state holding deposited quarter thread tokens
(`rtok t`, `QTok.lean`), each deposit giving a slip `qslip γ t` that withdraws exactly the quarter
deposited (the same slot `t`: a thread must end with its own four quarters, `wp_fork_rtok_upd`).
The bank counts its quarters (`qbank γ L`: `L` of them), so that the counting law applies to them
together with a depositor's own quarter (`qbank_count`).

Meant to sit in an invariant: the quarter thread pool (`QPool.lean`: the quarters of the
borrowers) and raft's routines group (`core/Defs.lean`, `rgInv`: one quarter per goroutine
started by `goFunc` and not `Done`).

* `qbank γ L`, `qslip γ t` (timeless);
* `qbank_alloc : ⊢ |==> ∃ γ, qbank γ 0`;
* `qbank_deposit : qbank γ L ∗ rtok t ⊢ |==> (qbank γ (L + 1) ∗ qslip γ t)`;
* `qbank_withdraw : qbank γ L ∗ qslip γ t ⊢ |==> ∃ L', ⌜L = L' + 1⌝ ∗ qbank γ L' ∗ rtok t`;
* `qbank_count : qbank γ L ∗ rtok t ⊢ ⌜L + 1 ≤ 4 * (threadBound GF - 1)⌝ ∗ qbank γ L ∗ rtok t`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Threads.QTok
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

section bank
variable {GF : BundledGFunctors} [AllG GF] [hT : ThreadGS GF]

/-- The bank `γ` holding `L` quarters: the deposits `ls` (slip id, slot), a ghost map from slip
ids to slots, and a fresh-id bound `next`. -/
def qbank (γ : GName) (L : Nat) : IProp GF :=
  iprop(∃ (m : GMap Nat Nat) (ls : List (Nat × Nat)) (next : Nat),
    ghostMapAuth γ 1 m ∗ ([∗list] t ∈ ls.map Prod.snd, rtok t) ∗
    ⌜ls.length = L ∧ (∀ i t, m !! i = some t → (i, t) ∈ ls) ∧ (∀ i, next ≤ i → m !! i = none)⌝)

/-- A slip of the bank `γ`: withdraws the quarter of slot `t` deposited for it. -/
def qslip (γ : GName) (t : Nat) : IProp GF :=
  iprop(∃ i : Nat, i ↪[γ] t)

instance qbank_timeless (γ : GName) (L : Nat) : Timeless (qbank (GF := GF) γ L) := by
  unfold qbank; infer_instance

instance qslip_timeless (γ : GName) (t : Nat) : Timeless (qslip (GF := GF) γ t) := by
  unfold qslip; infer_instance

theorem qbank_alloc : ⊢@{IProp GF} |==> ∃ γ, qbank γ 0 := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) with ⟨%γ, Hm⟩
  imodintro
  iexists γ
  unfold qbank
  iexists ∅, [], 0
  iframe Hm
  isplitl []
  · rw [List.map_nil]; iapply BigSepL.bigSepL_nil.2; iempintro
  · ipureintro
    refine ⟨rfl, fun i t h => ?_, fun i _ => rfl⟩
    simp at h

theorem qbank_deposit (γ : GName) (L t : Nat) :
    qbank (GF := GF) γ L ∗ rtok t ⊢ |==> (qbank γ (L + 1) ∗ qslip γ t) := by
  unfold qbank qslip
  iintro ⟨⟨%m, %ls, %next, Hm, Hls, %⟨Hlen, Hmem, Hfresh⟩⟩, Ht⟩
  imod ghost_map_insert (GF := GF) next t (Hfresh next (Nat.le_refl _)) $$ Hm with ⟨Hm, Hi⟩
  imodintro
  isplitr [Hi]
  · iexists _, (next, t) :: ls, next + 1
    iframe Hm
    isplitl [Hls Ht]
    · rw [List.map_cons]; iapply BigSepL.bigSepL_cons.2; iframe
    · ipureintro
      refine ⟨by simp [Hlen], fun i u h => ?_, fun i hi => ?_⟩
      · by_cases he : next = i
        · subst he
          have : m.insert next t !! next = some t := GMap.lookup_insert m next t
          rw [this] at h; cases h; simp
        · have : m.insert next t !! i = m !! i := GMap.lookup_insert_ne m t he
          rw [this] at h
          exact List.mem_cons_of_mem _ (Hmem i u h)
      · have : m.insert next t !! i = m !! i := GMap.lookup_insert_ne m t (by omega)
        rw [this]; exact Hfresh i (by omega)
  · iexists next; iexact Hi

theorem qbank_withdraw (γ : GName) (L t : Nat) :
    qbank (GF := GF) γ L ∗ qslip γ t ⊢ |==> ∃ L', ⌜L = L' + 1⌝ ∗ qbank γ L' ∗ rtok t := by
  unfold qbank qslip
  iintro ⟨⟨%m, %ls, %next, Hm, Hls, %⟨Hlen, Hmem, Hfresh⟩⟩, ⟨%i, Hi⟩⟩
  icombine Hi Hm gives %Hl
  have hin := Hmem i t Hl
  have hperm : (ls.map Prod.snd).Perm (t :: (ls.erase (i, t)).map Prod.snd) := by
    simpa using (List.perm_cons_erase hin).map Prod.snd
  icases (BigSepL.bigSepL_perm (Φ := fun t => rtok (GF := GF) t) hperm).1 $$ Hls with ⟨Ht, Hls⟩
  imod ghost_map_delete $$ Hm Hi with Hm
  imodintro
  iexists (ls.erase (i, t)).length
  isplitr
  · ipureintro; rw [← Hlen, List.length_erase_of_mem hin]
    have : 0 < ls.length := List.length_pos_of_mem hin
    omega
  iframe Ht
  iexists _, ls.erase (i, t), next
  iframe Hm Hls
  ipureintro
  refine ⟨rfl, fun j u h => ?_, fun j hj => ?_⟩
  · by_cases he : i = j
    · subst he
      have : m.delete i !! i = none := GMap.lookup_delete m i
      rw [this] at h; cases h
    · have : m.delete i !! j = m !! j := GMap.lookup_delete_ne m he
      rw [this] at h
      exact (List.mem_erase_of_ne (by intro e; cases e; exact he rfl)).mpr (Hmem j u h)
  · by_cases he : i = j
    · subst he; exact GMap.lookup_delete m i
    · have : m.delete i !! j = m !! j := GMap.lookup_delete_ne m he
      rw [this]; exact Hfresh j hj

/-- The bank's quarters and a depositor's own quarter, counted together. -/
theorem qbank_count (γ : GName) (L t : Nat) :
    qbank (GF := GF) γ L ∗ rtok t ⊢
      ⌜L + 1 ≤ 4 * (hT.threadBound - 1)⌝ ∗ qbank γ L ∗ rtok t := by
  unfold qbank
  iintro ⟨⟨%m, %ls, %next, Hm, Hls, %⟨Hlen, Hmem, Hfresh⟩⟩, Ht⟩
  icases persistent_entails_left (rtoks_le (GF := GF) (t :: ls.map Prod.snd)) $$ [Ht Hls]
    with ⟨Hall, %Hle⟩
  · iapply BigSepL.bigSepL_cons.2; iframe
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨Ht, Hls⟩
  isplitl []
  · ipureintro; simp [Hlen] at Hle; omega
  iframe Ht
  iexists m, ls, next
  iframe
  ipureintro; exact ⟨Hlen, Hmem, Hfresh⟩

end bank

end Perennial
