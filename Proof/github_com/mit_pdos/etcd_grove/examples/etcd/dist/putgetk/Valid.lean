/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/Valid.lean`: the length checks, the
addresses' loop (only safe: its result is not claimed), and the ids' loop, whose map `lows` holds exactly the
16 low bits of the ids seen so far (`MemberID`'s spec: `memberIdOf`), all distinct and not `0`; so `true` is
returned only if `cfgOk`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Valid
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AddrOK
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.MemberID

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode

/-- An id's 16 low bits, as `Valid` computes them (`MemberID(p) & 0xffff`). -/
theorem low_uZ (id : w64) : uint.Z (id &&& W64 65535) = uint.Z id % 2 ^ 16 := by
  have h : (id &&& W64 65535).toNat = id.toNat % 2 ^ 16 := by
    rw [BitVec.toNat_and, show (W64 65535).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [show uint.Z (id &&& W64 65535) = ((id &&& W64 65535).toNat : Int) from rfl, h,
    show uint.Z id = (id.toNat : Int) from rfl]
  first | norm_cast | omega | simp

/-- An id's 16 low bits, as an integer (`idsOk`'s). -/
abbrev lowOf (id : w64) : Int := uint.Z id % 2 ^ 16

/-- The ids' loop's map `lows`: the 16 low bits seen, `zs`, distinct and not `0`, are its keys. -/
def lowsInv (L : GMap w64 Bool) (zs : List Int) : Prop :=
  zs.Nodup ∧ (∀ z ∈ zs, z ≠ 0) ∧ ∀ k : w64, L !! k = if uint.Z k ∈ zs then some true else none

theorem lowsInv_nil : lowsInv (∅ : GMap w64 Bool) [] := by
  refine ⟨List.nodup_nil, by simp, fun k => ?_⟩
  simp

theorem lowsInv_snoc {L : GMap w64 Bool} {zs : List Int} {low : w64} (h : lowsInv L zs)
    (hn : uint.Z low ∉ zs) (h0 : uint.Z low ≠ 0) :
    lowsInv (<[low := true]> L) (zs ++ [uint.Z low]) := by
  obtain ⟨hnd, hnz, hm⟩ := h
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    intro e; subst e; exact hn ha
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hnz z hz
    · rw [List.mem_singleton] at hz; subst hz; exact h0
  · rw [GMap.lookup_insert_eq_iff]
    by_cases hk : low = k
    · subst hk; simp
    · rw [if_neg hk, hm k]
      have : uint.Z k ≠ uint.Z low := fun e => hk (uint_Z_inj.1 e).symm
      simp [this]

theorem idsOk_of_lowsInv {L : GMap w64 Bool} {ids : List w64} (h : lowsInv L (ids.map lowOf)) :
    idsOk ids :=
  ⟨h.1, fun id hid => h.2.1 _ (List.mem_map_of_mem hid)⟩

open Lean Elab Tactic Meta in
/-- Case on an innermost `decide p` of the goal (one whose `p` has no `decide`): `Hd : decide p = bd`,
`bd` split (`false`, `true`), and the conditions on `bd` simplified. -/
local elab "dcase" : tactic => do
  let isDec : Lean.Expr → Bool := fun e => e.isAppOfArity ``Decidable.decide 2
  let tgt ← instantiateMVars (← getMainTarget)
  let some d := tgt.find? (fun e => isDec e && !(e.appFn!.appArg!.find? isDec).isSome)
    | throwError "dcase: no decide in the goal"
  let dStx ← Term.exprToSyntax d
  let hd := mkIdent `Hd
  let bd := mkIdent `bd
  evalTactic (← `(tactic| (generalize $hd:ident : $dStx = $bd:ident; cases $bd:ident <;> cleanup_bool_decide <;>
    (try simp only [Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false, eq_self_iff_true,
      decide_eq_true_eq, ↓reduceIte]))))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

theorem Valid.wp_proof
    (wp_AddrOK : AddrOK.spec (GF := GF) (hG := hG))
    (wp_MemberID : MemberID.spec (GF := GF) (hG := hG)) :
    Valid.spec (GF := GF) (hG := hG) := by
  intro psl csl peers clients dq₁ dq₂ Hfips
  wp_start as ⟨Hp, Hc⟩
  ihave %Hpl := ownSlice_len $$ Hp
  ihave %Hcl := ownSlice_len $$ Hc
  (try wp_auto)
  dcase
  · have hp0 := of_decide_eq_false Hd
    (try wp_auto)
    dcase
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hpc := of_decide_eq_true Hd
    have hlen : peers.length = clients.length := by rw [Hpl.1, Hcl.1, hpc]
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := Bool)) as %sm Hsm
    (try wp_auto)
    -- the addresses' loop: only read (its checks are not claimed)
    ihave IH : iprop(∃ (j : w64) (M : GMap GoString Bool), "j" ∷ j_ptr ↦ j ∗ "Hsm" ∷ sm ↦$ M ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j⌝) $$ [j Hsm]
    · iexists _, _
      iframe
      ipureintro
      first | decide | rfl | word
    wp_for IH
    dcase
    · -- the ids' loop
      (try wp_auto)
      wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %lm HL
      (try wp_auto)
      ihave IJ : iprop(∃ (j : w64) (L : GMap w64 Bool), "j" ∷ j_ptr ↦ j ∗ "HL" ∷ lm ↦$ L ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ lowsInv L (((idsOf peers).map lowOf).take (sint.nat j))⌝) $$ [j HL]
      · iexists _, ∅
        iframe
        ipureintro
        refine ⟨by first | decide | rfl | word, ?_⟩
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
        exact lowsInv_nil
      wp_for IJ
      obtain ⟨hj0, hinv⟩ := Hj
      dcase
      · -- every id checked: `cfgOk`
        have hge : ¬ sint.Z j < sint.Z psl.len := of_decide_eq_false Hd
        (try wp_auto)
        iapply HΦ
        iframe
        ipureintro
        intro _
        have hall : ((idsOf peers).map lowOf).take (sint.nat j) = (idsOf peers).map lowOf :=
          List.take_of_length_le (by simp only [List.length_map, idsOf]; word)
        rw [hall] at hinv
        refine ⟨?_, hlen, ?_⟩
        · intro h; apply hp0; rw [h] at Hpl; simp at Hpl; word
        · exact idsOk_of_lowsInv hinv
      have hlt : sint.Z j < sint.Z psl.len := of_decide_eq_true Hd
      have hjn : sint.nat j < peers.length := by word
      obtain ⟨pj, hpj⟩ : ∃ x, peers[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjn⟩
      (try wp_auto)
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len from ⟨hj0, hlt⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index psl (sint.Z j) peers dq₁ pj hj0) $$ [Hp] as Hp
      · iframe; ipureintro; exact hpj
      wp_apply (wp_MemberID pj Hfips)
      (try wp_auto)
      dcase
      · have hl0 : ¬ memberIdOf pj &&& W64 65535 = W64 0 := of_decide_eq_false Hd
        (try wp_auto)
        wp_apply (wp_map_lookup1 go.uint64 go.bool lm L _ (DFrac.own 1)) $$ HL as HL
        rw [hinv.2.2]
        by_cases hin : uint.Z (memberIdOf pj &&& W64 65535) ∈ ((idsOf peers).map lowOf).take (sint.nat j)
        · simp only [hin, ite_true, Option.getD_some]
          (try wp_auto)
          wp_for_post
          (try wp_auto)
          iapply HΦ; iframe; ipureintro; intro h; cases h
        · simp only [hin, ite_false, Option.getD_none]
          rw [show (zero_val Bool) = false from rfl]
          (try wp_auto)
          wp_apply wp_mapInsert $$ HL as HL
          (try wp_auto)
          wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          refine ⟨by word, ?_⟩
          have hz : ((idsOf peers).map lowOf)[sint.nat j]? = some (lowOf (memberIdOf pj)) := by
            simp [idsOf, hpj]
          rw [hj1, List.take_add_one, hz, Option.toList_some,
            show lowOf (memberIdOf pj) = uint.Z (memberIdOf pj &&& W64 65535) from (low_uZ _).symm]
          exact lowsInv_snoc hinv hin (fun h => hl0 (uint_Z_inj.1 (by rw [h]; rfl)))
      · (try wp_auto)
        wp_for_post
        (try wp_auto)
        iapply HΦ; iframe; ipureintro; intro h; cases h
    -- one address pair
    have hlt : sint.Z j < sint.Z psl.len := of_decide_eq_true Hd
    have hjn : sint.nat j < peers.length := by word
    have hjc : sint.nat j < clients.length := by omega
    obtain ⟨pj, hpj⟩ : ∃ x, peers[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjn⟩
    obtain ⟨cj, hcj⟩ : ∃ x, clients[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjc⟩
    (try wp_auto)
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len from ⟨Hj, hlt⟩, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index psl (sint.Z j) peers dq₁ pj Hj) $$ [Hp] as Hp
    · iframe; ipureintro; exact hpj
    (try wp_auto)
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z csl.len from ⟨Hj, by rw [← hpc]; exact hlt⟩,
      _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index csl (sint.Z j) clients dq₂ cj Hj) $$ [Hc] as Hc
    · iframe; ipureintro; exact hcj
    (try wp_auto)
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %rl ⟨Hrl, -⟩
    try simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
    (try wp_auto)
    ihave IK : iprop(∃ (i : w64) (av : GoString) (M : GMap GoString Bool), "i" ∷ i_ptr ↦ i ∗
        "a" ∷ a_ptr ↦ av ∗ "Hsm" ∷ sm ↦$ M ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i⌝) $$ [i a Hsm]
    · iexists _, _, _
      iframe
      ipureintro
      first | decide | rfl | word
    wp_for IK
    dcase
    · -- the pair done
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      word
    have hlt' := of_decide_eq_true Hd
    have hli : sint.nat i < 2 := by
      first
        | word
        | (simp only [go.arrayLiteralSize, List.foldl] at hlt'; word)
    obtain ⟨x, hx⟩ : ∃ x, [pj, cj][sint.nat i]? = some x :=
      ⟨_, List.getElem?_eq_getElem (show sint.nat i < [pj, cj].length by
        simp only [List.length_cons, List.length_nil]; omega)⟩
    (try wp_auto)
    simp only [Hi, hlt', _root_.and_self, _root_.true_and, ↓reduceIte, ite_true]
    wp_apply (wp_load_slice_index _ (sint.Z i) [pj, cj] (DFrac.own 1) x Hi) $$ [Hrl] as Hrl
    · iframe; ipureintro; exact hx
    (try wp_auto)
    wp_apply (wp_AddrOK x) as %b -
    (try wp_auto)
    cases b
    · (try wp_auto)
      wp_for_post
      wp_for_post
      (try wp_pures)
      (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    (try wp_auto)
    wp_apply (wp_map_lookup1 go.string go.bool sm M x (DFrac.own 1)) $$ Hsm as Hsm
    cases hm : M !! x with
    | some v =>
      simp only [Option.getD_some]
      cases v
      · (try wp_auto)
        wp_apply wp_mapInsert $$ Hsm as Hsm
        (try wp_auto)
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        word
      · (try wp_auto)
        wp_for_post
        wp_for_post
        (try wp_pures)
        (try wp_auto)
        iapply HΦ; iframe; ipureintro; intro h; cases h
    | none =>
      simp only [Option.getD_none]
      rw [show (zero_val Bool) = false from rfl]
      (try wp_auto)
      wp_apply wp_mapInsert $$ Hsm as Hsm
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      word
  · (try wp_auto)
    iapply HΦ; iframe; ipureintro; intro h; cases h

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
