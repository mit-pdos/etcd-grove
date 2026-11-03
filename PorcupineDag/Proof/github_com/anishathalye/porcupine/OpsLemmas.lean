/-
Lean-first (no Rocq counterpart).

# Porcupine PR #46: the chains of a slice of operations (2026-11-02)

What `makeEntries` and `checkOperations` need of `chainsOf ops nc` (client `c`'s ids, in the order
listed): its chains as `makeEntries`'s loop builds them (`chK ops k c`, the ids below `k`), and the
bridge `checkOperations` crosses from the caller's premises (`HistOk`, `ClientsOk`) to
`checkParallel`'s (`ChainsOk`, `HistWf`, `AllocOk`), with the chains' order the client order
(`chainOrder_iff`, so `LinearizableCO` at one is `LinearizableCO` at the other).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.anishathalye.porcupine

open Theory

section ops
variable [GooseExts]

/-- Client `c`'s ids below `k`, in order (`chainsOf`'s chains are `chK ops ops.length`). -/
def chK (ops : List Operation) (k c : Nat) : List Nat :=
  (List.range k).filter fun (i : Nat) =>
    decide (((ops[i]?).map (fun o => sint.Z o.ClientId')) = some (c : Int))

theorem chK_zero (ops : List Operation) (c : Nat) : chK ops 0 c = [] := by
  simp [chK]

theorem chK_succ (ops : List Operation) (k c : Nat) :
    chK ops (k + 1) c = chK ops k c ++
      (if ((ops[k]?).map (fun o => sint.Z o.ClientId')) = some (c : Int) then [k] else []) := by
  unfold chK
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : ((ops[k]?).map (fun o => sint.Z o.ClientId')) = some (c : Int)
  · simp only [List.filter_cons, List.filter_nil, h, decide_true, ↓reduceIte]
  · simp only [List.filter_cons, List.filter_nil, h, decide_false, ↓reduceIte,
      Bool.false_eq_true]

theorem mem_chK {ops : List Operation} {k c i : Nat} :
    i ∈ chK ops k c ↔ i < k ∧ ((ops[i]?).map (fun o => sint.Z o.ClientId')) = some (c : Int) := by
  simp [chK]

theorem chK_sorted (ops : List Operation) (k c : Nat) : (chK ops k c).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem chainsOf_length (ops : List Operation) (nc : Nat) : (chainsOf ops nc).length = nc := by
  simp [chainsOf]

theorem chain_chainsOf {ops : List Operation} {nc c : Nat} (hc : c < nc) :
    chain (chainsOf ops nc) c = chK ops ops.length c := by
  simp [chain, chainsOf, chK, hc]

theorem chain_chainsOf_ge {ops : List Operation} {nc c : Nat} (hc : nc ≤ c) :
    chain (chainsOf ops nc) c = [] := by
  unfold chain chainsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_none (by simp only [List.length_range]; omega)]
  rfl

/-- A member of a chain of `chainsOf` has that client's id. -/
theorem mem_chainsOf {ops : List Operation} {nc c y : Nat} (hy : y ∈ chain (chainsOf ops nc) c) :
    c < nc ∧ y < ops.length ∧ ((ops[y]?).map (fun o => sint.Z o.ClientId')) = some (c : Int) := by
  by_cases hc : c < nc
  · rw [chain_chainsOf hc, mem_chK] at hy
    exact ⟨hc, hy⟩
  · rw [chain_chainsOf_ge (by omega)] at hy
    cases hy

/-- Every id is a client below `nc`. -/
def IdsBelow (ops : List Operation) (nc : Nat) : Prop :=
  ∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧ sint.Z o.ClientId' < (nc : Int)

/-- Strictly sorted: a smaller value is at a smaller index. -/
theorem idx_lt_of_sorted {l : List Nat} (hs : l.Pairwise (· < ·)) {i j a b : Nat}
    (ha : l[i]? = some a) (hb : l[j]? = some b) (hab : a < b) : i < j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact h
  · exfalso
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hb
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := List.pairwise_iff_getElem.1 hs j i hj hi h
      omega
    · subst h; omega

theorem val_lt_of_sorted {l : List Nat} (hs : l.Pairwise (· < ·)) {i j a b : Nat}
    (ha : l[i]? = some a) (hb : l[j]? = some b) (hij : i < j) : a < b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  exact List.pairwise_iff_getElem.1 hs i j hi hj hij

theorem cid_eq_of_z {a b : Operation} (h : sint.Z a.ClientId' = sint.Z b.ClientId') :
    a.ClientId' = b.ClientId' :=
  BitVec.toInt_inj.mp h

/-- The chains' order is the client order. -/
theorem chainOrder_iff {ops : List Operation} {nc : Nat} (hids : IdsBelow ops nc) (a b : Nat) :
    chainOrder (chainsOf ops nc) a b ↔ clientOrder ops a b := by
  constructor
  · rintro ⟨c, i, j, hij, ha, hb⟩
    have hsrt : (chain (chainsOf ops nc) c).Pairwise (· < ·) := by
      by_cases hc : c < nc
      · rw [chain_chainsOf hc]; exact chK_sorted _ _ _
      · rw [chain_chainsOf_ge (by omega)]; exact List.Pairwise.nil
    have hab := val_lt_of_sorted hsrt ha hb hij
    obtain ⟨-, -, hca⟩ := mem_chainsOf (List.mem_of_getElem? ha)
    obtain ⟨-, -, hcb⟩ := mem_chainsOf (List.mem_of_getElem? hb)
    refine ⟨hab, ?_⟩
    cases hoa : ops[a]? with
    | none => rw [hoa] at hca; cases hca
    | some oa =>
      cases hob : ops[b]? with
      | none => rw [hob] at hcb; cases hcb
      | some ob =>
        rw [hoa] at hca; rw [hob] at hcb
        simp only [Option.map_some, Option.some.injEq] at hca hcb
        exact ⟨oa, ob, rfl, rfl, cid_eq_of_z (by rw [hca, hcb])⟩
  · rintro ⟨hab, oa, ob, ha, hb, hc⟩
    have hoa := hids oa (List.mem_of_getElem? ha)
    let c := (sint.Z oa.ClientId').toNat
    have hcz : ((c : Nat) : Int) = sint.Z oa.ClientId' := Int.toNat_of_nonneg hoa.1
    have hcn : c < nc := by omega
    have hal : a < ops.length := (List.getElem?_eq_some_iff.1 ha).1
    have hbl : b < ops.length := (List.getElem?_eq_some_iff.1 hb).1
    have hma : a ∈ chain (chainsOf ops nc) c := by
      rw [chain_chainsOf hcn, mem_chK, ha]; exact ⟨hal, by simp [hcz]⟩
    have hmb : b ∈ chain (chainsOf ops nc) c := by
      rw [chain_chainsOf hcn, mem_chK, hb]; exact ⟨hbl, by simp [hcz, hc]⟩
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hma
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hmb
    have hsrt : (chain (chainsOf ops nc) c).Pairwise (· < ·) := by
      rw [chain_chainsOf hcn]; exact chK_sorted _ _ _
    refine ⟨c, i, j, idx_lt_of_sorted hsrt (List.getElem?_eq_some_iff.2 ⟨hi, hia⟩)
      (List.getElem?_eq_some_iff.2 ⟨hj, hjb⟩) hab,
      List.getElem?_eq_some_iff.2 ⟨hi, hia⟩, List.getElem?_eq_some_iff.2 ⟨hj, hjb⟩⟩

/-- `LinearizableCO` at the chains' order is `LinearizableCO` at the client order. -/
theorem linCO_chains_iff {σ : Type} {M : SeqModel σ OpV} {ops : List Operation} {nc : Nat}
    (hids : IdsBelow ops nc) :
    LinearizableCO M (histOf ops) (chainOrder (chainsOf ops nc)) ↔
      LinearizableCO M (histOf ops) (clientOrder ops) := by
  constructor
  · exact good_mono fun a b hab => hab.imp_right (chainOrder_iff hids a b).2
  · exact good_mono fun a b hab => hab.imp_right (chainOrder_iff hids a b).1

theorem histOf_getElem? (ops : List Operation) (i : Nat) :
    (histOf ops)[i]? = (ops[i]?).map opOf := by
  simp [histOf]

/-- The chains of `chainsOf` are `ChainsOk`. -/
theorem chainsOk_chainsOf {ops : List Operation} {nc : Nat} (hids : IdsBelow ops nc)
    (hmono : MonoReturns ops) : ChainsOk (histOf ops) (chainsOf ops nc) := by
  refine ⟨fun c => ?_, fun y => ?_, fun y c c' hy hy' => ?_⟩
  · have hsrt : (chain (chainsOf ops nc) c).Pairwise (· < ·) := by
      by_cases hc : c < nc
      · rw [chain_chainsOf hc]; exact chK_sorted _ _ _
      · rw [chain_chainsOf_ge (by omega)]; exact List.Pairwise.nil
    refine ⟨hsrt.imp Nat.ne_of_lt, hsrt.imp_of_mem fun {a b} ha hb hab => ?_⟩
    obtain ⟨-, hal, hca⟩ := mem_chainsOf ha
    obtain ⟨-, hbl, hcb⟩ := mem_chainsOf hb
    have hoa := List.getElem?_eq_getElem hal
    have hob := List.getElem?_eq_getElem hbl
    rw [hoa] at hca; rw [hob] at hcb
    simp only [Option.map_some, Option.some.injEq] at hca hcb
    refine ⟨opOf ops[a], opOf ops[b], by rw [histOf_getElem?, hoa]; rfl,
      by rw [histOf_getElem?, hob]; rfl, ?_⟩
    exact hmono a b _ _ hab hoa hob (cid_eq_of_z (by rw [hca, hcb]))
  · simp only [histOf, List.length_map, chainsOf_length]
    constructor
    · intro hy
      have hoy := hids _ (List.getElem_mem hy)
      let c := (sint.Z (ops[y]).ClientId').toNat
      have hcz : ((c : Nat) : Int) = sint.Z (ops[y]).ClientId' := Int.toNat_of_nonneg hoy.1
      have hcn : c < nc := by omega
      refine ⟨c, hcn, ?_⟩
      rw [chain_chainsOf hcn, mem_chK, List.getElem?_eq_getElem hy]
      exact ⟨hy, by simp [hcz]⟩
    · rintro ⟨c, -, hy⟩
      exact (mem_chainsOf hy).2.1
  · have h1 := (mem_chainsOf hy).2.2
    have h2 := (mem_chainsOf hy').2.2
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    exact_mod_cast h2

theorem histWf_histOf {ops : List Operation} (hok : HistOk ops) : HistWf (histOf ops) := by
  refine ⟨by simpa [histOf] using hok.1, fun o ho => ?_⟩
  simp only [histOf, List.mem_map] at ho
  obtain ⟨o', ho', rfl⟩ := ho
  exact hok.2 o' ho'

/-- `CoFresh` grows by one operation at the end of the chain. -/
theorem coFresh_snoc {h : List (Op OpV)} {ch : List Nat} {cos : List clientOperation}
    {y : Nat} {o : Op OpV} {co : clientOperation} (hf : CoFresh h ch cos) (hy : h[y]? = some o)
    (hid : sint.Z co.id' = y) (hgid : sint.Z co.globalId' = y) (hin : co.Op'.Input' = o.val.1)
    (hout : co.Op'.Output' = o.val.2) (hcall : sint.Z co.Op'.Call' = o.call)
    (hret : sint.Z co.Op'.Return' = o.ret) (hv : co.visited' = false) :
    CoFresh h (ch ++ [y]) (cos ++ [co]) := by
  obtain ⟨hlen, hk⟩ := hf
  refine ⟨by simp [hlen], fun k co' hk' => ?_⟩
  rcases Nat.lt_or_ge k cos.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk'
    obtain ⟨y', o', h1, h2⟩ := hk k co' hk'
    exact ⟨y', o', by rw [List.getElem?_append_left (by omega)]; exact h1, h2⟩
  · rw [List.getElem?_append_right hge] at hk'
    have hk0 : k - cos.length = 0 := by
      rcases Nat.lt_or_ge (k - cos.length) 1 with h | h
      · omega
      · rw [List.getElem?_eq_none (by simpa using h)] at hk'; cases hk'
    rw [hk0] at hk'
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
    subst hk'
    refine ⟨y, o, ?_, hy, hid, hgid, hin, hout, hcall, hret, hv⟩
    rw [List.getElem?_append_right (by omega), show k - ch.length = 0 by omega]
    rfl

theorem coFresh_nil (h : List (Op OpV)) : CoFresh h [] [] :=
  ⟨rfl, fun k co hk => by simp at hk⟩

/-- The allocation bound for `maxClientId + 1` clients. -/
theorem allocOk_max {ops : List Operation} {mx : Int} (hids : ClientIdsOk ops)
    (hmx : (ops = [] ∧ mx = 0) ∨ ∃ o ∈ ops, 0 ≤ mx ∧ mx ≤ sint.Z o.ClientId') :
    AllocOk (mx.toNat + 1) ops.length := by
  rcases hmx with ⟨rfl, rfl⟩ | ⟨o, ho, h0, hle⟩
  · simp [AllocOk, maxAllocBytes]
  · have := (hids o ho).2
    have h0' := (hids o ho).1
    simp only [AllocOk, maxAllocBytes] at this ⊢
    have hle' : (((mx.toNat + 1 : Nat) : Int)) ≤ ((sint.nat o.ClientId' + 1 : Nat) : Int) := by
      have : (sint.nat o.ClientId' : Int) = sint.Z o.ClientId' := by
        simp only [sint.nat]; exact Int.toNat_of_nonneg (by omega)
      push_cast; omega
    have hm : (0 : Int) ≤ ((max ops.length 6 : Nat) : Int) := by omega
    have h1 := Int.mul_le_mul_of_nonneg_right hle' hm
    generalize ((mx.toNat + 1 : Nat) : Int) * ((max ops.length 6 : Nat) : Int) = X at h1 ⊢
    generalize ((sint.nat o.ClientId' + 1 : Nat) : Int) * ((max ops.length 6 : Nat) : Int) = Y
      at h1 this
    omega

end ops

end github_com.anishathalye.porcupine
end Perennial
