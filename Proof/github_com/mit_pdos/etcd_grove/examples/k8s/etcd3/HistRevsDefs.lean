/-
Lean-first (no Rocq counterpart).

# The vocabulary of `HistoryRevs`' spec (k8s-dist K9, `notes/k8s-dist-k9.md` §2.7)

- `rvPatL`, `rvOfMsgL msg`: `rvOfMsg(msg)`: the resource version after the first occurrence of
  `"ResourceVersion in object meta: "` in `msg` (`parseRV`), or `0`;
- `rvOfMsgL_preMsgL`: on a failed resource-version precondition's message (`preMsgL`, its RV branch),
  `rvOfMsg` reads the object's resource version back, when the precondition's string is shorter than
  the pattern (the generator's is a `rvString`: 0 or 8 bytes);
- `decItemRVsL_encItemsL`: when the items `encItemsL os` decode at all (and their encoding is shorter
  than `2^64`), `decodeItemRVs` gives `os`' resource versions (the framing carries them);
- `HistOpOk x y`: what `HistoryRevs` needs of one operation to name every revision `OpAnchors` asks
  for (both facts above's premises).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section pure
variable [GooseExts]

/-- `rvOfMsg`'s pattern. -/
def rvPatL : GoString := go!"ResourceVersion in object meta: "

/-- `rvOfMsg(msg)`: the revision after the pattern's first occurrence, or `0`. -/
def rvOfMsgL (msg : GoString) : w64 :=
  match (List.range msg.length).find? (fun i => decide (rvPatL <+: msg.drop i)) with
  | none => 0
  | some i => (parseRVD (msg.drop (i + rvPatL.length))).getD 0

/-- `preMsgL`'s fixed prefix on the resource-version branch. -/
abbrev preRVHeadL : GoString := go!"Precondition failed: ResourceVersion in precondition: "

/-- A prefix of `A ++ B` agrees with `A` where both are defined. -/
theorem zip_eq_of_prefix_append {α : Type} [DecidableEq α] :
    ∀ (A B pat : List α), pat <+: A ++ B → ∀ q ∈ A.zip pat, q.1 = q.2
  | [], _, _, _, q, hq => by simp at hq
  | _ :: _, _, [], _, q, hq => by simp at hq
  | a :: A, B, p :: pat, h, q, hq => by
    rw [List.cons_append, List.cons_prefix_cons] at h
    simp only [List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact h.1.symm
    · exact zip_eq_of_prefix_append A B pat h.2 q hq

theorem preRVHead_noPat : ∀ j < preRVHeadL.length,
    ∃ q ∈ (preRVHeadL.drop j).zip rvPatL, q.1 ≠ q.2 := by decide

theorem rvPat_noComma : ∀ b ∈ rvPatL, b ≠ (go!",").head! := by decide

theorem sep_noPat : ∃ q ∈ ((go!", ").drop 1).zip rvPatL, q.1 ≠ q.2 := by decide

theorem rvPatL_length : rvPatL.length = 32 := rfl

/-- The pattern does not start in a string shorter than it followed by `", "`. -/
theorem not_rvPat_prefix_comma (L R : GoString) (hL : L.length < rvPatL.length) :
    ¬ rvPatL <+: L ++ (go!", " ++ R) := by
  intro h
  have := h.getElem hL
  rw [List.getElem_append_right (Nat.le_refl _)] at this
  simp only [Nat.sub_self] at this
  exact rvPat_noComma _ (List.getElem_mem _) (by rw [this]; rfl)

/-- **`rvOfMsg` reads back a failed resource-version precondition's object revision.** -/
theorem rvOfMsgL_preMsgL (x : Input) (o : Obj) (hl : x.PreRV'.length < rvPatL.length)
    (hb : (x.HasPreUID' && !decide (x.PreUID' = o.UID')) = false) :
    rvOfMsgL (preMsgL x o) = o.ResourceVersion' := by
  have hmsg : preMsgL x o =
      preRVHeadL ++ (x.PreRV' ++ (go!", " ++ (rvPatL ++ rvStr o.ResourceVersion'))) := by
    simp only [preMsgL, hb, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rfl
  have hH : preRVHeadL.length = 54 := rfl
  have hC : (go!", ").length = 2 := rfl
  have hk : (preMsgL x o).drop (preRVHeadL.length + x.PreRV'.length + 2) =
      rvPatL ++ rvStr o.ResourceVersion' := by
    rw [hmsg, ← List.append_assoc, ← List.append_assoc]
    exact List.drop_left' (by simp only [List.length_append, hC])
  unfold rvOfMsgL
  rw [show (List.range (preMsgL x o).length).find? (fun i => decide (rvPatL <+: (preMsgL x o).drop i))
      = some (preRVHeadL.length + x.PreRV'.length + 2) from ?_]
  · dsimp only
    rw [← List.drop_drop, hk, List.drop_left, parseRVD_rvStr]; rfl
  rw [List.find?_range_eq_some]
  refine ⟨by rw [hk]; simp, ?_, ?_⟩
  · rw [List.mem_range, hmsg]; simp only [List.length_append, hC, rvPatL_length]; omega
  intro j hj
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hp
  rw [hmsg] at hp
  by_cases hjP : j < preRVHeadL.length
  · rw [List.drop_append_of_le_length (Nat.le_of_lt hjP)] at hp
    obtain ⟨q, hq, hne⟩ := preRVHead_noPat j hjP
    exact hne (zip_eq_of_prefix_append _ _ _ hp q hq)
  obtain ⟨m, rfl⟩ : ∃ m, j = preRVHeadL.length + m := ⟨j - preRVHeadL.length, by omega⟩
  rw [← List.drop_drop, List.drop_left] at hp
  by_cases hm : m ≤ x.PreRV'.length
  · rw [List.drop_append_of_le_length hm] at hp
    exact not_rvPat_prefix_comma _ _ (by simp; omega) hp
  · obtain rfl : m = x.PreRV'.length + 1 := by omega
    rw [← List.drop_drop, List.drop_left, List.drop_append_of_le_length (by rw [hC]; omega)] at hp
    obtain ⟨q, hq, hne⟩ := sep_noPat
    exact hne (zip_eq_of_prefix_append _ _ _ hp q hq)

/-- **A list's items that decode give their resource versions back.** -/
theorem decItemRVsL_encItemsL (os : List Obj) (hl : (encItemsL os).length < 2 ^ 64)
    (hs : (decItemRVsL (encItemsL os)).isSome) :
    ∃ ds, decItemRVsL (encItemsL os) = some ds ∧
      ds.map (·.ResourceVersion') = os.map (·.ResourceVersion') := by
  induction os with
  | nil => exact ⟨[], by simp [encItemsL, decItemRVsL], rfl⟩
  | cons o os ih =>
    have he : encItemsL (o :: os) = encItemL o ++ encItemsL os := by
      simp [encItemsL_eq]
    rw [he] at hl hs ⊢
    have hl' : (encItemsL os).length < 2 ^ 64 := by simp at hl; omega
    obtain ⟨e, he'⟩ : ∃ e, e = encodeWith tagV1 o := ⟨_, rfl⟩
    have hel : e.length < 2 ^ 64 := by simp [encItemL, ← he', rvBytes_length] at hl; omega
    have hn : (bytesBE (rvBytes (W64 (e.length : Int)))).toNat = e.length := by
      rw [bytesBE_rvBytes]; simp only [W64, BitVec.toNat_ofInt]; omega
    have hne : encItemL o ++ encItemsL os ≠ [] := by simp [encItemL, rvBytes]
    have hdrop : (encItemL o ++ encItemsL os).drop 16 = e ++ encItemsL os := by
      simp [encItemL, ← he', rvBytes]
    have h8 : ((encItemL o ++ encItemsL os).drop 8).take 8 = rvBytes (W64 (e.length : Int)) := by
      simp [encItemL, ← he', rvBytes]
    have h0 : (encItemL o ++ encItemsL os).take 8 = rvBytes o.ResourceVersion' := by
      simp [encItemL, ← he', rvBytes]
    have hlen16 : ¬ (encItemL o ++ encItemsL os).length < 16 := by
      simp [encItemL, rvBytes]
    have hunf : decItemRVsL (encItemL o ++ encItemsL os) =
        match decodeD e with
        | none => none
        | some d => (decItemRVsL (encItemsL os)).map fun rest =>
            { d with ResourceVersion' := o.ResourceVersion' } :: rest := by
      rw [decItemRVsL]
      simp only [hne, hlen16, dite_false, ite_false]
      simp only [hdrop, h8, h0, hn]
      simp only [bytesBE_rvBytes, List.length_append, List.take_left', List.drop_left']
      simp only [Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false]
      rfl
    rw [hunf] at hs ⊢
    split at hs
    · simp at hs
    · rename_i d hd
      simp only [Option.isSome_map] at hs
      obtain ⟨ds, hds, hmap⟩ := ih hl' hs
      refine ⟨{ d with ResourceVersion' := o.ResourceVersion' } :: ds, by simp [hds], ?_⟩
      simp [hmap]

/-- **What `HistoryRevs` needs of one operation** (see the file header): the precondition's string is
shorter than `rvOfMsg`'s pattern, and a successful list's items decode, their encoding shorter than
`2^64`. -/
def HistOpOk (x : Input) (y : Output) : Prop :=
  x.PreRV'.length < rvPatL.length ∧
  (x.Kind' = W64 4 → y.Err' = W64 0 → (decItemRVsL y.Items').isSome ∧ y.Items'.length < 2 ^ 64)

end pure

end k8s_etcd3
end EtcdGrove
end Perennial
