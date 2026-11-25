-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/CCWireSound.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvRaft.Proof.go_etcd_io.raft.v3.CCCodecLemmas

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The bytes consumed by any successful varint loop form a single varint.
The last byte has at most one payload bit at offset nine. -/
private theorem ccVarintLoop_consumed (fuel : Nat) (pre input : List w8) (n : Nat)
    (acc shift v : w64) (j : Nat) (room : n + fuel = 10)
    (h : ccVarintLoop (pre ++ input) fuel n pre.length acc shift = some (v, j)) :
    ∃ wire rest, input = wire ++ rest ∧ j = pre.length + wire.length ∧ IsVarint wire ∧
      n + wire.length ≤ 10 ∧ varintVal wire < 2^(64-7*n) := by
  induction fuel generalizing pre input n acc shift with
  | zero => simp [ccVarintLoop] at h
  | succ k ih =>
    cases input with
    | nil => simp [ccVarintLoop] at h
    | cons c tail =>
      have atc : (pre ++ c :: tail)[pre.length]? = some c := by simp
      simp only [ccVarintLoop, atc] at h
      split at h
      · contradiction
      · rename_i hmax
        have hc : uint.Z c = (c.toNat : Int) := rfl
        split at h
        · rename_i hlast
          have hj := congrArg Prod.snd (Option.some.inj h)
          have hlow : c.toNat < 128 := by omega
          have hval : varintVal [c] = c.toNat := by simp [varintVal, Nat.mod_eq_of_lt hlow]
          have bound : c.toNat < 2^(64-7*n) := by
            by_cases hn : n = 9
            · subst n; change c.toNat < 2; omega
            · exact Nat.lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ 64-7*n by omega))
          refine ⟨[c], tail, rfl, ?_, ?_, ?_, hval ▸ bound⟩
          · simpa using hj.symm
          · refine ⟨by simp, by simp, ?_, ?_, ?_⟩
            · intro i hi; simp at hi
            · intro b hb; simp at hb; subst b; exact hlow
            · rw [hval]; exact Nat.lt_trans hlow (by decide)
          · simp; omega
        · rename_i hmore
          have hcHigh : 128 ≤ c.toNat := by omega
          have hn : n ≤ 8 := by omega
          rw [show pre ++ c :: tail = (pre ++ [c]) ++ tail by simp,
            show pre.length + 1 = (pre ++ [c]).length by simp] at h
          obtain ⟨wire, rest, rfl, hj, hw, hlen, hv⟩ := ih (pre ++ [c]) tail (n+1) _ _ (by omega) h
          have hne : wire ≠ [] := by intro he; subst wire; exact (by simpa using hw.1 : False)
          have hp : 2^(64-7*n) = 2^(64-7*(n+1)) * 128 := by
            rw [show 64-7*n = (64-7*(n+1))+7 by omega, Nat.pow_add]
          have val : varintVal (c::wire) < 2^(64-7*n) := by
            rw [hp, varintVal]; have := Nat.mod_lt c.toNat (by decide : 0 < 128); omega
          refine ⟨c :: wire, rest, rfl, ?_, ?_, ?_, val⟩
          · simp at hj ⊢; omega
          · refine ⟨by simp, by simp; omega, ?_, ?_, ?_⟩
            · intro i hi; cases i with
              | zero => exact hcHigh
              | succ i => exact hw.2.2.1 i (by simp at hi; omega)
            · intro b hb; apply hw.2.2.2.1 b
              cases wire <;> simp_all
            · exact Nat.lt_of_lt_of_le val (Nat.pow_le_pow_right (by decide) (by omega))
          · simp; omega

/-- Recover the wire bytes and the value from any successful varint read. -/
theorem ccVarintL_consumed (pre input : List w8) (v : w64) (j : Nat)
    (read : ccVarintL (pre ++ input) pre.length = some (v, j)) :
    ∃ wire rest, input = wire ++ rest ∧ j = pre.length + wire.length ∧
      IsVarint wire ∧ varintVal wire = uint.nat v := by
  obtain ⟨wire, rest, rfl, hj, hw, _, _⟩ :=
    ccVarintLoop_consumed 10 pre input 0 (W64 0) (W64 0) v j rfl read
  have enc := ccVarintL_wire wire pre rest hw
  rw [List.append_assoc, read] at enc
  have he := congrArg Prod.fst (Option.some.inj enc)
  change v = W64 (varintVal wire) at he
  have hbound := hw.2.2.2.2
  have hnat : uint.nat (W64 (varintVal wire)) = varintVal wire := by
    generalize varintVal wire = k at hbound ⊢
    word
  exact ⟨wire, rest, rfl, hj, hw, by rw [he, hnat]⟩

/-- Tags within the value of a group are retained with their original encoding. -/
theorem ccTagL_consumed (pre input : List w8) (t j : Nat)
    (read : ccTagL (pre ++ input) pre.length (2^31-1) = some (t, j)) :
    ∃ wire rest, input = wire ++ rest ∧ j = pre.length + wire.length ∧
      TagOk false (t/8) (t%8) wire := by
  unfold ccTagL at read
  cases hv : ccVarintL (pre ++ input) pre.length with
  | none => simp [hv] at read
  | some pair =>
    obtain ⟨v, k⟩ := pair
    simp only [hv] at read
    change (if 1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^31-1
      then some (uint.nat v, k) else none) = some (t, j) at read
    split at read
    · rename_i h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj read)
      obtain ⟨wire, rest, heq, hj, hw, hval⟩ := ccVarintL_consumed pre input v k hv
      refine ⟨wire, rest, heq, hj, h.1, ?_, hw, ?_⟩
      · change uint.nat v / 8 < 2^31; omega
      · rw [hval]; omega
    · contradiction

theorem ccSkipScalar_consumed (pre input : List w8) (d num wt j : Nat)
    (read : ccSkipScalar (pre ++ input) pre.length wt = some j) :
    ∃ wire rest, input = wire ++ rest ∧ j = pre.length + wire.length ∧ WVal d num wt wire := by
  match wt with
  | 0 =>
    unfold ccSkipScalar at read
    cases hv : ccVarintL (pre ++ input) pre.length with
    | none => simp [hv] at read
    | some pair =>
      obtain ⟨v, k⟩ := pair
      simp [hv] at read; subst j
      obtain ⟨wire, rest, he, hj, hw, _⟩ := ccVarintL_consumed pre input v k hv
      exact ⟨wire, rest, he, hj, .varint _ _ _ hw⟩
  | 1 | 5 =>
    all_goals
      simp only [ccSkipScalar, List.length_append] at read
      split at read
      · rename_i hl
        obtain rfl := Option.some.inj read
        first
        | refine ⟨input.take 8, input.drop 8, (List.take_append_drop ..).symm, ?_, .i64 _ _ _ ?_⟩
        | refine ⟨input.take 4, input.drop 4, (List.take_append_drop ..).symm, ?_, .i32 _ _ _ ?_⟩
        all_goals simp; omega
      · contradiction
  | 2 =>
    unfold ccSkipScalar ccFieldL at read
    cases hv : ccVarintL (pre ++ input) pre.length with
    | none => simp [hv] at read
    | some pair =>
      obtain ⟨v, k⟩ := pair
      simp only [hv] at read
      split at read
      · simp at read
      · rename_i hfits
        simp at read; subst j
        obtain ⟨size, tail, rfl, hk, hw, hval⟩ := ccVarintL_consumed pre input v k hv
        have hnat : uint.Z v = (uint.nat v : Int) := by word
        simp only [List.length_append] at hfits
        have hroom : uint.nat v ≤ tail.length := by omega
        have hlen : (tail.take (uint.nat v)).length = uint.nat v := by simp [hroom]
        refine ⟨size ++ tail.take (uint.nat v), tail.drop (uint.nat v), ?_, ?_, .len _ _ _ _ hw ?_⟩
        · simp
        · simp [hk, hlen, Nat.add_assoc]
        · rw [hval, hlen]
  | 3 | 4 | _+6 => all_goals simp [ccSkipScalar] at read

/-- A byte sequence that completes the open groups from innermost to
outermost. Each remaining body uses the depth available at its stack level. -/
private inductive CCGroupCloses : List Nat → List w8 → Prop where
  | nil : CCGroupCloses [] []
  | close {parent : Nat} {outer : List Nat} {body etag tail : List w8} :
      WFields (10000-outer.length) body → TagOk false parent 4 etag →
      CCGroupCloses outer tail → CCGroupCloses (parent :: outer) (body ++ etag ++ tail)

private theorem ccGroupLoop_consumed (fuel : Nat) (pre input : List w8) (opened : List Nat) (j : Nat)
    (read : ccGroupLoop (pre ++ input) fuel pre.length opened = some j) :
    ∃ wire rest, input = wire ++ rest ∧ j = pre.length + wire.length ∧ CCGroupCloses opened wire := by
  induction fuel generalizing pre input opened with
  | zero =>
    cases opened with
    | nil => exact ⟨[], input, rfl, (Option.some.inj read).symm, .nil⟩
    | cons => simp [ccGroupLoop] at read
  | succ fuel ih =>
    cases opened with
    | nil => exact ⟨[], input, rfl, (Option.some.inj read).symm, .nil⟩
    | cons parent outer =>
      simp only [ccGroupLoop] at read
      cases ht : ccTagL (pre ++ input) pre.length (2^31-1) with
      | none => simp [ht] at read
      | some ts =>
        obtain ⟨tag, start⟩ := ts
        obtain ⟨tb, post, rfl, rfl, htag⟩ := ccTagL_consumed pre input tag start ht
        simp only [ht, Option.bind_some] at read
        let pt := pre ++ tb
        have hbytes : pre ++ (tb ++ post) = pt ++ post := by simp [pt]
        have hstart : pre.length + tb.length = pt.length := by simp [pt]
        rw [hbytes, hstart] at read
        change (match tag % 8 with
          | 3 => if outer.length + 1 ≤ 10000 then ccGroupLoop (pt++post) fuel pt.length (tag/8 :: parent :: outer) else none
          | 4 => if tag/8 = parent then ccGroupLoop (pt++post) fuel pt.length outer else none
          | wt => (ccSkipScalar (pt++post) pt.length wt).bind fun k => ccGroupLoop (pt++post) fuel k (parent :: outer)) = some j at read
        split at read
        · rename_i h3
          split at read
          · rename_i room
            obtain ⟨w, rest, rfl, hj, hcl⟩ := ih pt post _ read
            cases hcl with
            | @close _ _ inner etag next hinner he hnext =>
              cases hnext with
              | @close _ _ body pend tail hbody hp htail =>
                have depth : 10000-outer.length = (10000-(parent :: outer).length)+1 := by simp; omega
                have hvalue : WVal (10000-outer.length) (tag/8) 3 (inner ++ etag) := depth ▸ .group _ _ _ _ hinner he
                rw [h3] at htag
                have fields := WFields.cons _ _ _ tb _ _ htag hvalue hbody
                refine ⟨_, rest, ?_, ?_, CCGroupCloses.close fields hp htail⟩
                · simp [List.append_assoc]
                · simpa [pt, List.length_append, Nat.add_assoc] using hj
          · contradiction
        · rename_i h4
          split at read
          · rename_i eqParent
            obtain ⟨w, rest, rfl, hj, hcl⟩ := ih pt post outer read
            rw [h4, eqParent] at htag
            refine ⟨tb ++ w, rest, by simp, ?_, ?_⟩
            · simpa [pt, Nat.add_assoc] using hj
            · exact CCGroupCloses.close (.nil _) htag hcl
          · contradiction
        · rename_i wt h3 h4
          cases hs : ccSkipScalar (pt ++ post) pt.length (tag%8) with
          | none => simp [hs] at read
          | some k =>
            obtain ⟨v, tail, rfl, rfl, hv⟩ := ccSkipScalar_consumed pt post (10000-outer.length) (tag/8) (tag%8) k hs
            simp only [hs, Option.bind_some] at read
            have hnext : ccGroupLoop ((pt ++ v) ++ tail) fuel (pt ++ v).length (parent::outer) = some j := by
              simpa [List.append_assoc, List.length_append] using read
            obtain ⟨w, rest, rfl, hj, hcl⟩ := ih (pt ++ v) tail _ hnext
            cases hcl with
            | @close _ _ body etag ending hbody he htail =>
              have fields := WFields.cons _ _ _ tb v body htag hv hbody
              refine ⟨_, rest, ?_, ?_, CCGroupCloses.close fields he htail⟩
              · simp [List.append_assoc]
              · simpa [pt, Nat.add_assoc] using hj

/-- Parsing determines the exact group or scalar value that the caller can
append to a protobuf unknown-field buffer. -/
theorem ccSkipField_value {b : List w8} {i tag j : Nat} (hi : i ≤ b.length)
    (h : ccSkipField b i tag = some j) :
    WVal 10001 (tag/8) (tag%8) (subslice i j b) := by
  let pre := b.take i
  let input := b.drop i
  have hbytes : b = pre ++ input := (List.take_append_drop ..).symm
  have hidx : i = pre.length := by simp [pre, hi]
  have finish : ∀ (wire rest : List w8), input = wire ++ rest →
      j = pre.length + wire.length → subslice i j b = wire := by
    intro wire rest he hj
    rw [hidx, hbytes, he, hj, ← List.append_assoc, ← List.length_append]
    rw [subslice, List.take_left, List.drop_left]
  unfold ccSkipField at h
  split at h
  · rename_i h3
    unfold ccGroupAt at h
    rw [hidx, hbytes] at h
    obtain ⟨wire, rest, hin, hj, done⟩ := ccGroupLoop_consumed _ pre input [tag/8] j h
    rw [finish _ _ hin hj, h3]
    cases done with
    | close hbody he htail =>
      cases htail
      simp only [List.append_nil]
      exact WVal.group 10000 _ _ _ hbody he
  · rw [hidx, hbytes] at h
    obtain ⟨wire, rest, hin, hj, hw⟩ := ccSkipScalar_consumed pre input 10001 (tag/8) (tag%8) j h
    rw [finish _ _ hin hj]; exact hw

private theorem ufWire_append_fields {s : FieldSchema} {left right : List w8}
    (h : ufWire s left) (hr : ufWire s right) : ufWire s (left ++ right) := by
  induction h with
  | nil => exact hr
  | cons num wt tag v tail ht hv route _ ih =>
    simpa only [List.append_assoc] using ufWire.cons num wt tag v _ ht hv route ih

theorem ccUnknown_valid {schema : FieldSchema} {bs uf : List w8} {tag : w64} {atTag start j : Nat}
    (before : ufWire schema uf) (read : ccTagL bs atTag (2^29-1) = some (uint.nat tag, start))
    (skip : ccSkipField bs start (uint.nat tag) = some j)
    (route : Routed schema (uint.nat tag / 8) (uint.nat tag % 8)) :
    ufWire schema ((uf ++ ccVarint tag) ++ subslice start j bs) := by
  have hb := ccTagL_bound read
  have valid := ccSkipField_value hb.2 skip
  have limits : 1 ≤ uint.nat tag / 8 ∧ uint.nat tag / 8 ≤ 2^29-1 := by
    unfold ccTagL at read
    cases hv : ccVarintL bs atTag with
    | none => simp [hv] at read
    | some pair =>
      obtain ⟨v,k⟩ := pair
      simp only [hv] at read
      change (if 1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^29-1
        then some (uint.nat v, k) else none) = some (uint.nat tag, start) at read
      split at read
      · have he := congrArg Prod.fst (Option.some.inj read)
        change uint.nat v = uint.nat tag at he
        rw [← he]; assumption
      · contradiction
  have ht : TagOk true (uint.nat tag / 8) (uint.nat tag % 8) (ccVarint tag) := by
    refine ⟨limits.1, ?_, ?_⟩
    · change uint.nat tag / 8 < 2^29; omega
    · change varintEnc _ = varintEnc _; congr 1; omega
  rw [List.append_assoc]
  apply ufWire_append_fields before
  simpa using (ufWire.cons _ _ _ _ [] ht valid route (.nil : ufWire schema []))

end EtcdGrove
end Perennial
