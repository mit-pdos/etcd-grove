/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): raft's formatted ids
(`strconv.FormatUint(id, 10)`, `decStr`) as the checker parses them (`parseID`): each line's node,
vote, sender and receiver are the ids raft formatted.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSim
public import Proof.strconv.FormatUintDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

theorem baseDigits_ne_nil (b : Nat) (hb : 2 ≤ b) (n : Nat) : baseDigits b hb n ≠ [] := by
  rw [baseDigits]; split <;> simp

/-- The leading digit of a positive number is not 0. -/
theorem baseDigits_head (b : Nat) (hb : 2 ≤ b) (n : Nat) (hn : 1 ≤ n) :
    ∃ d ds, baseDigits b hb n = d :: ds ∧ d ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · exact ⟨n, [], rfl, by omega⟩
    · rename_i h
      have h1 : 1 ≤ n / b := by
        have := Nat.div_pos (by omega : b ≤ n) (by omega : 0 < b); omega
      obtain ⟨d, ds, hd, hd0⟩ := ih (n / b) (Nat.div_lt_self (by omega) (by omega)) h1
      exact ⟨d, ds ++ [n % b], by rw [hd]; rfl, hd0⟩

/-- A number below `b ^ k` has at most `max 1 k` digits. -/
theorem baseDigits_length (b : Nat) (hb : 2 ≤ b) : ∀ (k n : Nat), n < b ^ k →
    (baseDigits b hb n).length ≤ max 1 k := by
  intro k
  induction k with
  | zero => intro n hn; simp at hn; subst hn; rw [baseDigits]; simp [show 0 < b by omega]
  | succ k ih =>
    intro n hn
    rw [baseDigits]
    split
    · simp
    · rename_i h
      have : n / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at hn; exact hn
      have := ih (n / b) this
      simp only [List.length_append, List.length_singleton]
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at this; have : n / b < 1 := by simpa using (by assumption : n / b < b ^ 0)
          have := (Nat.div_lt_iff_lt_mul (by omega)).1 this; omega
        · exact h0
      omega

/-- The decimal digits' characters, as `gsStr` reads raft's bytes. -/
theorem digit_char (d : Nat) (hd : d < 10) : Char.ofNat (digitChar d).toNat = Char.ofNat (48 + d) := by
  unfold digitChar
  simp only [hd, ↓reduceIte]
  congr 1
  have : 48 + d < 256 := by omega
  simp; omega

/-- **Raft's formatted id parses to its number** (`parseID (FormatUint(w, 10))`). -/
theorem dchar_facts : ∀ d, d < 10 → (Char.ofNat (48 + d)).toNat = 48 + d ∧
    (Char.ofNat (48 + d)).isDigit = true ∧ (d ≠ 0 → Char.ofNat (48 + d) ≠ '0') := by
  decide

set_option linter.deprecated false in
theorem string_mk_toList (l : List Char) : (String.mk l).toList = l := by
  have : String.mk l = String.ofList l := rfl
  rw [this, String.toList_ofList]

theorem parseID_decStr (w : w64) : Etcdraft.parseID (gsStr (decStr w)) = some (uint.nat w) := by
  have hw : w.toNat = uint.nat w := rfl
  generalize hds : baseDigits 10 (by omega) (uint.nat w) = ds
  have hlt : ∀ d ∈ ds, d < 10 := by rw [← hds]; exact baseDigits_lt 10 (by omega) _
  have hcs : (gsStr (decStr w)).toList = ds.map (fun d => Char.ofNat (48 + d)) := by
    unfold gsStr
    rw [decStr_eq, hw, hds]
    rw [string_mk_toList, List.map_map]
    apply List.map_congr_left; intro d hd
    exact digit_char d (hlt d hd)
  have hval : digitsVal 10 ds = uint.nat w := by rw [← hds]; exact digitsVal_baseDigits 10 _ _
  have hn64 : uint.nat w < 2 ^ 64 := by word
  have hlen : ds.length ≤ 20 := by
    have := baseDigits_length 10 (by omega) 20 (uint.nat w) (by omega)
    rw [hds] at this; omega
  have hne : ds ≠ [] := by rw [← hds]; exact baseDigits_ne_nil _ _ _
  -- the fold is the digits' value
  have hfold : (ds.map (fun d => Char.ofNat (48 + d))).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 =
      digitsVal 10 ds := by
    unfold digitsVal
    rw [List.foldl_map]
    suffices ∀ (l : List Nat) (a : Nat), (∀ d ∈ l, d < 10) →
        l.foldl (fun acc d => acc * 10 + ((Char.ofNat (48 + d)).toNat - '0'.toNat)) a =
          l.foldl (fun a d => 10 * a + d) a from this ds 0 hlt
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons d l ih =>
      intro a hl
      simp only [List.foldl_cons]
      have hd := (dchar_facts d (hl d (by simp))).1
      rw [hd]
      have : (48 + d - '0'.toNat) = d := by
        have : '0'.toNat = 48 := rfl
        omega
      rw [this, Nat.mul_comm]
      exact ih _ (fun x hx => hl x (by simp [hx]))
  have hall : (ds.map (fun d => Char.ofNat (48 + d))).all Char.isDigit = true := by
    rw [List.all_eq_true]; intro c hc
    rw [List.mem_map] at hc; obtain ⟨d, hd, rfl⟩ := hc
    exact (dchar_facts d (hlt d hd)).2.1
  have he : (ds.map (fun d => Char.ofNat (48 + d))).isEmpty = false := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  have hhead : 1 < ds.length → (ds.map (fun d => Char.ofNat (48 + d))).head? ≠ some '0' := by
    intro h1
    have h10 : 10 ≤ uint.nat w := by
      rcases Nat.lt_or_ge (uint.nat w) 10 with hlt10 | h
      · exfalso
        have : ds = [uint.nat w] := by
          rw [← hds, baseDigits]; simp only [hlt10, ↓reduceIte]
        rw [this] at h1; simp at h1
      · exact h
    obtain ⟨d, ds', hd, hd0⟩ := baseDigits_head 10 (by omega) (uint.nat w) (by omega)
    rw [hds] at hd; subst hd
    simp only [List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
    exact (dchar_facts d (hlt d (by simp))).2.2 hd0
  unfold Etcdraft.parseID
  simp only [hcs, he, List.length_map, Bool.false_or]
  have h20 : decide (ds.length > 20) = false := by simp; omega
  rw [h20, Bool.false_or]
  rcases Nat.lt_or_ge 1 ds.length with h1 | h1
  · have : ((ds.map (fun d => Char.ofNat (48 + d))).head? == some '0') = false := by
      simpa using hhead h1
    simp only [this, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hall, hfold, hval, hn64]
  · have : decide (ds.length > 1) = false := by simp; omega
    simp only [this, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hall, hfold, hval, hn64]

/-- Raft's formatted voters, as the checker's set. -/
theorem toSet_decStr (xs : List w64) :
    Etcdraft.toSet (xs.map (fun x => gsStr (decStr x))) = some (Etcdraft.SetIds.mk (xs.map idAbs)) := by
  unfold Etcdraft.toSet
  have : (xs.map (fun x => gsStr (decStr x))).mapM Etcdraft.parseID = some (xs.map idAbs) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.mapM_cons, parseID_decStr, ih]
      rfl
  rw [this]; rfl

/-- **A node event's line** (no message, no configuration change: the events `traceNodeEvent`
logs but `ChangeConf`): its node, vote and configuration are raft's. -/
theorem parseLine_node (k : Nat) (e : TraceEv) (id vote : w64) (xs ys : List w64)
    (hnid : e.nid = decStr id) (hvote : e.vote = decStr vote)
    (hconf : e.conf = (xs.map decStr, ys.map decStr)) (hmsg : e.msg = none)
    (hname : Etcdraft.isMessageEvent (gsStr e.name) = false) (hcc : gsStr e.name ≠ "ChangeConf") :
    Etcdraft.parseLine k (evConv e) =
      .ok { ev := evConv e, nid := idAbs id, vote := idAbs vote, role := (evConv e).role,
            conf := (Etcdraft.SetIds.mk (xs.map idAbs), Etcdraft.SetIds.mk (ys.map idAbs)),
            «from» := 0, to := 0 } := by
  unfold Etcdraft.parseLine
  have h1 : Etcdraft.parseID (evConv e).nid = some (idAbs id) := by
    simp only [evConv, hnid]; exact parseID_decStr id
  have h2 : Etcdraft.parseID (evConv e).state.vote = some (idAbs vote) := by
    simp only [evConv, hvote]; exact parseID_decStr vote
  have h3 : Etcdraft.toSet (evConv e).conf.1 = some (Etcdraft.SetIds.mk (xs.map idAbs)) := by
    simp only [evConv, hconf, List.map_map]; exact toSet_decStr xs
  have h4 : Etcdraft.toSet (evConv e).conf.2 = some (Etcdraft.SetIds.mk (ys.map idAbs)) := by
    simp only [evConv, hconf, List.map_map]; exact toSet_decStr ys
  have h5 : (evConv e).msg = none := by simp [evConv, hmsg]
  have h6 : (evConv e).name = gsStr e.name := rfl
  simp [h1, h2, h3, h4, h5, h6, hname, hcc, bind, Except.bind, pure, Except.pure]

end TraceSim

end EtcdGrove
end Perennial
