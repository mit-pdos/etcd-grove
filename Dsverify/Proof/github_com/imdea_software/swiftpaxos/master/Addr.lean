/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Addr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Pure facts about the replicas' addresses as the master builds them (`fmt.Sprintf("%s:%d", ...)`)
and as the frozen specs write them (`sp.addrPort`, `replicaAddrs`, `replicaRpcAddrs`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Perennial.Proof.fmt
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv Perennial.fmt

namespace master

/-- The replicas' IPs (`replicaAddrs[k]` is `replicaIps[k]:(7002 + k)`). -/
def replicaIps : List GoString :=
  [go!"127.0.0.1", go!"127.0.0.1", go!"127.0.0.1", go!"127.0.0.1", go!"127.0.0.1"]

theorem w8_toNat_of_lt (n : Nat) (h : n < 256) : (W8 n).toNat = n := by
  simp only [W8, BitVec.toNat_ofInt]
  omega

/-- A digit's byte. -/
def digitW8 (ch : Char) : w8 := W8 ch.toNat

theorem digitW8_digitChar : ∀ {d : Nat}, d < 10 → digitW8 (Nat.digitChar d) = digitByte d
  | 0, _ => by rw [Nat.digitChar_eq_zero.mpr rfl]; simp [digitW8, digitByte]
  | 1, _ => by rw [Nat.digitChar_eq_one.mpr rfl]; simp [digitW8, digitByte]
  | 2, _ => by rw [Nat.digitChar_eq_two.mpr rfl]; simp [digitW8, digitByte]
  | 3, _ => by rw [Nat.digitChar_eq_three.mpr rfl]; simp [digitW8, digitByte]
  | 4, _ => by rw [Nat.digitChar_eq_four.mpr rfl]; simp [digitW8, digitByte]
  | 5, _ => by rw [Nat.digitChar_eq_five.mpr rfl]; simp [digitW8, digitByte]
  | 6, _ => by rw [Nat.digitChar_eq_six.mpr rfl]; simp [digitW8, digitByte]
  | 7, _ => by rw [Nat.digitChar_eq_seven.mpr rfl]; simp [digitW8, digitByte]
  | 8, _ => by rw [Nat.digitChar_eq_eight.mpr rfl]; simp [digitW8, digitByte]
  | 9, _ => by rw [Nat.digitChar_eq_nine.mpr rfl]; simp [digitW8, digitByte]
  | _ + 10, h => by omega

theorem decimalNat_toDigits (n : Nat) :
    decimalNat n = (Nat.toDigits 10 n).map digitW8 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimalNat_eq, Nat.toDigits_eq_ite (by decide)]
    by_cases h : n < 10
    · simp only [h, ↓reduceIte, List.nil_append, List.map_cons, List.map_nil]
      rw [Nat.mod_eq_of_lt h, digitW8_digitChar h]
    · simp only [h, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
      rw [ih (n / 10) (by omega), digitW8_digitChar (Nat.mod_lt _ (by decide))]

/-- `Sprintf`'s `%s:%d` with a non-negative port is `addrPort`. -/
theorem decimal_addrPort (x : GoString) (n : w64) (h : 0 ≤ sint.Z n) :
    x ++ go!":" ++ decimal (sint.Z n) = sp.addrPort x n := by
  unfold sp.addrPort
  rw [decimal_of_nonneg h, decimalNat_toDigits]
  have : (sint.Z n).toNat = n.toNat := by
    have := BitVec.toInt_eq_toNat_of_msb (x := n)
    word
  rw [this]
  simp [digitW8]

section sprintf
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] [go.string ↓u go.string]

theorem sprintf_str_d [go.IntoValInj GoString] [go.IntoValInj w64] (x : GoString) (n : w64)
    (out : GoString)
    (h : out = _root_.Perennial.fmt.render [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      [.str x, .int (sint.Z n)]) :
    out = x ++ go!":" ++ decimal (sint.Z n) := by
  rw [h]; simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, _root_.Perennial.fmt.decimalPad_zero]

theorem sprintf_colon_d [go.IntoValInj w64] (n : w64) (out : GoString)
    (h : out = _root_.Perennial.fmt.render [.lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      [.int (sint.Z n)]) :
    out = go!":" ++ decimal (sint.Z n) := by
  rw [h]; simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, _root_.Perennial.fmt.decimalPad_zero]

end sprintf

/-- Splitting at the last colon. -/
theorem split_last {c : w8} : ∀ {a a' b b' : GoString}, c ∉ b → c ∉ b' →
    a ++ c :: b = a' ++ c :: b' → a = a' ∧ b = b'
  | [], [], _, _, _, _, h => by simp at h; exact ⟨rfl, h⟩
  | [], x :: a', b, b', hb, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact absurd (h ▸ List.mem_append_right _ (List.mem_cons_self ..)) hb
  | x :: a, [], b, b', _, hb', h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact absurd (h ▸ List.mem_append_right _ (List.mem_cons_self ..)) hb'
  | x :: a, y :: a', b, b', hb, hb', h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨h1, h2⟩ := split_last hb hb' h
      exact ⟨by rw [h1], h2⟩

theorem digit_toNat {ch : Char} (hd : ch.isDigit) : 48 ≤ ch.toNat ∧ ch.toNat ≤ 57 := by
  have := Char.isDigit_iff_toNat.mp hd
  simpa using this

theorem colon_not_mem_digits (n : Nat) : W8 58 ∉ (Nat.toDigits 10 n).map digitW8 := by
  intro h
  obtain ⟨ch, hch, he⟩ := List.mem_map.mp h
  have hd := digit_toNat (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hch)
  unfold digitW8 at he
  have := congrArg BitVec.toNat he
  rw [w8_toNat_of_lt _ (by omega)] at this
  have h58 : (W8 58).toNat = 58 := rfl
  omega

theorem digitW8_inj_digits {l l' : List Char} (hl : ∀ c ∈ l, c.toNat < 256)
    (hl' : ∀ c ∈ l', c.toNat < 256) (h : l.map digitW8 = l'.map digitW8) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons c l ih =>
    cases l' with
    | nil => simp at h
    | cons c' l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hc := hl c (List.mem_cons_self ..)
      have hc' := hl' c' (List.mem_cons_self ..)
      have e : c.toNat = c'.toNat := by
        have := congrArg BitVec.toNat h1
        unfold digitW8 at this
        rwa [w8_toNat_of_lt _ hc, w8_toNat_of_lt _ hc'] at this
      rw [Char.toNat_inj.mp e, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) h2]

theorem digits_lt256 (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.toNat < 256 := by
  intro c hc
  have hd := digit_toNat (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
  omega

theorem toDigits_inj {n n' : Nat}
    (h : (Nat.toDigits 10 n).map digitW8 = (Nat.toDigits 10 n').map digitW8) : n = n' := by
  have := digitW8_inj_digits (digits_lt256 n) (digits_lt256 n') h
  rw [← Nat.ofDigitChars_ten_toDigits (n := n), ← Nat.ofDigitChars_ten_toDigits (n := n'), this]

/-- The address of replica node `k`, split. -/
theorem replicaAddrs_eq : ∀ k < 5, replicaAddrs[k]? =
    replicaIps[k]?.map (fun ip => ip ++ W8 58 :: decimalNat (7002 + k))
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => by
    simp [decimalNat_eq, digitByte, replicaAddrs, replicaIps]
  | _ + 5, h => by omega

theorem replicaRpcAddrs_eq : ∀ k < 5, replicaRpcAddrs[k]? =
    replicaIps[k]?.map (fun ip => ip ++ W8 58 :: decimalNat (8002 + k))
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => by
    simp [decimalNat_eq, digitByte, replicaRpcAddrs, replicaIps]
  | _ + 5, h => by omega

/-- `addrPort ip port` is replica node `k`'s address only for its IP and port `7002 + k`. -/
theorem addrPort_replica {ip : GoString} {port : w64} {k : Nat}
    (h : replicaAddrs[k]? = some (sp.addrPort ip port)) :
    k < 5 ∧ replicaIps[k]? = some ip ∧ port = W64 (7002 + k) := by
  have hk : k < 5 := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa [replicaAddrs] using this
  rw [replicaAddrs_eq k hk] at h
  obtain ⟨ip', hip, h⟩ := Option.map_eq_some_iff.mp h
  unfold sp.addrPort at h
  have hd : (Nat.toDigits 10 port.toNat).map (fun ch => W8 ch.toNat) =
      (Nat.toDigits 10 port.toNat).map digitW8 := rfl
  rw [hd, List.append_assoc, List.singleton_append, decimalNat_toDigits] at h
  obtain ⟨h1, h2⟩ := split_last (colon_not_mem_digits _) (colon_not_mem_digits _) h
  subst h1
  have := toDigits_inj h2
  refine ⟨hk, hip, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [← this]
  simp only [W64, BitVec.toNat_ofInt]
  omega

end master

end Perennial.github_com.imdea_software.swiftpaxos
