/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/CmdStr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`CommandId.String` (defs.go:173: `fmt.Sprintf("%v,%v", cmdId.ClientId, cmdId.SeqNum)`): its
function `swift.cmdStr` (the two `int32`s' decimals with a comma between), injective
(`swift.cmdStr_inj`: a decimal has no comma, and a decimal determines its integer), and the
method's specs `swift.CommandId.String.specS swift.cmdStr` and `swift.CommandId.String.specI`
proved from the code over `fmt.Sprintf`'s spec (the `str` the run loop's allocation and the
arms take: ServersLink).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## The function and its injectivity (pure) -/

/-- `CommandId.String`'s result: `"<ClientId>,<SeqNum>"` (decimals of the `int32`s). -/
def swift.cmdStr (x : swift.CommandId) : GoString :=
  fmt.decimal (sint.Z x.ClientId') ++ W8 44 :: fmt.decimal (sint.Z x.SeqNum')

/-- The value of a digit string (most significant first). -/
def swift.digitsVal (s : GoString) : Nat :=
  s.foldl (fun acc c => acc * 10 + (uint.nat c - 48)) 0

theorem swift.digitsVal_append (s t : GoString) :
    swift.digitsVal (s ++ t) =
      t.foldl (fun acc c => acc * 10 + (uint.nat c - 48)) (swift.digitsVal s) := by
  unfold swift.digitsVal; rw [List.foldl_append]

theorem swift.digitsVal_decimalNat (n : Nat) : swift.digitsVal (fmt.decimalNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [fmt.decimalNat_eq]
    have hd : uint.nat (fmt.digitByte (n % 10)) - 48 = n % 10 := by
      have : n % 10 < 10 := Nat.mod_lt _ (by omega)
      unfold fmt.digitByte
      have h2 : uint.nat (W8 (48 + (n % 10 : Nat))) = 48 + n % 10 := by
        rw [show ((48 + (n % 10 : Nat)) : Int) = ((48 + n % 10 : Nat) : Int) by push_cast; rfl]
        word
      omega
    split
    · rename_i h
      simp only [List.nil_append, swift.digitsVal, List.foldl_cons, List.foldl_nil]
      rw [hd]; omega
    · rename_i h
      rw [swift.digitsVal_append, ih (n / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hd]; omega

theorem swift.decimalNat_inj {a b : Nat} (h : fmt.decimalNat a = fmt.decimalNat b) : a = b := by
  have := congrArg swift.digitsVal h
  rwa [swift.digitsVal_decimalNat, swift.digitsVal_decimalNat] at this

theorem swift.decimalNat_head (n : Nat) : ∃ c t, fmt.decimalNat n = c :: t ∧ c ≠ W8 45 := by
  obtain ⟨c, t, he⟩ : ∃ c t, fmt.decimalNat n = c :: t := by
    cases h : fmt.decimalNat n with
    | nil => exact absurd h (fmt.decimalNat_ne_nil n)
    | cons c t => exact ⟨c, t, rfl⟩
  refine ⟨c, t, he, ?_⟩
  have hc := fmt.decimalNat_digits n c (by rw [he]; simp)
  intro hc'; subst hc'; rw [show uint.Z (W8 45) = 45 by rfl] at hc; omega

theorem swift.decimal_inj {a b : Int} (h : fmt.decimal a = fmt.decimal b) : a = b := by
  unfold fmt.decimal at h
  obtain ⟨ca, ta, hea, hca⟩ := swift.decimalNat_head a.natAbs
  obtain ⟨cb, tb, heb, hcb⟩ := swift.decimalNat_head b.natAbs
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp only [ha, hb, ↓reduceIte] at h
  · have := swift.decimalNat_inj (List.cons.inj h).2; omega
  · rw [heb] at h; exact absurd (List.cons.inj h).1.symm hcb
  · rw [hea] at h; exact absurd (List.cons.inj h).1 hca
  · have := swift.decimalNat_inj h; omega

theorem swift.comma_not_mem_decimal (z : Int) : W8 44 ∉ fmt.decimal z := by
  intro hm
  have hdig : ∀ c ∈ fmt.decimalNat z.natAbs, 48 ≤ uint.Z c ∧ uint.Z c ≤ 57 :=
    fmt.decimalNat_digits _
  unfold fmt.decimal at hm
  have e : uint.Z (W8 44) = 44 := rfl
  split at hm
  · rcases List.mem_cons.1 hm with h | h
    · exact absurd h (by decide)
    · have := hdig _ h; rw [e] at this; omega
  · have := hdig _ hm; rw [e] at this; omega

/-- Two lists split at the first occurrence of `c`. -/
theorem swift.append_cons_inj {α : Type} (c : α) :
    ∀ (l1 l2 r1 r2 : List α), c ∉ l1 → c ∉ l2 → l1 ++ c :: r1 = l2 ++ c :: r2 →
      l1 = l2 ∧ r1 = r2
  | [], [], _, _, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | [], b :: l2, _, _, _, h2, h => by
      have := (List.cons.inj h).1; subst this; simp at h2
  | a :: l1, [], _, _, h1, _, h => by
      have := (List.cons.inj h).1; subst this; simp at h1
  | a :: l1, b :: l2, r1, r2, h1, h2, h => by
      obtain ⟨hab, h'⟩ := List.cons.inj h
      obtain ⟨e1, e2⟩ := swift.append_cons_inj c l1 l2 r1 r2
        (fun hm => h1 (List.mem_cons_of_mem _ hm)) (fun hm => h2 (List.mem_cons_of_mem _ hm)) h'
      exact ⟨by rw [hab, e1], e2⟩

theorem swift.cmdStr_inj : Function.Injective swift.cmdStr := by
  intro x y h
  unfold swift.cmdStr at h
  obtain ⟨e1, e2⟩ := swift.append_cons_inj _ _ _ _ _ (swift.comma_not_mem_decimal _)
    (swift.comma_not_mem_decimal _) h
  have h1 := swift.decimal_inj e1
  have h2 := swift.decimal_inj e2
  cases x; cases y
  simp only at h1 h2
  rw [BitVec.toInt_inj.mp h1, BitVec.toInt_inj.mp h2]

section sprintf
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] [go.string ↓u go.string]

theorem swift.IntArgValue.uniq_int32 [go.IntoValInj w32] (n : w32) :
    ∀ z', fmt.IntArgValue (interface.mk go.int32 #n) z' → z' = sint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := fmt.IntArgValue.of_int32 h
  rw [go.intoVal_inj hv]

/-- `Sprintf("%v,%v", a, b)` for two `int32`s is exactly `a,b`. -/
theorem swift.SprintfOut_v_comma_v [go.IntoValInj w32] (a b : w32) (out : GoString)
    (h : fmt.SprintfOut go!"%v,%v" [interface.mkOk go.int32 #a, interface.mkOk go.int32 #b] out) :
    out = fmt.decimal (sint.Z a) ++ W8 44 :: fmt.decimal (sint.Z b) := by
  have hfmt : go!"%v,%v" = W8 37 :: W8 118 :: W8 44 :: W8 37 :: [W8 118] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := fmt.SprintfOut.int_inv (w := 0) (rest := W8 44 :: W8 37 :: [W8 118])
    (by decide) (fmt.IntArgValue.int32 a) (swift.IntArgValue.uniq_int32 a) h
  obtain ⟨o2, rfl, h2⟩ := fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := fmt.SprintfOut.int_inv (w := 0) (rest := []) (by decide)
    (fmt.IntArgValue.int32 b) (swift.IntArgValue.uniq_int32 b) h2
  rw [fmt.SprintfOut.done_inv h3, fmt.decimalPad_zero, fmt.decimalPad_zero]
  simp

end sprintf

/-! ## The method -/

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

theorem swift.CommandId.String.wp_proof : swift.CommandId.String.specS swift.cmdStr := by
  intro p dq x
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.int32 #x.ClientId', interface.mkOk go.int32 #x.SeqNum']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf _ _ _ _
    (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _)
      (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _) fmt.ArgsWf.nil))
    $$ [Hlit] as %s ⟨-, %Hout⟩
  · iexact Hlit
  rw [swift.SprintfOut_v_comma_v _ _ _ Hout,
    show fmt.decimal (sint.Z x.ClientId') ++ W8 44 :: fmt.decimal (sint.Z x.SeqNum') =
      swift.cmdStr x from rfl]
  iapply HΦ
  iframe

theorem swift.CommandId.String.wp_proofI : swift.CommandId.String.specI := by
  intro p x
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.int32 #x.ClientId', interface.mkOk go.int32 #x.SeqNum']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf _ _ _ _
    (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _)
      (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.int32 _) fmt.ArgsWf.nil))
    $$ [Hlit] as %s ⟨-, -⟩
  · iexact Hlit
  iapply HΦ
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
