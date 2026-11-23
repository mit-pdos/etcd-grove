/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/IdBound.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
GAP SWB-13 (round 14): a registered command's id is small (`sp.inv`'s body: its client is a
tracked one, `1 ≤ cl ≤ 6`, and its number is below `2^25`), so a duplicate-free list of
registered ids is shorter than `6·2^32` — below `2^62`, what a fast ack's `depWf` needs.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SeqBound
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- A small id (see the file header). -/
def swift.idSmall (x : sp.CmdId) : Prop := 1 ≤ x.cl.toInt ∧ x.cl.toInt ≤ 6

/-- A duplicate-free list of small ids has at most `6·2^32` entries. -/
theorem swift.small_ids_len (l : List sp.CmdId) (hnd : l.Nodup) (hs : ∀ x ∈ l, swift.idSmall x) :
    l.length ≤ 6 * 2 ^ 32 := by
  let f : sp.CmdId → Nat := fun x => (x.cl.toNat - 1) * 2 ^ 32 + x.seq.toNat
  have hcl : ∀ x ∈ l, 1 ≤ x.cl.toNat ∧ x.cl.toNat ≤ 6 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hs x hx
    have h3 := swift.cl_toNat_lt _ h1
    rw [BitVec.toInt_eq_toNat_cond] at h2
    have := x.cl.isLt
    constructor
    · exact h3.1
    · split at h2 <;> omega
  have hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
    intro x hx y hy he
    obtain ⟨a1, a2⟩ := hcl x hx
    obtain ⟨b1, b2⟩ := hcl y hy
    have sx := x.seq.isLt
    have sy := y.seq.isLt
    simp only [f] at he
    have h1 : x.cl.toNat = y.cl.toNat := by omega
    have h2 : x.seq.toNat = y.seq.toNat := by omega
    cases x; cases y
    simp only at h1 h2
    rw [BitVec.toNat_inj] at h1 h2
    subst h1; subst h2; rfl
  have hm : (l.map f).Nodup := swift.nodup_map_on f l hinj hnd
  have := swift.nodup_nat_len hm (n := 6 * 2 ^ 32) (by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨a1, a2⟩ := hcl x hx
    have := x.seq.isLt
    simp only [f]
    have : (x.cl.toNat - 1) * 2 ^ 32 ≤ 5 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    omega)
  simpa using this

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
variable {γ : sp.Names} {γc γm γl : GName}

/-- **A registered command's id is small** (`sp.inv`'s body). -/
theorem swift.cmdIs_small (x : sp.CmdId) (c : sp.Cmd) :
    sp.inv γ γc γm γl ∗ sp.cmdIs γ x c ⊢ |={↑sp.spN}=> ⌜swift.idSmall x⌝ := by
  unfold sp.inv sp.cmdIs
  iintro ⟨#Hinv, #Hc⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, >%HDom, Hcmds, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HC Hc
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes Hproto HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    ipureintro
    exact ⟨Hrepr, Hcl, HDom⟩
  imodintro
  ipureintro
  obtain ⟨⟨n, hn, -⟩, -⟩ := Hcl x c Hlk
  exact HDom.2 x.cl n hn

theorem swift.bigSepL_small : ∀ (s : sp.Seq) (Φ : Nat → sp.CmdId × sp.Cmd → IProp netDistGF),
    (∀ i p, Φ i p ⊢ sp.cmdIs γ p.1 p.2) →
    sp.inv γ γc γm γl ∗ ([∗list] i ↦ p ∈ s, Φ i p) ⊢ |={↑sp.spN}=> ⌜∀ p ∈ s, swift.idSmall p.1⌝
  | [], _, _ => by
    iintro -
    imodintro
    ipureintro
    simp
  | a :: s, Φ, hΦ => by
    iintro ⟨#Hinv, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, Hs⟩
    ihave Ha := hΦ 0 a $$ H0
    imod swift.cmdIs_small a.1 a.2 $$ [Hinv Ha] with %ha
    · iframe Hinv Ha
    imod swift.bigSepL_small s (fun k p => Φ (k + 1) p) (fun k p => hΦ (k + 1) p) $$ [Hinv Hs]
      with %hs
    · iframe Hinv Hs
    imodintro
    ipureintro
    intro p hp
    rcases List.mem_cons.mp hp with e | hp
    · subst e; exact ha
    · exact hs p hp

/-- The commands of a `locLb` have small ids. -/
theorem swift.locLb_small (r b : Nat) (s : sp.Seq) :
    sp.inv γ γc γm γl ∗ sp.locLb γ r b s ⊢ |={↑sp.spN}=> ⌜∀ p ∈ s, swift.idSmall p.1⌝ := by
  unfold sp.locLb
  exact swift.bigSepL_small s _ (fun _ _ => by iintro ⟨-, H⟩; iexact H)

end laws

end Perennial.github_com.imdea_software.swiftpaxos
