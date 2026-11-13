/- Lean-first (no Rocq counterpart).

# The drop of a name off the area claim, as a step (W4, `notes/wal-fsext-plan.md`, "W4 implementation
log", ninth session)

`Create` needs the whole claim on `nm.tmp` (`RemoveAll`, `CreateDirAll`, the segment's creation), and
`cleanupWAL` the one on `nm.broken.<time>`; the program holds half of the area claim `(jr, N, h)`
(`walAreaRes`), the invariant the other half. `walInvBody_drop` (a ghost step, the file system's shared
invariant and the WAL invariant's contents open, the lock free) takes the invariant's half of the
area claim and gives it back off the name `b`: the program gets the whole claim on `.only [b]` and keeps
its half of the rest. The invariant's facts carry over by `CreateDropInv.lean`; what they need of the
step: the area claim is the invariant's claim on the WAL name `nm` (`WalsCreateOk`, and two claims of
one directory sharing a name are one, `osClaims_keys`), it occurs once (a third half would be invalid),
it is no WAL directory's claim (the lock free, `walParked` holds the program's half of every such claim:
three halves again), the claims are one log's (`osClaims_log`), and the creating map is empty (a
non-empty one holds the lock token).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDropInv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The first occurrence of a member. -/
theorem List.split_first {α : Type} [DecidableEq α] {c : α} :
    ∀ {l : List α}, c ∈ l → ∃ l1 l2, l = l1 ++ c :: l2 ∧ c ∉ l1
  | [], h => absurd h (List.not_mem_nil)
  | a :: l, h => by
    by_cases ha : a = c
    · subst ha; exact ⟨[], l, rfl, List.not_mem_nil⟩
    · obtain ⟨l1, l2, rfl, h1⟩ := List.split_first (List.mem_of_ne_of_mem (Ne.symm ha) h)
      refine ⟨a :: l1, l2, rfl, ?_⟩
      rintro (_ | ⟨_, hm⟩)
      · exact ha rfl
      · exact h1 hm

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The claims held are keys of the claims' authority. -/
theorem claims_keys (Γn : GMap (Ino × NameSet) NamesH) :
    ∀ cl : List (Claim × DFrac),
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn -∗ osClaims L cl -∗
      ⌜∀ c ∈ cl, c.1.2.1 ≠ .only [] → Γn !! (c.1.1, c.1.2.1) = some c.1.2.2⌝ ∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn Γn ∗ osClaims L cl
  | [] => by
    iintro HA Hc
    iframe
    ipureintro; intro c hc; cases hc
  | c :: cl => by
    iintro HA Hc
    icases (osClaims_cons L c cl).1 $$ Hc with ⟨H1, Hc⟩
    icases claims_keys Γn cl $$ HA Hc with ⟨%hcl, HA, Hc⟩
    by_cases hN : c.1.2.1 = .only []
    · iframe HA
      isplitr
      · ipureintro
        intro c' hc' hne
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact absurd hN hne
        · exact hcl c' hc' hne
      iapply (osClaims_cons L c cl).2
      iframe
    · rw [osNames_of_ne _ _ hN]
      icases gAuth_lookup _ _ _ _ _ _ $$ HA H1 with %h1
      iframe HA
      isplitr
      · ipureintro
        intro c' hc' hne
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact h1
        · exact hcl c' hc' hne
      iapply (osClaims_cons L c cl).2
      rw [osNames_of_ne _ _ hN]
      iframe

/-- **A claim held and a list of claims**: each claim of the list on the same directory sharing a
name with it is it (same names, same history; `NamesCoh.disj`). -/
theorem osClaims_keys (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH)
    (cl : List (Claim × DFrac)) (hN : N ≠ .only []) {Em : CoPset} (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N dq h -∗ osClaims L cl ={Em}=∗
      osNames (L := L) j N dq h ∗ osClaims L cl ∗
      ⌜∀ c ∈ cl, c.1.1 = j → ∀ b, N.Mem b → c.1.2.1.Mem b → c.1.2.1 = N ∧ c.1.2.2 = h⌝ := by
  rw [osNames_of_ne dq h hN]
  unfold osSharedInv
  iintro #Hsi H Hc
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAn H with %h1
  icases claims_keys Γn cl $$ HAn Hc with ⟨%hcl, HAn, Hc⟩
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe
  ipureintro
  intro c hc hj b hb hb'
  have hne : c.1.2.1 ≠ .only [] := nameSet_ne_empty hb'
  have h2 := hcl c hc hne
  rw [hj] at h2
  have hNN : c.1.2.1 = N := Classical.byContradiction fun hn =>
    hcoh.2.disj j N c.1.2.1 h c.1.2.2 b h1 h2 (Ne.symm hn) hb hb'
  refine ⟨hNN, ?_⟩
  rw [hNN, h1] at h2
  cases h2; rfl

/-- **A claim's history is its own restriction** (every entry writes one of its names). -/
theorem osNames_self (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) {Em : CoPset}
    (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N dq h ={Em}=∗
      osNames (L := L) j N dq h ∗ ⌜h.restrict j N = h⌝ := by
  unfold osSharedInv
  iintro #Hsi H
  imod inv_acc hE $$ Hsi with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%Vs, %Γn, Hs, HAn, %hcoh, Halen, HAlog⟩
  icases osNames_auth L hcoh.2 _ _ _ _ $$ HAn H with %hh
  imod Hclose $$ [Hs HAn Halen HAlog] with -
  · inext; iexists Vs, Γn; iframe; ipureintro; exact hcoh
  imodintro
  iframe H
  ipureintro
  rw [hh]; exact namesOf_restrict_self Vs j N

/-- Two halves of a claim make it whole. -/
theorem osNames_halves (j : Ino) (N : NameSet) (h h' : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own (1 : Qp).half) h -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h' -∗
      ⌜h = h'⌝ ∗ osNames (L := L) j N (DFrac.own 1) h := by
  rw [osNames_of_ne _ h hN, osNames_of_ne _ h' hN, osNames_of_ne _ h hN]
  iintro H1 H2
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  obtain ⟨-, rfl⟩ := hv
  isplitr
  · ipureintro; rfl
  have hs := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) (1 : Qp).half
    (1 : Qp).half h
  rw [Qp.half_add_half] at hs
  iapply hs.2
  iframe

/-- A whole claim in halves. -/
theorem osNames_halve (j : Ino) (N : NameSet) (h : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own 1) h -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h ∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h := by
  rw [osNames_of_ne (DFrac.own 1) h hN, osNames_of_ne (DFrac.own (1 : Qp).half) h hN]
  iintro H
  have hs := gElem_split (gooseOsGS (L := L)) (gooseOsGS (L := L)).γn (j, N) (1 : Qp).half
    (1 : Qp).half h
  rw [Qp.half_add_half] at hs
  iapply hs.1
  iexact H

/-- **Three halves of a claim are invalid.** -/
theorem osNames_three_halves (j : Ino) (N : NameSet) (h1 h2 h3 : NamesH) (hN : N ≠ .only []) :
    ⊢ osNames (L := L) j N (DFrac.own (1 : Qp).half) h1 -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h2 -∗
      osNames (L := L) j N (DFrac.own (1 : Qp).half) h3 -∗ False := by
  iintro H1 H2 H3
  icases osNames_halves (L := L) j N h1 h2 hN $$ H1 H2 with ⟨-, H⟩
  rw [osNames_of_ne (DFrac.own 1) h1 hN, osNames_of_ne (DFrac.own (1 : Qp).half) h3 hN]
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H H3 with %hv
  exfalso
  have := DFrac.valid_own_op hv.1
  simp at this

end iris

end WalFs
end EtcdGrove
end Perennial

end
