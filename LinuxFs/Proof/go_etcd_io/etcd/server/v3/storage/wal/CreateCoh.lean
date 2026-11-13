/- Lean-first (no Rocq counterpart).

# Every claim the program holds is coherent (W4, `notes/wal-fsext-plan.md`, "W4 implementation log",
tenth session)

`ClaimCoh h j N` (`Cut.lean`: the claim's entries below its `next`, and a crash keeping all of them
leaves each of its names as it is now) is true of every claim, whose history is the shared history's
(`namesOf`, the shared invariant's `NamesCoh.hist`): `namesOf_coh` (pure: the log's entries in order;
replaying all of a slot's writers gives its current value, `prefTree_frame` past the last one), and
`osNames_coh` (a claim held: its history coherent). The minting of `Create`'s creating claim records
it (`CreatingOk`), for the rename's commit (`walsOk_create`), which cannot open the shared invariant.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDrop
public import GooseLang.Ext.Fs.CrashRegion
public import GooseLang.Ext.Fs.TreeCutProof
public import GooseLang.Ext.Fs.TreeShared

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- Every element of a filtered range is at most its last. -/
theorem le_getLast_filter_range {L : Nat} {p : Nat → Bool} {w : Nat}
    (hl : ((List.range L).filter p).getLast? = some w) :
    ∀ y ∈ (List.range L).filter p, y ≤ w := by
  have hpw : ((List.range L).filter p).Pairwise (· < ·) :=
    (List.pairwise_lt_range).filter p
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hl
  rw [hys] at hpw ⊢
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · exact Nat.le_of_lt ((List.pairwise_append.1 hpw).2.2 y hy w (List.mem_singleton_self _))
  · rw [List.mem_singleton.1 hy]; exact Nat.le_refl _

/-- **The tree now has a slot as its last writer left it** (all entries kept). -/
theorem now_entry_slotAfter (V : Hist) (j : Ino) (b : GoString) :
    V.now.entry j b = slotAfter V.1 V.2 (fun _ => True) j b := by
  classical
  have hnow : V.now = prefTree V.1 V.2 V.2.length := by
    simp [Hist.now, Hist.ops, prefTree]
  rw [hnow]
  unfold slotAfter lastKept
  split
  next w hl =>
    have hwm := List.mem_of_getLast? hl
    have hwL : w < V.2.length := List.mem_range.1 (List.mem_filter.1 hwm).1
    refine (prefTree_frame V.1 V.2 (u := w + 1) V.2.length (by omega) (Nat.le_refl _)
      (fun y e hy1 hy2 he hw => ?_))
    have := le_getLast_filter_range hl y (List.mem_filter.2 ⟨List.mem_range.2 hy2, by
      simp only [_root_.true_and, decide_eq_true_eq]; exact ⟨e, he, hw⟩⟩)
    omega
  next hl =>
    have hno : ∀ y (e : LogEntry), 0 ≤ y → y < V.2.length → V.2[y]? = some e →
        ¬ e.op.Writes j b := by
      intro y e _ hy he hw
      rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hl
      have := hl y (List.mem_range.2 hy)
      simp only [_root_.true_and, decide_eq_true_eq] at this
      exact this ⟨e, he, hw⟩
    rw [prefTree_frame V.1 V.2 (u := 0) V.2.length (Nat.zero_le _) (Nat.le_refl _) hno,
      prefTree_zero]

/-- **A claim whose history is the shared history's is coherent.** -/
theorem namesOf_coh (V : Hist) (hst : Starts V.2) (j : Ino) (N : NameSet) :
    ClaimCoh (namesOf V j N) j N := by
  classical
  refine ⟨fun xe hxe => ?_, fun K hK b hb => ?_⟩
  · rw [namesOf_ents] at hxe
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hxe
    unfold NamesH.next
    rw [namesOf_ents, List.getLast?_map]
    cases hl : ((List.range V.2.length).filter (fun x => decide
        (∃ e, V.2[x]? = some e ∧ ∃ b, N.Mem b ∧ e.op.Writes j b))).getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hl
      rw [hl] at hx; cases hx
    | some w =>
      simp only [Option.map_some, Option.getD_some]
      have := le_getLast_filter_range hl x hx
      omega
  · -- the crash keeping every entry: `regionCrashed_of_cut` over the tree now
    have hr := regionCrashed_of_cut (V := V) (S := fun _ => True) (m' := V.now) (n := V.2.length)
      (c := V.2.length) hst (fun _ _ _ _ => trivial) (fun _ _ => trivial) (Nat.le_refl _)
      (fun j' b' => now_entry_slotAfter V j' b') [(j, N, namesOf V j N)]
      (fun cc hcc => by rw [List.mem_singleton.1 hcc])
    obtain ⟨K', hK1, hK2, hK3⟩ := hr
    have hmem : ((j, N, namesOf V j N) : Claim) ∈ [(j, N, namesOf V j N)] := List.mem_singleton_self _
    have hall : ∀ xe ∈ (namesOf V j N).ents, K' xe.1 := by
      intro xe hxe
      have hx : xe.1 < V.2.length := by
        rw [namesOf_ents] at hxe
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hxe
        exact List.mem_range.1 (List.mem_filter.1 hx).1
      exact hK2 _ hmem xe.1 xe.2.1 xe.2.2 hxe hx
    rw [valAfter_congrK _ j K K' b (fun xe hxe => ⟨fun _ => hall xe hxe, fun _ => hK xe hxe⟩),
      ← hK3 _ hmem b hb]
    show _ = restrictN N (entsOf V.now j) !! b
    rw [restrictN_lookup _ _ _ hb, entsOf_entry]

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **A claim held is coherent.** -/
theorem osNames_coh (R : Roots) (j : Ino) (N : NameSet) (dq : DFrac) (h : NamesH) {Em : CoPset}
    (hE : ↑osShN ⊆ Em) :
    ⊢ osSharedInv (L := L) R -∗ osNames (L := L) j N dq h ={Em}=∗
      osNames (L := L) j N dq h ∗ ⌜ClaimCoh h j N⌝ := by
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
  rw [hh]; exact namesOf_coh Vs hcoh.2.starts j N

end iris

end WalFs
end EtcdGrove
end Perennial

end
