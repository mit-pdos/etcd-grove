/- Lean-first (no Rocq counterpart).

# The WAL directories hold only files after a crash: the claims' fact (`walFoRes`, step 2 of
`notes/wal-units/tester.md`'s last handoff; `notes/wal-fsext-w4c-plan.md`, U3 log, third session)

The crash boot (`walBootCrash`) needs every WAL directory of the crashed tree to hold only files
(`BootFo`'s first part). A crash leaves at a claimed name what the claim's history held right after
its last kept entry (`RegionCrashed`, `NamesH.valAfter`), every entry below the invariant's commit
bound `n` kept. **`HistFoP P n j N h`**: no version a crash at the bound `n` may leave holds a
directory at a name of `N` satisfying `P` (for a WAL directory's claim, `P` = not a pipeline name:
the pipeline's names have claims of their own, `walTmpParked`). Weaker than "no version ever holds
a directory" (the history of a new WAL's directory, `Create`'s, holds the probe and the first segment's
creation, all below the bound when `Create` commits): what a crash may pick.

* `HistFoP.mono`: a larger bound keeps it (fewer crashes);
* `HistFoP.log`: a logged entry leaving no directory at the names it writes keeps it;
* `HistFoP.of_coh`: a coherent claim all of whose entries are below the bound has it iff its current
  names do (`Create`'s new directory, the boot's claims);
* `HistFoP.cur`: a coherent claim's current names hold no directory;
* `HistFoP.crash`: after a crash the claims allow, the name holds no directory.

Pure.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpNames

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs

/-- **No version of the history `h` a crash at the commit bound `n` may leave holds a directory at a
name of `N` satisfying `P`.** -/
def HistFoP (P : GoString → Prop) (n : Nat) (j : Ino) (N : NameSet) (h : NamesH) : Prop :=
  ∀ K : Nat → Prop, (∀ xe ∈ h.ents, xe.1 < n → K xe.1) → ∀ b, N.Mem b → P b →
    ∀ J, h.valAfter j K b ≠ some (.dir J)

/-- **A WAL directory's claim holds no directory a crash may leave, but at the pipeline's names.** -/
abbrev HistFoN (n : Nat) (j : Ino) (N : NameSet) (h : NamesH) : Prop :=
  HistFoP (· ∉ walTmps) n j N h

/-- **No directory at the names but the pipeline's** (a WAL directory's entries after a crash, at boot). -/
def NoDirX (e : Ents) : Prop := ∀ b J, b ∉ walTmps → e !! b ≠ some (.dir J)

/-- A larger commit bound keeps it. -/
theorem HistFoP.mono {P : GoString → Prop} {n n' : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hf : HistFoP P n j N h) (hn : n ≤ n') : HistFoP P n' j N h :=
  fun K hK => hf K (fun xe hxe hlt => hK xe hxe (Nat.lt_of_lt_of_le hlt hn))

/-- **An entry logged leaving no directory at the names of `N` it writes keeps it.** -/
theorem HistFoP.log {P : GoString → Prop} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hf : HistFoP P n j N h) (x : Nat) (e : LogEntry) (E : Ents)
    (hE : ∀ b, N.Mem b → P b → e.op.Writes j b → ∀ J, E !! b ≠ some (.dir J)) :
    HistFoP P n j N (h.log x e E) := by
  classical
  intro K hK b hb hP J
  have hK0 : ∀ xe ∈ h.ents, xe.1 < n → K xe.1 := fun xe hxe hlt =>
    hK xe (by simp [NamesH.log, hxe]) hlt
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  by_cases hw : K x ∧ e.op.Writes j b
  · rw [if_pos (by simp [hw])]
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    exact hE b hb hP hw.2 J
  · rw [if_neg (by simp [hw])]
    simp only [List.append_nil]
    exact hf K hK0 b hb hP J

/-- **A coherent claim all of whose entries are below the bound**: it holds iff its current names do. -/
theorem HistFoP.of_coh {P : GoString → Prop} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hc : ClaimCoh h j N) (hlt : ∀ xe ∈ h.ents, xe.1 < n)
    (hcur : ∀ b, N.Mem b → P b → ∀ J, h.cur !! b ≠ some (.dir J)) : HistFoP P n j N h := by
  intro K hK b hb hP J
  rw [hc.2 K (fun xe hxe => hK xe hxe (hlt xe hxe)) b hb]
  exact hcur b hb hP J

/-- **A coherent claim's current names hold no directory.** -/
theorem HistFoP.cur {P : GoString → Prop} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hf : HistFoP P n j N h) (hc : ClaimCoh h j N) :
    ∀ b, N.Mem b → P b → ∀ J, h.cur !! b ≠ some (.dir J) := by
  intro b hb hP J
  rw [← hc.2 (fun _ => True) (fun _ _ => trivial) b hb]
  exact hf (fun _ => True) (fun _ _ _ => trivial) b hb hP J

/-- A claim with nothing logged: it holds iff its names at boot do. -/
theorem HistFoP.of_boot {P : GoString → Prop} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (he : h.ents = []) (hb : ∀ b, N.Mem b → P b → ∀ J, h.boot !! b ≠ some (.dir J)) :
    HistFoP P n j N h := by
  intro K _ b hbN hP J
  unfold NamesH.valAfter
  rw [he]
  exact hb b hbN hP J

/-- **After a crash the claims allow, a name of a claim with the fact holds no directory.** -/
theorem HistFoP.crash {P : GoString → Prop} {cl : List Claim} {n : Nat} {m' : Tree}
    (hr : RegionCrashed cl n m') {c : Claim} (hc : c ∈ cl) (hf : HistFoP P n c.1 c.2.1 c.2.2)
    {b : GoString} (hb : c.2.1.Mem b) (hP : P b) : ∀ J, m'.entry c.1 b ≠ some (.dir J) := by
  obtain ⟨K, -, hK, hv⟩ := hr
  intro J
  rw [hv c hc b hb]
  exact hf K (fun xe hxe hlt => hK c hc xe.1 xe.2.1 xe.2.2 hxe hlt) b hb hP J

/-- A claim's fact for fewer names. -/
theorem HistFoP.sub {P : GoString → Prop} {n : Nat} {j : Ino} {N N' : NameSet} {h : NamesH}
    (hf : HistFoP P n j N h) (hs : ∀ b, N'.Mem b → N.Mem b) : HistFoP P n j N' h :=
  fun K hK b hb => hf K hK b (hs b hb)

/-- A claim's fact for a weaker name predicate. -/
theorem HistFoP.weaken {P P' : GoString → Prop} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    (hf : HistFoP P n j N h) (hP : ∀ b, P' b → P b) : HistFoP P' n j N h :=
  fun K hK b hb hb' => hf K hK b hb (hP b hb')

end WalFs
end EtcdGrove
end Perennial

end
