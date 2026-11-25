/-
**Fresh database files at program start, from the tree** (S3e, 2026-11-17;
`notes/bbolt-integration-plan.md`). Until S3e an axiom (`goose_adequacy_start_files`,
`Proof/runtime/Start.lean`) handed a closed theorem's proof `backend.fileHolds f ∅` for each fresh
database file `f` (premise `dbFilesAbsent`). Since `backend.fileHolds` is the concrete claim on the
file's name in the tree's shared mode, it is derived instead, from what the file extension's start
gives (`osStart`: the tree's shared view, filled in, as `fs_start` opens it) and a premise on the
initial state (no file at the names): `start_fileHolds` opens the tree's shared invariants
(`osSwitchKit_open`, giving `osShared`), splits the claim on the root directory's names into one claim per fresh name
(`claims_split`), and gives each name a share of the root's call permission (its key's, since
wal-link's L4: `osCallPerms_root`) and the root's path. Untrusted.

The fresh files are names `b` of one root `r` of the file system's roots (`(r, j0) ∈ roots`): an
absolute directory the program owns (`Impl.lean`'s environment: no other process changes it), with no
entry at `b` in the durable tree the program starts with (`FsInit`: the tree as on disk).
-/
module

public import Proof.runtime.Start
public import GooseLang.Ext.Fs.TreeShared
public import GooseLang.Ext.Fs.CrashTok
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

section files
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Fresh files from a claim on a directory's names**: the claim on all names of `j0` but `acc`,
split along fresh names `bs` (none of them in `acc`, none present: `h.cur !! b = none`), each with a
share of the root `r`'s call permission (`callKey R r`, wal-link L4) and the path of the root `r` (`j0`'s), is `fileHoldsF (child r b) ∅` of
each name `b`. -/
theorem files_of_claim (R : Roots) (r : GoString) (j0 : Ino) (hr : (r, j0) ∈ R) :
    ∀ (bs acc : List GoString) (h : NamesH) (q : Qp), bs.Nodup → (∀ b ∈ bs, b ∉ acc) →
      (∀ b ∈ bs, NameOk b ∧ PathFits (child r b)) → (∀ b ∈ bs, h.cur !! b = none) →
      ⊢ osInv (L := hG.goose_localGS) -∗ osSharedInv (L := hG.goose_localGS) R -∗
        osNames (L := hG.goose_localGS) j0 (.except acc) (DFrac.own 1) h -∗
        osCallPerm (L := hG.goose_localGS) (callKey R r) q ={⊤}=∗
        [∗list] b ∈ bs, backend.fileHoldsF (GF := GF) (child r b) ∅
  | [], _, _, _, _, _, _, _ => by
    iintro - - - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | b :: bs, acc, h, q, hnd, hacc, hok, hcur => by
    iintro #Hinv #Hsh Hn Hp
    have hb : b ∉ acc := hacc b (List.mem_cons_self ..)
    have hsplit := osNames_split (E := ⊤) (L := hG.goose_localGS) R j0 (.except acc) [b] h
      (fun _ _ => CoPset.mem_full)
    have hin : (NameSet.except acc).inter [b] = .only [b] := by
      simp [NameSet.inter, hb]
    have hdiff : (NameSet.except acc).diff [b] = .except (acc ++ [b]) := rfl
    rw [hin, hdiff] at hsplit
    imod hsplit $$ Hsh Hn with ⟨Hb, Hrest⟩
    rw [← Qp.half_add_half q]
    icases (osCallPerm_split (L := hG.goose_localGS) (callKey R r) q.half q.half).1 $$ Hp with ⟨Hp1, Hp2⟩
    imod osPathS_root (E := ⊤) (L := hG.goose_localGS) R r j0 (DFrac.own 1) hr
      (fun _ _ => CoPset.mem_full) $$ Hsh with Hpath
    have hnd' := List.nodup_cons.1 hnd
    imod files_of_claim R r j0 hr bs (acc ++ [b]) (h.restrict j0 (.except (acc ++ [b])))
      q.half hnd'.2
      (fun b' hb' => by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hacc b' (List.mem_cons_of_mem _ hb'), fun he => hnd'.1 (he ▸ hb')⟩)
      (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => by
        simp only [NamesH.restrict]
        rw [restrictN_lookup]
        · exact hcur b' (List.mem_cons_of_mem _ hb')
        · simp only [NameSet.Mem, List.mem_append, List.mem_singleton, not_or]
          exact ⟨hacc b' (List.mem_cons_of_mem _ hb'), fun he => hnd'.1 (he ▸ hb')⟩)
      $$ Hinv Hsh Hrest Hp2 with Hfs
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hfs
    unfold backend.fileHoldsF
    iexists R, r, b, DFrac.own 1, j0, q.half, h.restrict j0 (.only [b])
    iframe Hinv Hsh Hpath Hp1 Hb
    isplitr
    · ipureintro; exact ⟨rfl, (hok b (List.mem_cons_self ..)).1, (hok b (List.mem_cons_self ..)).2⟩
    unfold bbolt.nameHolds
    iright
    ipureintro
    refine ⟨?_, rfl⟩
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem])]
    exact hcur b (List.mem_cons_self ..)

variable [backend.FsNoErrAll]

/-- **The fresh files at program start** (see the file header): from the file extension's start
resources (`osStart` of an `FsInit` state), at the step of the program `e` (not a value), the
proof of `e` gets `backend.fileHolds (child r b) ∅` for each fresh name `b` of the root `r`. The
program's proof gets nothing else of the tree. -/
theorem start_fileHolds (σ : OsState) (hfs : FsInit σ) (r : GoString) (j0 : Ino)
    (bs : List GoString) (hr : (r, j0) ∈ σ.fs.roots) (hbs : bs.Nodup)
    (hok : ∀ b ∈ bs, NameOk b ∧ PathFits (child r b))
    (habs : ∀ b ∈ bs, σ.fs.treeDur.entry j0 b = none) (e : Expr) (Φ : val → IProp GF) :
    ⊢ osStart (gooseOsGS (L := hG.goose_localGS)) σ -∗
      (([∗list] b ∈ bs, backend.fileHolds (GF := GF) (child r b) ∅) -∗
        WP e @ Stuckness.NotStuck; ⊤ {{ Φ }}) ={⊤}=∗
      WP e @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro Hs Hk
  unfold osStart osStartF treeStart bytesMap metaMap
  icases Hs with ⟨⟨-, -, Hv⟩, Hd⟩
  imod osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imod osSwitchKit_open (L := hG.goose_localGS) σ.fs.roots (σ.fs.treeDur, []) ⊤ $$ Hd with Hsh
  unfold osShared
  icases Hsh with ⟨#Hsh, #-, Hperms, -, Hcl⟩
  icases osCallPerms_root (L := hG.goose_localGS) σ.fs.roots r j0 hfs.2.2.2.1 hr $$ Hperms with ⟨Hperm, -⟩
  -- the root's claim
  have hnow : Hist.now (σ.fs.treeDur, ([] : List LogEntry)) = σ.fs.treeDur := rfl
  have hj0 : j0 ∈ σ.fs.treeDur := hfs.2.2.2.2.1.1 j0 (Reach.root r j0 hr)
  obtain ⟨v0, hv0⟩ := Option.isSome_iff_exists.mp ((GMap.mem_iff _ _).mp hj0)
  have hmem : j0 ∈ (GMap.toList (Hist.now (σ.fs.treeDur, ([] : List LogEntry)))).map (·.1) := by
    rw [hnow]
    exact List.mem_map.mpr ⟨(j0, v0), (GMap.mem_toList _ _ _).mpr hv0, rfl⟩
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hmem
  ihave Hj := BigSepL.bigSepL_lookup (Φ := fun _ j => osNames (L := hG.goose_localGS) j
    (.except []) (DFrac.own 1) (namesOf (σ.fs.treeDur, []) j (.except []))) hk $$ Hcl
  imod files_of_claim (hG := hG) σ.fs.roots r j0 hr bs [] (namesOf (σ.fs.treeDur, []) j0 (.except []))
    1 hbs (fun _ _ h => absurd h List.not_mem_nil) hok
    (fun b hb => by
      simp only [namesOf]
      rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), entsOf_lookup, hnow]
      exact habs b hb) $$ Hinv Hsh Hj Hperm with Hfs
  imodintro
  iapply Hk
  have heq : ∀ p, backend.fileHolds (GF := GF) p ∅ = backend.fileHoldsF p ∅ := fun p => by
    unfold backend.fileHolds; exact backend.onFs_eq _
  simp only [heq]
  iexact Hfs

end files

end EtcdGrove
end Perennial
