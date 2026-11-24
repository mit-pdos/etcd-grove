/-
Lean-first (no Rocq counterpart).

# The WAL tester's boot after a crash (W4c U5, `notes/wal-fsext-w4c-plan.md`)

* `TCrashed e V`: what the tester's crash obligation (`tester_crash`, `Crash.lean`) hands the new
  generation besides its tree's shared view (`osShared … V`): the WAL's
  start over the crashed tree (`walStart`, the boot files, the lock and crash tokens, from
  `walInv_crash`), the ghost WAL state `od` the new generation's program map holds (`walDirIs`) and
  the oracle `o` it accounts for (`tRelI`, from the `_keep` lemmas: `walSyncedLb`/`walNamed` of the
  new generation), the area's durability, the oracle file as the crash left it (`durFound`,
  `durFoundTmp`, from `durInv_crash`) holding `o` (`tOracleFile ⟨v, none⟩ o none`), and the pure facts
  `walBootCrash` needs of the crashed tree and state. `BootFo V.now e.jr` is carried as a fact,
  from `walInv_crash` (`bootFo_of`; until 2026-11-22 in part `tester_crash`'s premise `BootFoNmTmp`).
* `tBootCrash`: from `TCrashed e V` and `osShared … V` (the shared invariant, the whole call
  permission, every directory's whole claim), the incarnation's `TBoot e`, as `tBoot0` does for the
  first: the WAL's area by `walBootCrash`, the oracle file's by durable's `durBoot` on the oracle
  directory's claim (among `walBootCrash`'s `bootRest`: `mem_bootRest_root`), the tester's ghost
  variables and invariant allocated over `o` and `od`, nothing pending.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Boot0
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 Fs WalFs

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **What the crash obligation hands the new generation** (`L`, its first tree `V`), besides the
tree itself: see the file header. -/
def TCrashed (e : TEnv) (V : Hist) : IProp GF :=
  iprop(∃ (W : WalGS GF) (s : AbsDiskState) (o : TOracle) (od : Option WalDur) (v : Option GoString),
    ⌜W.roots = e.R ∧ V.2 = [] ∧ WalsBounded s ∧ DirsRoots e.R s ∧ TreeWf e.R V.now ∧ BootFo V.now e.jr ∧
      tOracleFile ⟨v, none⟩ o none⌝ ∗
    walStart L W walCodec walRaftMr e.R e.jr (e.area) s V.now ∗
    ([∗list] i ∈ bootFiles V.now e.jr, trFile (hG := ⟨G, L⟩) i False) ∗
    WalFs.walUnlockedTok (W := W) ∗ WalFs.walCrashTok (W := W) ∗
    WalFs.walDirIs (W := W) (tWalDir e.area) od ∗ tRelI (W := W) e.area o od ∗
    WalFs.dirDurable (W := W) (e.area) ∗
    DurFs.durFound (L := L) e.orFile V.now v ∗ DurFs.durFoundTmp (L := L) e.orFile V.now)

end boot

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **The tester's boot after a crash** (see the file header). World premises, as `tBoot0`'s (U7):
the roots well formed, the area and the oracle directory two distinct roots, the receipts' bound. -/
theorem tBootCrash (L : GooseLocalGS GF) (e : TEnv) (V : Hist) (hR : RootsOk e.R)
    (hr : (e.area, e.jr) ∈ e.R) (ho : (e.orDir, e.jo) ∈ e.R) (hne : e.jo ≠ e.jr)
    (hrb : ReceiptBoundLe GF (2 ^ 62)) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ TCrashed (L := L) e V -∗ osInv (L := L) -∗ osSharedInv (L := L) e.R -∗ osAboveInv (L := L) -∗
      osCallPerms (L := L) e.R -∗
      ([∗list] j ∈ (GMap.toList V.now).map (·.1),
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E}=∗
      TBoot (L := L) e := by
  iintro Hc #Hos #Hsh #Hab Hcps Hall
  ihave Hcp := tPerm_of_osCallPerms e hR hr ho hne $$ Hcps
  unfold TCrashed
  icases Hc with ⟨%W, %s, %o, %od, %v, %hp, Hst, Hbf, Hu, Hct, Hw, #Hrel, #Hdd, Hdf, Hdt⟩
  obtain ⟨hWR, hV, hbd, hdr, hwf, hfo, hof⟩ := hp
  -- the WAL's area
  imod walBootCrash walCodec walCodec_ok walRaftMr L W e.R e.jr (e.area) s V hV hR hr hwf
    hbd hdr hfo hrb walRaftMr_encState_lt hWR E hE $$ Hos Hsh Hab Hst Hbf Hall with ⟨#Hok, Hres, -, Hrest⟩
  -- the oracle directory's claim, and durable's boot
  ihave Hjo := claims_take L V _ e.jo (mem_bootRest_root hwf hr ho hne) $$ Hrest
  have hd := DurFs.durBoot L e.orFile e.R V v E hV ho hE
  rw [show e.orFile.J = e.jo from rfl] at hd
  imod hd $$ Hsh Hjo Hdf Hdt with ⟨%γd, #Hdi, Hdh, Hds, Hdc⟩
  -- the tester's ghost variables and invariant
  imod ghostVar_alloc (GF := GF) ((o, none) : TOracle × Option TOracle) with ⟨%γo, Ho⟩
  icases (ghostVar_split_half (GF := GF) γo 1 ((o, none) : TOracle × Option TOracle)).1 $$ Ho
    with ⟨Ho1, Ho2⟩
  imod ghostVar_alloc (GF := GF) od with ⟨%γw, Hw'⟩
  icases (ghostVar_split_half (GF := GF) γw 1 od).1 $$ Hw' with ⟨Hw1, Hw2⟩
  let γ : TGS := ⟨γd, γo, γw⟩
  imod inv_alloc tN E (TInvBody (GF := GF) (W := W) e γ) $$ [Hds Ho1 Hw1 Hw] with #Hinv
  · inext
    unfold TInvBody
    iexists ⟨v, none⟩, o, none, od
    iframe Hds Ho1 Hw1 Hw Hrel
    isplitr
    · ipureintro; exact hof
    · unfold tRelA; iempintro
  imodintro
  unfold TBoot
  iexists W, γ, o, od
  unfold tOrOwn tWalOwn TInv
  iframe Hinv Ho2 Hw2 Hok Hdd Hres Hu Hdi Hdh Hcp Hct Hdc

end boot

end etcd_wal
end EtcdGrove
end Perennial
