/-
Lean-first (no Rocq counterpart).

# The WAL tester's first boot (W4c U5, `notes/wal-fsext-w4c-plan.md`)

`tBoot0`: from the tree's shared view at the first start (`osShared`, `fs_startS`: the shared invariant,
the whole call permission, a whole claim on all names of every directory of the boot tree `V.now`,
nothing logged), the first incarnation's `TBoot`: the WAL's area by `walBoot0` (U3) and the oracle
file's by durable's first boot (`DurBoot0`, proved by U2's `DurFs.durBoot0`: `durBoot0_holds`), the tester's invariant allocated over the fresh oracle and no WAL.

The world premises (each the closed theorem's, U7): the roots well formed; the area `e.area` and the
oracle directory `e.orDir` two distinct roots; no entry of the area at a WAL function's name
(`walBoot0`'s `hslots`: no WAL found); no oracle file and no temporary of it; the receipts' bound.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Inv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Boot0
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Boot

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
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **Durable's first boot** (the statement the tester needs; `durBoot0_holds`): at the shared mode's
switch, from the whole claim on the file's directory (a root, holding neither the file nor its
temporary), fresh ghost names, the invariant and the handle, the client's half of the state (no file,
nothing pending) and the crash token. -/
def DurBoot0 : Prop :=
  ∀ (L : GooseLocalGS GF) (f : DurFs.DFile) (R : Roots) (V : Hist) (E : CoPset),
    f.Ok → V.2 = [] → (f.d, f.J) ∈ R → V.now.entry f.J f.b = none → V.now.entry f.J f.tb = none →
    ↑osShN ⊆ E →
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗
      osNames (L := L) f.J (.except []) (DFrac.own 1) (namesOf V f.J (.except [])) ={E}=∗
      ∃ γ : DurFs.DurGS, DurFs.durInv (L := L) γ f ∗ DurFs.durHandle (L := L) γ f R ∗
        DurFs.durSt (GF := GF) γ ⟨none, none⟩ ∗ DurFs.durCrashTok (GF := GF) γ

theorem durBoot0_holds : DurBoot0 (GF := GF) :=
  fun L f R V E hf hV hR hb ht hE => DurFs.durBoot0 L f R V E hf hV hR hb ht hE

/-- An element of the boot tree's directory list, out of the list. -/
theorem claims_take (L : GooseLocalGS GF) (V : Hist) (js : List Ino) (j : Ino) (hj : j ∈ js) :
    ⊢@{IProp GF} ([∗list] j ∈ js, osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) -∗
      osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except [])) := by
  iintro Hall
  ihave Hall := (BigSepL.bigSepL_perm (Φ := fun j => osNames (L := L) j (.except []) (DFrac.own 1)
    (namesOf V j (.except []))) (List.perm_cons_erase hj)).1 $$ Hall
  icases Hall with ⟨Hj, -⟩
  iexact Hj

/-- The area is durable at the first boot. -/
theorem dirDurable_boot0 [W : WalGS GF] (r : GoString) :
    ⊢@{IProp GF} WalFs.walPast (W := W) (walBoot0St r) -∗ WalFs.dirDurable (W := W) r := by
  iintro #Hp
  unfold WalFs.dirDurable
  iexists walBoot0St r
  iframe Hp
  ipureintro
  simp [walBoot0St]

/-- **The tester's first boot** (see the file header). -/
theorem tBoot0 (hPre : AbsDiskGpreS GF) (L : GooseLocalGS GF)
    (e : TEnv) (V : Hist) (hV : V.2 = []) (hR : RootsOk e.R) (hr : (e.area, e.jr) ∈ e.R)
    (hjr : e.jr ∈ V.now) (hslots : ∀ b, AreaSlot b → V.now.entry e.jr b = none)
    (ho : (e.orDir, e.jo) ∈ e.R) (hjo : e.jo ∈ V.now) (hne : e.jo ≠ e.jr)
    (hob : V.now.entry e.jo e.orFile.b = none) (hot : V.now.entry e.jo e.orFile.tb = none)
    (hf : e.orFile.Ok) (hrb : ReceiptBoundLe GF (2 ^ 62)) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) e.R -∗ osAboveInv (L := L) -∗ osCallPerms (L := L) e.R -∗
      ([∗list] j ∈ (GMap.toList V.now).map (·.1),
        osNames (L := L) j (.except []) (DFrac.own 1) (namesOf V j (.except []))) ={E}=∗
      TBoot (L := L) e := by
  iintro #Hos #Hsh #Hab Hcps Hall
  ihave Hcp := tPerm_of_osCallPerms e hR hr ho hne $$ Hcps
  -- the WAL's area
  have hjrm : e.jr ∈ (GMap.toList V.now).map (·.1) := by
    cases he : V.now !! e.jr with
    | none => have := (GMap.mem_iff _ _).1 hjr; rw [he] at this; cases this
    | some x => exact List.mem_map.2 ⟨(e.jr, x), (GMap.mem_toList _ _ _).2 he, rfl⟩
  imod walBoot0 hPre walCodec walCodec_ok walRaftMr L e.R e.jr (e.area) V hV hR hr _ hjrm hslots
    hrb walRaftMr_encState_lt E hE $$ Hos Hsh Hab Hall
    with ⟨%W, #Hok, Hres, Hu, Hc, #Hp, Hown, -, Hrest⟩
  ihave #Hdd := dirDurable_boot0 (W := W) (e.area) $$ Hp
  -- the oracle directory's claim, and durable's boot
  have hmem : e.jo ∈ ((GMap.toList V.now).map (·.1)).erase e.jr := by
    have h1 : e.jo ∈ (GMap.toList V.now).map (·.1) := by
      cases he : V.now !! e.jo with
      | none => have := (GMap.mem_iff _ _).1 hjo; rw [he] at this; cases this
      | some x => exact List.mem_map.2 ⟨(e.jo, x), (GMap.mem_toList _ _ _).2 he, rfl⟩
    exact (List.mem_erase_of_ne hne).2 h1
  ihave Hjo := claims_take L V _ e.jo hmem $$ Hrest
  have hd := durBoot0_holds (GF := GF) L e.orFile e.R V E hf hV ho hob hot hE
  rw [show e.orFile.J = e.jo from rfl] at hd
  imod hd $$ Hos Hsh Hjo with ⟨%γd, #Hdi, Hdh, Hds, Hdc⟩
  -- the tester's ghost variables and invariant
  imod ghostVar_alloc (GF := GF) ((tFreshOracle, none) : TOracle × Option TOracle) with ⟨%γo, Ho⟩
  icases (ghostVar_split_half (GF := GF) γo 1 ((tFreshOracle, none) : TOracle × Option TOracle)).1 $$ Ho
    with ⟨Ho1, Ho2⟩
  imod ghostVar_alloc (GF := GF) (none : Option WalDur) with ⟨%γw, Hw⟩
  icases (ghostVar_split_half (GF := GF) γw 1 (none : Option WalDur)).1 $$ Hw with ⟨Hw1, Hw2⟩
  let γ : TGS := ⟨γd, γo, γw⟩
  imod inv_alloc tN E (TInvBody (GF := GF) (W := W) e γ) $$ [Hds Ho1 Hw1 Hown] with #Hinv
  · inext
    unfold TInvBody
    iexists ⟨none, none⟩, tFreshOracle, none, none
    iframe Hds Ho1 Hw1
    isplitr
    · ipureintro; exact tOracleFile_fresh
    isplitl [Hown]
    · unfold WalFs.walDirIs
      iexists ∅
      iframe Hown
      ipureintro
      show walOptLe none ((∅ : GMap GoString WalDur) !! tWalDir e.area)
      rw [GMap.lookup_empty]; trivial
    isplitr
    · unfold tRelI
      simp only [tFreshOracle, Bool.false_eq_true, ite_false]
      ipureintro; exact ⟨rfl, Or.inl rfl⟩
    · unfold tRelA; iempintro
  imodintro
  unfold TBoot
  iexists W, γ, tFreshOracle, none
  unfold tOrOwn tWalOwn TInv
  iframe Hinv Ho2 Hw2 Hok Hdd Hres Hu Hdi Hdh Hcp Hc Hdc

end boot

end etcd_wal
end EtcdGrove
end Perennial
