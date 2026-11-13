/- Lean-first (no Rocq counterpart).

# `cut`'s client update at the rename (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

`walCut_osAUnc`: the atomic update `cut` gives `os.Rename.specFileSnc` for the rename of the
pipeline's `tmp` (its claim `(j, .only [tmp], ht)`, the program's) onto the free `.wal` name `bt` of
the WAL directory `j` (the claim `(j, .except X, hj)`, the program's half and the invariant's, the
key `walDirKey dir j X`). The program keeps a quarter of its half of the WAL claim in the update
(`walCutP`), to agree with the invariant's at the opening; the call gets the other quarter.

* *Opening* (with the generation's `notCrashed`): opens `walInv`, finds the key's claim (`DirKeysOk`:
  once among the invariant's), agrees with the program's, hands out the invariant's half with the
  quarter.
* *Abort*, or a commit with no effect: closed again; the program's resources back.
* *Commit* (the rename logged at `x` by a call begun at `s0`): the WAL state is unchanged; no cut is
  pending (`walCut_agree`), and the flag goes to `some dir` (`walCut_set`); the tail record gives the
  WAL `d`, its layout `lay` and old tail `g0` (`walTailsRes_cut`), which the program's copy matches
  (`H`, the metadata, the cuts, the old tail's inode); the old tail's halves agree with the
  program's (synced and truncated: its bytes the stream's, durable); the new segment's inode is no
  layout's (`laysResF_ino_ne`). The invariant takes half of the new claim, the new segment's
  halves (`laysResF_cut`), the layout `cutLay lay |H| g wr` (`cutCommit_pure`), the tail record moved
  to the new segment (`tailG_cut`, `tailZeros_cut`, `tailBound_cut`), the old tail's program halves
  deposited and the new segment and claim out of `walParked` (`walParked_cut`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutAuLemmas
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The tail's stream with a cut at the end, as the layout's. -/
theorem tailStream_cut (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    tailStream Mr d.H d.metadata (cuts ++ [d.H.length]) =
      segStream walCodec Mr d (cuts ++ [d.H.length]) (cuts.length + 1) := by
  rw [tailStream_eq]; simp

end pure

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- A quarter. -/
abbrev qQuarter : Qp := (1 : Qp).half.half

/-- **What `cut` holds for the rename's update**: the directory's key, the tail's key and the
program's half of the tail record (history `H`, metadata `md`, cuts, write position `wr0`, old tail
`i0`), a quarter of the WAL claim (the call has another), half of the pipeline file's claim (the call
has the other), the parking flag (`false`) and the pending-cut flag (`none`), the program's halves
of the old tail, the new segment `g` whole, and the facts that the history is synced and the WAL
named. -/
def walCutP (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (tmp : GoString)
    (ht : NamesH) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr0 : Nat) (i0 : Ino) (m0 : OsMeta) (bs0 : List ByteG) (g : SegG) : IProp GF :=
  iprop(walDirKey (W := W) dir j X ∗ walTailKey (W := W) dir γ ∗
    tailVar (W := W) γ ((H, md, cuts, wr0, i0, none) : TailG) ∗
    osNames j (.except X) (DFrac.own qQuarter) hj ∗ osNames j (.only [tmp]) (DFrac.own (1 : Qp).half) ht ∗
    walParkFrag (W := W) false ∗ walCutFrag (W := W) none ∗
    osMeta i0 (DFrac.own (1 : Qp).half) m0 ∗ osBytes i0 0 (DFrac.own (1 : Qp).half) bs0 ∗
    osMeta g.ino (DFrac.own 1) g.om ∗ osBytes g.ino 0 (DFrac.own 1) g.bs ∗
    walSyncedLb (W := W) dir H.length ∗ walNamed (W := W) dir)

/-- **What `cut` gets from the rename's update**: with no effect, what it held; after the commit
(logged at `x` by a call begun at `s0`), the claims' new histories (half of the pipeline's, a
quarter of the WAL's), the keys, the tail record at the new segment (the cut at `|H|`, written up to
`wr`), the flags (a cut pending in `dir`), the new segment's other halves. -/
def walCutQ (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (tmp : GoString)
    (ht : NamesH) (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr0 : Nat) (i0 : Ino) (m0 : OsMeta) (bs0 : List ByteG) (g : SegG) (bt : GoString) (wr : Nat) :
    Option (Nat × Nat) → IProp GF
  | none => walCutP (W := W) dir j X hj tmp ht γ H md cuts wr0 i0 m0 bs0 g
  | some (x, s0) => iprop(
      osNames j (.only [tmp]) (DFrac.own (1 : Qp).half)
        (ht.log x (renFileEnt j tmp j bt g.ino hj s0) (GMap.delete tmp ht.cur)) ∗
      osNames j (.except X) (DFrac.own qQuarter) (cutClaim j X hj tmp bt g.ino x s0).2.2 ∗
      walDirKey (W := W) dir j X ∗ walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ ((H, md, cuts ++ [H.length], wr, g.ino, none) : TailG) ∗
      walParkFrag (W := W) false ∗ walCutFrag (W := W) (some dir) ∗
      osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- **`cut`'s update for `os.Rename.specFileSnc`** (see the file header). The program's premises, over
its copy of the WAL (`H`, `md`, `cuts`): `tmp` one of the claim's left-out names; the cuts below
`|H|`; the old tail at the `.wal` name `nm0`; `bt` free, a `.wal` name past `nm0` with an index past
the history's; the old tail's bytes the stream's, durable, as many as its size; the new segment's
bytes its headers' frames (`wr` bytes) then zeros, durable, its `OsMeta` sized to them, named `bt`. -/
theorem walCut_osAUnc (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (tmp : GoString) (ht : NamesH)
    (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (wr0 : Nat) (i0 : Ino)
    (m0 : OsMeta) (bs0 : List ByteG) (g : SegG) (bt nm0 : GoString) (wr sq ix : Nat)
    (htmpX : tmp ∈ X) (hcuts : ∀ b ∈ cuts, b < H.length)
    (hnm0 : walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file i0))
    (hbt : bt = walFileName sq ix ∧ walLastIdx (H.map WalOpG.toM) + 1 ≤ ix ∧ go.GoStringLt nm0 bt)
    (hbtw : walNameP bt = true) (hcur : hj.cur !! bt = none)
    (hbs0 : bs0 = (tailStream Mr H md cuts).map durB ∧ bs0.length = m0.size)
    (hwr : wr = (tailStream Mr H md (cuts ++ [H.length])).length)
    (hbs : g.bs = (tailStream Mr H md (cuts ++ [H.length]) ++
      List.replicate (g.bs.length - wr) 0).map durB ∧ wr ≤ g.bs.length)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hfit : RecsFit walCodec (recsOfSegs walCodec Mr md (segsOf (H.map WalOpG.toM) (cuts ++ [H.length]))))
    (hz : g.bs.length - wr = 0 ∨ 8 ≤ g.bs.length - wr) (hgname : g.name = bt) (hgbs : g.bs ≠ []) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗
      walCutP (W := W) dir j X hj tmp ht γ H md cuts wr0 i0 m0 bs0 g -∗
      osAUnc iprop(osNames j (.only [tmp]) (DFrac.own (1 : Qp).half) ht ∗
          osNames j (.except X) (DFrac.own ((1 : Qp).half + qQuarter)) hj)
        (renFileOut j j g.ino (.only [tmp]) (.except X) tmp bt ht hj (DFrac.own (1 : Qp).half)
          (DFrac.own ((1 : Qp).half + qQuarter)))
        (walCutQ (W := W) dir j X hj tmp ht γ H md cuts wr0 i0 m0 bs0 g bt wr) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (walCutP (W := W) dir j X hj tmp ht γ H md cuts wr0 i0 m0 bs0 g) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold walCutP
  icases HP with ⟨#Hkey, Hk, Hv, Hq, Ht, Hpf, Hcf, Hm0, Hb0, Hmg, Hbg, #Hsy, #Hnd⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hkey with %HK
  obtain ⟨lay1, hj1, hl1, hj1j, hjjr, hXw, honce, hcoh, hexcl⟩ := Hdko.1 dir j X HK
  obtain ⟨l1, l2, hcl, hn1, hn2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  icases osNames_agree j (.except X) _ _ hj1 hj $$ Hα Hq with %Hhj
  subst Hhj
  ihave Hw := (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).2 $$ [Hα Hq]
  · iframe Hα Hq
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  isplitl [Ht Hw]
  · iframe Ht Hw
  iframe Hnc
  isplit
  · -- abort
    iintro ⟨Ht, Hw⟩
    icases (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).1 $$ Hw with ⟨Hα, Hq⟩
    imod Hcl'
    imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp]
    · iexists s
      iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
      iframe Hg Hcm Hlays Htl Hpk
      isplitr
      · ipureintro; exact Har
      isplitl [Hl1 Hα Hl2]
      · iapply (osClaims_split _ _ _ _).2
        iframe Hl1 Hα Hl2
      isplitr
      · ipureintro; exact Hok
      isplitr
      · ipureintro; exact Hco
      isplitl [Hcra]
      · iexists CR
        iframe Hcra
        ipureintro; exact Hcro
      isplitr
      · ipureintro; exact Han
      isplitr
      · ipureintro; exact Hnm
      iexists K, cp
      iframe Hdk Hcp
      ipureintro; exact Hdko
    imodintro
    dsimp only
    iframe Hkey Hk Hv Hq Ht Hpf Hcf Hm0 Hb0 Hmg Hbg Hsy Hnd
  · iintro %o Hβ
    rcases o with _ | ⟨x, s0⟩
    · -- no effect: as the abort
      unfold renFileOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Ht, Hw⟩
      icases (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).1 $$ Hw with ⟨Hα, Hq⟩
      imod Hcl'
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp]
      · iexists s
        iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
        iframe Hg Hcm Hlays Htl Hpk
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hα Hl2]
        · iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hα Hl2
        isplitr
        · ipureintro; exact Hok
        isplitr
        · ipureintro; exact Hco
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; exact Hcro
        isplitr
        · ipureintro; exact Han
        isplitr
        · ipureintro; exact Hnm
        iexists K, cp
        iframe Hdk Hcp
        ipureintro; exact Hdko
      imodintro
      dsimp only [walCutQ, walCutP]
      iframe Hkey Hk Hv Hq Ht Hpf Hcf Hm0 Hb0 Hmg Hbg Hsy Hnd
    · imod Hcl'
      sorry

end au

end WalFs
end EtcdGrove
end Perennial

end
