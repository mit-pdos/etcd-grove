/- Lean-first (no Rocq counterpart).

# A step on a pipeline name under the WAL invariant (step 2 (B) of `notes/wal-units/tester.md`)

The claim on a pipeline name `b` (`0.tmp`, `1.tmp`) of a WAL directory `j` is split: the program's
three quarters (`tmpClaim`, `qTmp`), the invariant's quarter (`tmpHalf`, `qTmpI`, in `walTmpParked`'s
`walTmpHalves`), which keeps the fact that no version a crash may leave holds a directory there
(`HistFoP`). A step on the name (the pipeline's create, its removes, the cut's rename) needs the whole
claim, so it opens the invariant:

* `walInvBody_tmpAcc`: the invariant's quarter of `(j, b)`, out of the invariant's contents and back,
  found by the WAL's key (`walDirKey dir j X`: `DirKeysOk` gives the layout of `dir`, of directory `j`);
* `walTmp_osAUnc`: the atomic update a shared `os` spec takes for a step on `b` by a caller giving the
  call half the claim (`walTmpP`: the program's last quarter stays in the update, to agree with the
  invariant's at the opening; the update holds the other half). The outcome `β` at half splits into
  the invariant's quarter at the new history `hn o` and the caller's quarter (`hsplit`); the new history
  keeps the fact (`hfo`: the step leaves no directory at `b`, `HistFoP.log`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpClaim

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A WAL's pipeline name's invariant quarter, out of the parked resources and back** (the cut's
rename, inside the invariant's update). -/
theorem walParked_tmpAcc (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (dir : GoString) (lay : WalLay) (hl : Ls !! dir = some lay) (j : Ino) (hj : lay.j = j)
    (b : GoString) (hb : b ∈ walTmps) :
    walParked (L := L) (W := W) Ls cl F ⊢
      tmpHalf (hG := ⟨G, L⟩) j b ∗
        (tmpHalf (hG := ⟨G, L⟩) j b -∗ walParked (L := L) (W := W) Ls cl F) := by
  subst hj
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb', Hs, Hc, Ht, Hw⟩
  ihave ⟨Hh, Ht⟩ := walTmpParked_acc (G := G) (L := L) Ls o'.T dir lay hl b hb $$ Ht
  iframe Hh
  iintro Hh
  ihave Ht := Ht $$ Hh
  iexists bf, o'
  iframe Ha Hoa Hs Hc Ht Hw
  ipureintro; exact hb'

/-- **The invariant's half of a keyed WAL directory's pipeline name, out of its contents and back**
(the pipeline's key, current by its eighth of the incarnations, kept). -/
theorem walInvBody_tmpAcc (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (b : GoString)
    (hb : b ∈ walTmps) :
    ⊢ walPipeKey (W := W) dir j -∗ walInvBody (L := L) (W := W) C Mr R jr r s -∗
      walPipeKey (W := W) dir j ∗ tmpHalf (hG := ⟨G, L⟩) j b ∗
        (tmpHalf (hG := ⟨G, L⟩) j b -∗ walInvBody (L := L) (W := W) C Mr R jr r s) := by
  iintro Hkey Hb
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, Hcra,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walPipeKey_lookup K dir j $$ Hdk Hkey with %HK
  obtain ⟨X, HK⟩ := HK
  obtain ⟨lay, -, hl, hlj, -⟩ := Hdko.1 dir j X HK
  subst hlj
  unfold walParked
  icases Hpk with ⟨%bf, %o', Ha, Hoa, %hb', Hs, Hc, Ht, Hw⟩
  ihave ⟨Hh, Ht⟩ := walTmpParked_acc (G := G) (L := L) Ls o'.T dir lay hl b hb $$ Ht
  iframe Hh Hkey
  iintro Hh
  ihave Ht := Ht $$ Hh
  iexists Ls, cl, n, F
  iframe Hg Hcl0 Hcm Hlays Hcra Htl Hnms
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact Hok
  isplitr
  · ipureintro; exact Hco
  isplitr
  · ipureintro; exact Han
  isplitr
  · ipureintro; exact Hnm
  isplitl [Ha Hoa Hs Hc Ht Hw]
  · iexists bf, o'
    iframe Ha Hoa Hs Hc Ht Hw
    ipureintro; exact hb'
  isplitl [Hdk Hcp]
  · iexists K, cp
    iframe Hdk Hcp
    ipureintro; exact Hdko
  ipureintro; exact ⟨HAt, Hbd⟩

end iris

section au0
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- Half a claim, as two quarters. -/
theorem osNames_halfQ (j : Ino) (N : NameSet) (h : NamesH) :
    osNames (L := L) j N (DFrac.own (1 : Qp).half) h ⊣⊢
      osNames (L := L) j N (DFrac.own (1 : Qp).half.half) h ∗ osNames (L := L) j N (DFrac.own (1 : Qp).half.half) h := by
  have e := osNames_frac (L := L) j N (1 : Qp).half.half (1 : Qp).half.half h
  rw [Qp.half_add_half] at e
  exact e

end au0

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **What the caller of a step on a pipeline name keeps in the update**: the pipeline's key (with its
eighth of the incarnations, `walPipeKey`) and a quarter of the claim (the call gets the program's other
half). -/
def walTmpP (dir : GoString) (j : Ino) (b : GoString) (h : NamesH) : IProp GF :=
  iprop(walPipeKey (W := W) dir j ∗ osNames j (.only [b]) (DFrac.own (1 : Qp).half.half) h)

/-- **The update for a step on the pipeline name `b` of a keyed WAL directory** (see the file
header). -/
theorem walTmp_osAUnc {A : Type} (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (dir : GoString) (j : Ino) (b : GoString) (hb : b ∈ walTmps)
    (h : NamesH) (β : DFrac → A → IProp GF) (hn : A → NamesH)
    (hsplit : ∀ o, β (DFrac.own (1 : Qp).half) o ⊢
      osNames j (.only [b]) (DFrac.own qTmpI) (hn o) ∗ β (DFrac.own (1 : Qp).half.half) o)
    (hfo : ∀ o n0, HistFoP (fun _ => True) n0 j (.only [b]) h →
      HistFoP (fun _ => True) n0 j (.only [b]) (hn o)) :
    ⊢ walInv (W := W) C Mr R jr r -∗ walTmpP (W := W) dir j b h -∗
      osAUnc (osNames j (.only [b]) (DFrac.own (1 : Qp).half) h)
        (β (DFrac.own (1 : Qp).half))
        (fun o => iprop(β (DFrac.own (1 : Qp).half.half) o ∗ walPipeKey (W := W) dir j)) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (walTmpP (W := W) dir j b h) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open C Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  icases Hb with ⟨%s, Hb⟩
  unfold walTmpP
  icases HP with ⟨Hkey, Hq⟩
  ihave ⟨Hkey, Hh, Hbcl⟩ := walInvBody_tmpAcc C Mr R jr r s dir j b hb $$ Hkey Hb
  unfold tmpHalf
  icases Hh with ⟨%h1, %n0, Hα, #Hn0, %hf⟩
  icases osNames_agree j (.only [b]) _ _ h1 h $$ Hα Hq with %e
  subst e
  ihave Hw := (osNames_halfQ (L := hG.goose_localGS) j (.only [b]) h1).2 $$ [Hα Hq]
  · iframe Hα Hq
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ osAuMask \ ↑walN from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  iframe Hw Hnc
  isplit
  · -- abort
    iintro Hw
    icases (osNames_halfQ (L := hG.goose_localGS) j (.only [b]) h1).1 $$ Hw with ⟨Hα, Hq⟩
    imod Hcl'
    imod Hcl $$ [Hbcl Hα]
    · iexists s
      iapply Hbcl
      iexists h1, n0
      iframe Hα Hn0
      ipureintro; exact hf
    imodintro
    dsimp only
    iframe Hkey Hq
  · iintro %o Hβ
    ihave ⟨Hα, Hq⟩ := hsplit o $$ Hβ
    imod Hcl'
    imod Hcl $$ [Hbcl Hα]
    · iexists s
      iapply Hbcl
      iexists hn o, n0
      iframe Hα Hn0
      ipureintro; exact hfo o n0 hf
    imodintro
    dsimp only
    iframe Hq Hkey

end au

end WalFs
end EtcdGrove
end Perennial

end
