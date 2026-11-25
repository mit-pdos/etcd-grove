/- Lean-first (no Rocq counterpart).

# The loans of a WAL name, returned (P6b fix A)

A holder of the lock that borrowed fractions of a registered WAL's name claim (`walInv_dirPath`'s paths,
`walNamesRes_lendAt`'s claims) keeps them as `walLoanP` beside the lock's record of them
(`walNamesFragS ⟨none, none, Lo⟩`), and returns them all (`walInv_returnAll`) before it gives the lock token
back, so that the free token finds every name's program half whole (`DiscardUnsaved`'s merge).

* `walLoanP R jr r x`: the loan `x = (nm, q)` held: a path to `r/nm` of fraction `q`, or the claim's.
* `walInvBody_returnName`/`walInv_returnName`: `walNamesRes_returnName` under the invariant.
* `walInv_returnLoan`, `walInv_returnAll`: one loan, every loan.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameClaims
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameSplit

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **A loan held**: the fraction `x.2` of the name `x.1`'s claim, as a path to its directory (`r/x.1`,
`walInv_dirPath`'s) or as the claim itself (`walNamesRes_lendAt`'s). -/
def walLoanP (R : Roots) (jr : Ino) (r : GoString) (x : GoString × Qp) : IProp GF :=
  iprop((∃ j : Ino, osPathS (L := hG.goose_localGS) R (child r x.1) (DFrac.own x.2) j) ∨
    (∃ hn : NamesH, osNames (L := hG.goose_localGS) jr (.only [x.1]) (DFrac.own x.2) hn))

/-- `walNamesRes_returnName` under the invariant's body. -/
theorem walInvBody_returnName (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (nm : GoString) (q : Qp) (hn' : NamesH) (Lo : List (GoString × Qp))
    (hx : (nm, q) ∈ Lo) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗
      walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
      osNames (L := hG.goose_localGS) jr (.only [nm]) (DFrac.own q) hn' ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗
        walNamesFragS (W := W) ⟨none, none, Lo.erase (nm, q)⟩ := by
  iintro Hb Hf Hn
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    Hdk, %HAt, Hnms, Hbd⟩
  imod walNamesRes_returnName R jr r Ls nm q hn' Lo hx $$ Hnms Hf Hn with ⟨Hnms, Hf⟩
  imodintro
  iframe Hf
  iexists Ls, cl, n, F
  iframe
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  ipureintro; exact HAt

/-- **One loan returned, at a program step** (`notCrashed`). -/
theorem walInv_returnLoan (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (x : GoString × Qp) (Lo : List (GoString × Qp)) (hx : x ∈ Lo) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
      walLoanP R jr r x ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
        walNamesFragS (W := W) ⟨none, none, Lo.erase x⟩ := by
  iintro #Hinv Hnc Hf Hx
  obtain ⟨nm, q⟩ := x
  unfold walLoanP
  icases Hx with (⟨%j, Hp⟩ | ⟨%hn, Hn⟩)
  · iapply walInv_dirPathRet C Mr R jr r nm q j Lo hx $$ Hinv Hnc Hf Hp
  · imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
      with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
    imod walInvBody_returnName C Mr R jr r s nm q hn Lo hx $$ Hb Hf Hn with ⟨Hb, Hf⟩
    imod Hcl $$ [Hb] with -
    · iexists s; iexact Hb
    imodintro
    iframe

/-- **Every loan returned**: the lock holder's record back to no loan out (`walNamesFrag none`). -/
theorem walInv_returnAll (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (Lh : List (GoString × Qp)) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walNamesFragS (W := W) ⟨none, none, Lh⟩ -∗
      ([∗list] x ∈ Lh, walLoanP R jr r x) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walNamesFrag (W := W) none := by
  induction Lh with
  | nil =>
    iintro #Hinv Hnc Hf -
    imodintro
    iframe
  | cons x t ih =>
    iintro #Hinv Hnc Hf Hl
    icases Hl with ⟨Hx, Hl⟩
    imod walInv_returnLoan C Mr R jr r x (x :: t) List.mem_cons_self $$ Hinv Hnc Hf Hx with ⟨Hnc, Hf⟩
    simp only [List.erase_cons_head]
    iapply ih $$ Hinv Hnc Hf Hl

end iris

end WalFs
end EtcdGrove
end Perennial

end
