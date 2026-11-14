/- Lean-first (no Rocq counterpart).

# `openAtIndex`'s later ghost steps (W3/W5 of `notes/wal-fsext-plan.md`, twelfth session)

At a program step (`wp_notCrashed_acc`), as updates of `walInv` (`walInv_step`):
* `walInv_unpin`: an error arm puts the pinned halves back (`walInvBody_unpin`) and gets the lock
  token back;
* `walInv_mintOpening`: write mode, once the struct `w` exists, the ghost handle `walOpening w dir s`
  minted from the lock token (`walOpening_mint`, with the handles' authority out of `walGhost`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenUnpin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAlloc
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

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

/-- **The pinned halves back** (see the file header). -/
theorem walInv_unpin (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (S : List SegG) (write : Bool)
    (hS : ∀ g ∈ S, g.om.size = g.bs.length) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walLockedTok (W := W) -∗ (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) -∗
      walOutFrag (W := W) ⟨S.map (·.ino), [(j, .except X)], if write then [dir] else []⟩ -∗
      ([∗list] g ∈ S, segRes (L := L) g) -∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      (if write then walTmpsRes (hG := ⟨G, L⟩) j else emp) -∗ walDirKey (W := W) dir j X ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Hl Htf Ho HS Hn Ht #Hk
  iapply walInv_step C Mr R jr r
    iprop(walLockedTok (W := W) ∗ (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
      walOutFrag (W := W) ⟨S.map (·.ino), [(j, .except X)], if write then [dir] else []⟩ ∗
      ([∗list] g ∈ S, segRes (L := L) g) ∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      (if write then walTmpsRes (hG := ⟨G, L⟩) j else emp) ∗ walDirKey (W := W) dir j X)
    (walUnlockedTok (W := W)) ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨Hl, ⟨Htf, Hnf⟩, Ho, HS, Hn, Ht, Hk⟩
      imod walInvBody_unpin C Mr R jr r s dir j X hj S write hS $$ Hb Hl Htf Hnf Ho HS Hn Ht Hk
        with ⟨Hb, Hu⟩
      imodintro
      iframe)
    $$ Hinv Hnc [Hl Htf Ho HS Hn Ht]
  iframe
  iexact Hk

/-- The ghost handle minted from the lock token, on the invariant's contents. -/
theorem walInvBody_mintOpening (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (w : Loc) (dir : GoString) (sn : w64 × w64) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walLockedTok (W := W) ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walOpening (W := W) w dir sn := by
  iintro Hb Hl
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases (walGhost_handleAuth (W := W) s).1 $$ Hg with ⟨Ha, Hg⟩
  imod walOpening_mint (W := W) w dir sn $$ Ha Hl with ⟨Ha, Ho⟩
  ihave Hg := Hg $$ Ha
  imodintro
  iframe Ho
  iexists Ls, cl, n, F
  iframe

/-- **The ghost handle minted** (see the file header). -/
theorem walInv_mintOpening (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walLockedTok (W := W) ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗ walOpening (W := W) w dir sn := by
  iintro #Hinv Hnc Hl
  iapply walInv_step C Mr R jr r (walLockedTok (W := W)) (walOpening (W := W) w dir sn) ⊤
    CoPset.subseteq_top (fun s => by
      iintro Hb Hl
      imod walInvBody_mintOpening C Mr R jr r s w dir sn $$ Hb Hl with ⟨Hb, Ho⟩
      imodintro
      iframe)
    $$ Hinv Hnc Hl

end iris

end WalFs
end EtcdGrove
end Perennial

end
