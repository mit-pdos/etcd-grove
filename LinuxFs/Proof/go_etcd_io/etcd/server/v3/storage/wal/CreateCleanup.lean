/- Lean-first (no Rocq counterpart).

# `Create`'s cleanup after its commit (W4, `notes/wal-units/create.md`)

`Create`'s deferred `cleanupWAL` (`WAL.cleanupWAL.spec`) runs on its three error exits after the
commit (the parent's `OpenDir`, `Fsync` or `Close` failed). Its frame (`createFr`) is what `Create`
holds of the area past the commit: the area's path, the program's half of the area claim less
`nm.tmp` and `nm`, its fraction `c` of the program's half of `nm`'s claim (the rest is in the two
pinned paths `Close` returns), the area's tagged claims and the split names. Its outcome when the
rename was called (`createFin`): the area's path, the call permission, the tail lock's closed file, and
the area less `nm.tmp` (`createAreaL`), from which, with `nm.tmp`'s claim merged back, `walAreaRes`
(`create_cleanBack`).

* `create_cleanupLaw`: the rename's law (`cleanupLaw`): `nm`'s claim merged back into the area
  claim (the program's half whole again from the pinned paths: `os.osPathS_unchild` twice,
  `walInv_merge2`), the rename in it, the invariant's half of it through the update; `createFin` after
  any outcome. **`sorry`**: the update cannot be built over the invariant as it is (W4 log, this unit's
  session 3, `notes/wal-units/create.md`): its opening runs inside the `os` step, with the shared
  invariant's namespace already open (`osAuMask` excludes `osShN`), so it cannot find the invariant's
  half of the area claim through `osClaims_keys` as the program's steps do; `Create`'s commit found its
  claim through the creating map (`CreatingOk`), which has no entry for the area claim. And a rename
  that took effect needs the moved-aside step (`WalsAt`'s exception, the pending WAL known unnamed,
  `walAreaRes`'s exception for the broken name). Both are invariant changes, left as a design.
* `create_cleanBack`: **`sorry`** with it (`createAreaL` is to carry what the outcome left of the area
  claim; its pure facts depend on that design).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cleanupWAL
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAreaBack

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
variable [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The free lock token less its names fragment excludes a free one (both hold the lock's token). -/
theorem walUnlockedTokX_unlocked_excl :
    ⊢@{IProp GF} walUnlockedTokX (W := W) -∗ walUnlockedTok (W := W) -∗ False := by
  unfold walUnlockedTokX walUnlockedTok
  letI := walAllG (W := W)
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply token_exclusive $$ H1 H2

/-- **What `Create` lends its cleanup** (see the file header). -/
def createFr (R : Roots) (jr : Ino) (r nm : GoString) (qa : DFrac) (N : NameSet) (h : NamesH)
    (c : Qp) (hn : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) : IProp GF :=
  iprop(osPathS (L := hG.goose_localGS) R r qa jr ∗
    osNames (L := hG.goose_localGS) jr ((N.diff [tmpName nm]).diff [nm]) (DFrac.own (1 : Qp).half)
      ((h.restrict jr (N.diff [tmpName nm])).restrict jr ((N.diff [tmpName nm]).diff [nm])) ∗
    osNames (L := hG.goose_localGS) jr (.only [nm]) (DFrac.own c) hn ∗
    areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) ∗
    walSplitFrag (W := W) Wn)

/-- **The area less `nm.tmp`, after the cleanup's rename was called** (see the file header). -/
def createAreaL (jr : Ino) (nm : GoString) (N : NameSet) (cl : List (GoString × Claim))
    (Wn : List GoString) : IProp GF :=
  iprop(walUnlockedTokX (W := W) ∗
    ∃ h' : NamesH, osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half) h' ∗
      areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) ∗
      walSplitFrag (W := W) Wn)

/-- **What `Create` gets back from its cleanup's rename** (see the file header). -/
def createFin (R : Roots) (jr : Ino) (r nm : GoString) (qa : DFrac) (f : Loc) (N : NameSet)
    (cl : List (GoString × Claim)) (Wn : List GoString) (_err : GoInterface) : IProp GF :=
  iprop(osPathS (L := hG.goose_localGS) R r qa jr ∗ osCallPerm (L := hG.goose_localGS) 1 ∗
    (∃ nmf : GoString, os.ownFile f (-1 : w64) nmf (DFrac.own 1)) ∗ createAreaL (W := W) jr nm N cl Wn)

/-- **The cleanup's rename law** (see the file header). -/
theorem create_cleanupLaw (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString) (qa : DFrac)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString) (c d : Qp)
    (hn : NamesH) (J : Ino) (f : Loc)
    (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hself : h.restrict jr N = h) (hNnm : N.Mem nm)
    (hcd : d + (d + c) = (1 : Qp).half) (hJ : hn.cur !! nm = some (.dir J)) :
    ⊢ walAreaOk (L := hG.goose_localGS) (W := W) walCodec Mr R jr r -∗
      cleanupLaw (W := W) R jr r nm R d f (createFr (W := W) R jr r nm qa N h c hn cl Wn)
        (createFin (W := W) R jr r nm qa f N cl Wn) := by
  sorry

/-- **`walAreaRes` back after the cleanup's rename** (see the file header): `nm.tmp`'s claim (absent)
merged back. -/
theorem create_cleanBack (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r nm : GoString)
    (N : NameSet) (cl : List (GoString × Claim)) (Wn : List GoString) (ht : NamesH)
    (hft : ht.cur !! tmpName nm = none) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ createAreaL (W := W) jr nm N cl Wn -∗
      osNames (L := hG.goose_localGS) jr (.only [tmpName nm]) (DFrac.own 1) ht ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walAreaRes (L := hG.goose_localGS) jr := by
  sorry

end iris

end WalFs
end EtcdGrove
end Perennial

end
