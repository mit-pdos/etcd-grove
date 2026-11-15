/-
**`DB.freepages` with its consistency check linked** (maintainer 10, the plan's U10h link): U10h's
key-order check (`Commit/CheckKeyOrder{,Int,Verify}`) composed with `checkInvariantProperties`
(`Commit/CheckInv`, `Commit/CheckReach`) and the bucket walk (`Commit/CheckRoot`) into
`Tx.recursivelyCheckBucket_root.spec`, and that into `DB.freepages.wp_proof`: what is left are
the specs of the check's callees outside it (the page accessors, `Tx.page_r`, `Tx.forEachPage_r`,
`Bucket.ForEachBucket_r`, `Bucket.Bucket_r`, `bytes.Compare`, ...) and freepages' own.
-/
module

public import Proof.go_etcd_io.bbolt.DB__freepages
public import Proof.go_etcd_io.bbolt.Commit.CheckRoot
public import Proof.go_etcd_io.bbolt.Commit.CheckKeyOrder
public import Proof.go_etcd_io.bbolt.Commit.CheckKeyOrderVerify

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section link
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The key-order check linked**: `Tx.recursivelyCheckPageKeyOrder_ok` over its internal
recursion and `verifyKeyOrder`'s comparison. -/
theorem Tx.recursivelyCheckPageKeyOrder_ok.wp_linked
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBEs : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hLEs : internal.common.Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hLE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hLK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hCmp : bytes.Compare.spec (GF := GF) (hG := hG)) :
    Tx.recursivelyCheckPageKeyOrder_ok.spec (GF := GF) (hG := hG) :=
  Tx.recursivelyCheckPageKeyOrder_ok.wp_proof
    (Tx.recursivelyCheckPageKeyOrderInternal_ok.wp_proof hpage hIB hIL hCnt hBEs hBE hLEs hLE hBP
      hBK hLK (verifyKeyOrder_ok.wp_proof (compareKeys_ok.wp_proof hCmp)))

/-- **The consistency check of the root bucket linked** (`checkInvariantProperties` with the
key-order check, the bucket walk). -/
theorem Tx.recursivelyCheckBucket_root.wp_linked
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hfep : Tx.forEachPage_r.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hOv : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hfeb : Bucket.ForEachBucket_r.spec (GF := GF) (hG := hG))
    (hbkt : Bucket.Bucket_r.spec (GF := GF) (hG := hG))
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBEs : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hLEs : internal.common.Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hLE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hLK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hCmp : bytes.Compare.spec (GF := GF) (hG := hG)) :
    Tx.recursivelyCheckBucket_root.spec (GF := GF) (hG := hG) :=
  have hcip := Tx.checkInvariantProperties_ok.wp_proof hfep
    (verifyPageReachable_ok.wp_proof hId hOv hIB hIL) hPgid
    (Tx.recursivelyCheckPageKeyOrder_ok.wp_linked hpage hIB hIL hCnt hBEs hBE hLEs hLE hBP hBK
      hLK hCmp)
  Tx.recursivelyCheckBucket_root.wp_proof hRP hcip hfeb hbkt
    (Tx.recursivelyCheckBucket_child.wp_proof hRP hcip hfeb)

/-- **`DB.freepages` with its check linked.** -/
theorem DB.freepages.wp_linked
    (wp_beginTx_s : DB.beginTx_s.spec (GF := GF) (hG := hG))
    (wp_Rollback_r : Tx.Rollback_r.spec (GF := GF) (hG := hG))
    (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hfep : Tx.forEachPage_r.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hOv : internal.common.Page.Overflow.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hfeb : Bucket.ForEachBucket_r.spec (GF := GF) (hG := hG))
    (hbkt : Bucket.Bucket_r.spec (GF := GF) (hG := hG))
    (hpage : Tx.page_r.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBEs : internal.common.Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hLEs : internal.common.Page.LeafPageElements.spec (GF := GF) (hG := hG))
    (hLE : internal.common.Page.LeafPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hBK : internal.common.branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hLK : internal.common.leafPageElement.Key.spec (GF := GF) (hG := hG))
    (hCmp : bytes.Compare.spec (GF := GF) (hG := hG)) :
    DB.freepages.spec (GF := GF) (hG := hG) :=
  DB.freepages.wp_proof wp_beginTx_s wp_Rollback_r wp_meta hPgid
    (Tx.recursivelyCheckBucket_root.wp_linked hRP hfep hId hOv hPgid hfeb hbkt hpage hIB hIL hCnt
      hBEs hBE hLEs hLE hBP hBK hLK hCmp)

end link

end bbolt
end EtcdGrove
end Perennial
