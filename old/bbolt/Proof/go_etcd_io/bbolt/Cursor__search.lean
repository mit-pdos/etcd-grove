module
public import Spec.go_etcd_io.bbolt.Cursor__search
public import Proof.go_etcd_io.bbolt.CursorSearch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `search`, from the Löb induction tying it to `searchPage` (`CursorSearch.lean`). -/
theorem Cursor.search.wp_proof
    (hpageNode : Bucket.pageNode.spec (GF := GF) (hG := hG))
    (hIsBranch : Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIsLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hisLeaf : elemRef.isLeaf.spec (GF := GF) (hG := hG))
    (hnsearch : Cursor.nsearch.spec (GF := GF) (hG := hG))
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    Cursor.search.spec (GF := GF) (hG := hG) := by
  intro cl cv es V q pid key kb dk Hok Hwf
  have H := search_loeb hpageNode hIsBranch hIsLeaf hisLeaf hnsearch hBPEs hCount hKey hPgid
  unfold searchI at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %cl %cv %es %V %q %pid %key %kb %dk [] [HP] HΦ
  · ipureintro; exact ⟨Hok, Hwf⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
