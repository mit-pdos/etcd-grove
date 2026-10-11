module
public import Spec.go_etcd_io.bbolt.Cursor__searchPage
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

/-- `searchPage`, given `search` (`CursorSearch.lean`). -/
theorem Cursor.searchPage.wp_proof
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hsearch : Cursor.search.spec (GF := GF) (hG := hG)) :
    Cursor.searchPage.spec (GF := GF) (hG := hG) := by
  intro cl cv es rv V q pid pg key kb dk Hok Hlast Hnode Hpa Hbr Hwf Hlen Hkids
  have HS : ⊢ □ searchI (GF := GF) := by
    unfold searchI
    iintro !> %cl %cv %es %V %q %pid %key %kb %dk %Hp
    first
      | iapply (hsearch cl cv es V q pid key kb dk Hp.1 Hp.2)
      | (imodintro; iapply (hsearch cl cv es V q pid key kb dk Hp.1 Hp.2))
  have H := HS.trans (searchPage_of_search hBPEs hCount hKey hPgid)
  unfold searchPageI at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %trivial %cl %cv %es %rv %V %q %pid %pg %key %kb %dk [] [HP] HΦ
  · ipureintro; exact ⟨Hok, Hlast, Hnode, Hpa, Hbr, Hwf, Hlen, Hkids⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
