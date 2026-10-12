module
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas
public import Proof.go_etcd_io.bbolt.CursorSearch_s
public import Spec.go_etcd_io.bbolt.Cursor__search_s
public import Spec.go_etcd_io.bbolt.Cursor__nsearch_s

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

theorem Cursor.search.wp_sproof
    (hpageNode : Bucket.pageNode.wspec (GF := GF) (hG := hG))
    (hIsBranch : Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hIsLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hisLeaf : elemRef.isLeaf.wspec (GF := GF) (hG := hG))
    (hnsearch : Cursor.nsearch.sspec (GF := GF) (hG := hG))
    (hBPEs : Page.BranchPageElements.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hKey : branchPageElement.Key.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hIPgid : Inode.Pgid.spec (GF := GF) (hG := hG)) :
    Cursor.search.sspec (GF := GF) (hG := hG) := by
  intro cl cv es W hwm bl B txl pmap pm dqp pid key kb dk H1 H2 H3
  have H := search_loeb_s hpageNode hIsBranch hIsLeaf hisLeaf hnsearch hBPEs hCount hKey hPgid hK hIPgid
  unfold searchIs at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %cl %cv %es %W %hwm %bl %B %txl %pmap %pm %dqp %pid %key %kb %dk [] [HP] HΦ
  · ipureintro; exact ⟨H1, H2, H3⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
