module
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas
public import Proof.go_etcd_io.bbolt.CursorSearch_s
public import Spec.go_etcd_io.bbolt.Cursor__search_s
public import Spec.go_etcd_io.bbolt.Cursor__searchNode_s

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

theorem Cursor.searchNode.wp_sproof
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hIPgid : Inode.Pgid.spec (GF := GF) (hG := hG))
    (hsearch : Cursor.search.sspec (GF := GF) (hG := hG)) :
    Cursor.searchNode.sspec (GF := GF) (hG := hG) := by
  intro cl cv es rv W hwm bl B txl pmap pm dqp nl r key kb dk H1 H2 H3 H4 H5 H6
  have HS : ⊢ □ searchIs (GF := GF) := by
    unfold searchIs
    iintro !> %cl %cv %es %W %hwm %bl %B %txl %pmap %pm %dqp %pid %key %kb %dk %Hp
    first
      | iapply (hsearch cl cv es W hwm bl B txl pmap pm dqp pid key kb dk Hp.1 Hp.2.1 Hp.2.2)
      | (imodintro; iapply (hsearch cl cv es W hwm bl B txl pmap pm dqp pid key kb dk Hp.1 Hp.2.1 Hp.2.2))
  have H := HS.trans (searchNode_of_search_s hK hIPgid)
  unfold searchNodeIs at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %trivial %cl %cv %es %rv %W %hwm %bl %B %txl %pmap %pm %dqp %nl %r %key %kb %dk [] [HP] HΦ
  · ipureintro; exact ⟨H1, H2, H3, H4, H5, H6⟩
  · iexact HP

end proof

end bbolt
end EtcdGrove
end Perennial
