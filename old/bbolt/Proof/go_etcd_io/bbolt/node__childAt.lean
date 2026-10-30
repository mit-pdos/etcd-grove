module
public import Spec.go_etcd_io.bbolt.node__childAt
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.childAt.wp_proof (hPgid : Inode.Pgid.spec (GF := GF) (hG := hG))
    (hnode : Bucket.node.spec (GF := GF) (hG := hG)) :
    node.childAt.spec (GF := GF) (hG := hG) := by
  intro W bl B txl st pmap pm dqp nl r idx w p pg src HvOK Htx Hr Hbl Hleaf Hi0 Hw Hnn Hsrc
  wp_start as ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb⟩
  icases bktOwn_node_acc W bl B nl r Hr $$ Hb with ⟨Hn, Hback⟩
  isimp only [nodeOwn] at Hn
  icases Hn with ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hents
  ihave %Hsl := ownSlice_len _ _ _ $$ Hins
  have Hlt : (sint.Z idx).toNat < r.ins.length := by
    rw [Hlen]; exact (List.getElem?_eq_some_iff.1 Hw).1
  obtain ⟨it, Hit⟩ : ∃ it, r.ins[(sint.Z idx).toNat]? = some it :=
    ⟨_, List.getElem?_eq_getElem Hlt⟩
  icases wOwn_at W r.ins r.ws _ it w Hit Hw $$ Hents with ⟨%Hp, Hents⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  rw [Hleaf]
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z r.nv.inodes'.len
    from ⟨Hi0, by obtain ⟨h1, h2⟩ := Hsl; rw [h1] at Hlt; word⟩))]
  icases ownSlice_elem_acc (sint.Z idx) it r.nv.inodes' _ _ Hi0 Hit $$ Hins with ⟨Hit', Hsback⟩
  wp_apply hPgid $$ [$Hit'] as Hit'
  try wp_auto
  ihave Hins := Hsback $$ Hit'
  rw [list_set_lookup_self _ _ _ Hit]
  ihave Hb := Hback $$ %r [Hn Hins Hcap Hents Hch Hchcap Hkey]
  · unfold nodeOwn; iframe
  rw [bktOwn_insert_same W bl B nl r Hr, Hbl, Hp.2]
  wp_apply hnode W bl B txl st pmap pm dqp w.pgid nl p pg src HvOK Htx Hnn
    (fun h => ⟨Hsrc h, Or.inr (by rw [Hr]; rfl)⟩) $$ [Hb Hv Hst Hpf Hpm Hdb]
    as %l %B' %st' ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb, %Hres⟩
  · iframe
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hres

end proof

end bbolt
end EtcdGrove
end Perennial
