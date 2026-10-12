module
public import Spec.go_etcd_io.bbolt.node__prevSibling
public import Spec.go_etcd_io.bbolt.node__childAt
public import Spec.go_etcd_io.bbolt.node__childIndex

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

theorem node.prevSibling.wp_proof (hci : node.childIndex.spec (GF := GF) (hG := hG))
    (hca : node.childAt.spec (GF := GF) (hG := hG)) :
    node.prevSibling.spec (GF := GF) (hG := hG) := by
  intro W bl B txl st pmap pm dqp nl r HvOK Htx Hr Hsib
  wp_start as ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb⟩
  rcases Hsib with Hpn | ⟨rp, Hrp, Hne, Hpleaf, Hpbl, Hsort, Hlive, Hks, Hkids⟩
  · icases bktOwn_node_acc W bl B nl r Hr $$ Hb with ⟨Hn, Hback⟩
    isimp only [nodeOwn] at Hn
    icases Hn with ⟨Hn, Hrest⟩
    wp_auto
    rw [Hpn, decide_eq_true rfl]
    try wp_auto
    ihave Hb := Hback $$ %r [Hn Hrest]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B nl r Hr]
    iapply HΦ
    iframe
    ipureintro; exact Or.inl ⟨rfl, rfl, rfl⟩
  · icases bktOwn_node2_acc W bl B nl r.nv.parent' r rp Hr Hrp (Ne.symm Hne) $$ Hb
      with ⟨Hn, Hp, Hback⟩
    isimp only [nodeOwn] at Hn Hp
    icases Hn with ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
    icases Hp with ⟨Hpn, Hpins, Hpcap, Hpents, Hpch, Hpchcap, Hpkey⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases (pv_half W.data W.ps W.pages W.q).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
    icases nodeBorrow W HvOK.1 rp.ws rp.ins W.q.half Hlive $$ [Hpv1 Hpents]
      with ⟨%es, %Hm, Hes, Hpback⟩
    · iframe
    icases keyBorrow W HvOK.1 W.q.half r.nv.key' r.ksrc r.key Hks $$ [Hpv2 Hkey]
      with ⟨%dk, %ck, -, Hk, Hkback⟩
    · iframe
    icases typedPointsto_not_null_dup _ _ _ $$ Hpn with ⟨Hpn, %Hpnn⟩
    wp_auto
    rw [decide_eq_false Hpnn]
    try wp_auto
    have Hes_sorted : entriesSorted es := (wMatch_sorted _ _ Hm).2 Hsort
    wp_apply hci _ _ _ _ _ es _ _ _ ck dk Hes_sorted $$ [Hpn Hpins Hes Hn Hk]
      as %idx ⟨%Hidx, Hpn, Hpins, Hes, Hn, Hk⟩
    · iframe
    try wp_auto
    ihave Hk := Hkback $$ Hk
    icases Hk with ⟨Hpv2, Hkey⟩
    ihave Hes := Hpback $$ Hes
    icases Hes with ⟨Hpv1, Hpents⟩
    ihave Hpv := (pv_half W.data W.ps W.pages W.q).2 $$ [Hpv1 Hpv2]
    · iframe
    ihave %Hplen := BigSepL2.bigSepL2_length $$ Hpents
    ihave %Hpsl := ownSlice_len _ _ _ $$ Hpins
    ihave Hb := Hback $$ [Hn Hins Hcap Hents Hch Hchcap Hkey] [Hpn Hpins Hpcap Hpents Hpch Hpchcap Hpkey]
    · unfold nodeOwn; iframe
    · unfold nodeOwn; iframe
    wp_if_destruct
    · iapply HΦ
      iframe
      isplitl [Hdata Hpv Hfli]
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
      ipureintro; exact Or.inl ⟨rfl, rfl, rfl⟩
    · icases bktOwn_node_acc W bl B nl r Hr $$ Hb with ⟨Hn, Hback⟩
      isimp only [nodeOwn] at Hn
      icases Hn with ⟨Hn, Hrest⟩
      try wp_auto
      ihave Hb := Hback $$ %r [Hn Hrest]
      · unfold nodeOwn; iframe
      rw [bktOwn_insert_same W bl B nl r Hr]
      have Hidx0 : sint.Z idx ≠ 0 := by intro h; exact Hif (by word)
      have Hle := Hidx.2.1
      have Hi1 : (sint.Z (idx - W64 1)).toNat < rp.ws.length := by
        rw [← wMatch_length Hm] at Hle; word
      obtain ⟨w, Hw⟩ : ∃ w, rp.ws[(sint.Z (idx - W64 1)).toNat]? = some w :=
        ⟨_, List.getElem?_eq_getElem Hi1⟩
      have Hwm : w ∈ rp.ws := List.mem_of_getElem? Hw
      obtain ⟨Hwnn, Hwsrc⟩ := Hkids w Hwm
      obtain ⟨p, pg, src, Hps'⟩ : ∃ p pg src,
          B.nm !! w.pgid = none → nodeSrcOK W B pm w.pgid p pg src := by
        by_cases hn : B.nm !! w.pgid = none
        · obtain ⟨p, pg, src, h⟩ := Hwsrc hn
          exact ⟨p, pg, src, fun _ => h⟩
        · exact ⟨null, [], Src.view, fun h => absurd h hn⟩
      wp_apply hca W bl B txl st pmap pm dqp r.nv.parent' rp (idx - W64 1) w p pg src HvOK Htx Hrp
        Hpbl Hpleaf (by word) Hw Hwnn Hps' $$ [Hb Hdata Hpv Hfli Hst Hpf Hpm Hdb]
        as %l %B' %st' ⟨Hb, Hv, Hst, Hpf, Hpm, Hdb, %Hres⟩
      · unfold wView; iframe; iframe #; ipureintro; exact Hlgv
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      exact Or.inr ⟨rp, _, w, p, pg, src, Hrp, Hw, Hres⟩

end proof

end bbolt
end EtcdGrove
end Perennial
