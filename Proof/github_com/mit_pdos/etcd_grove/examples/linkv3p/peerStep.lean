/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/peerStep.lean` (until 2026-10-21
`partitioner`'s loop body, the partition plan's S3a). Lean-first (no Rocq counterpart). The range
check (a return if an index is out of range or the two are equal); otherwise the two servers out
of the read-only slice, their members' places in the network out of the `[∗list]`, `MemberID` of
each (the member id `srvNetMember` carries) and `CutPeer` or `MendPeer` of each with the other's
id.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.peerStep
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__CutPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MendPeer

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- A server of the list, its place in the network with a reader's token, lent (2026-10-24, rafthttp
stage 6d: until then its place in the network, persistent). -/
theorem srvPeerCtl_acc (γn : NetNames GF) (ss : List Loc) (k : Nat) (s : Loc)
    (hk : ss[k]? = some s) :
    ([∗list] s ∈ ss, ∃ id : w64, common.srvPeerCtl γn s id) ⊢
      (∃ id : w64, common.srvPeerCtl γn s id) ∗
        ((∃ id : w64, common.srvPeerCtl γn s id) -∗ [∗list] s ∈ ss, ∃ id : w64, common.srvPeerCtl γn s id) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hk
  have hset : ss.set k s = ss := by rw [← hget]; exact List.set_getElem_self hlt
  iintro H
  ihave ⟨Hx, Hc⟩ := (BigSepL.bigSepL_lookup_acc
    (Φ := fun _ s => iprop(∃ id : w64, common.srvPeerCtl (GF := GF) γn s id)) hk).1 $$ H
  iframe Hx
  iintro Hx
  ihave Hl := Hc $$ %s Hx
  rw [hset]
  iexact Hl

theorem peerStep.wp_proof
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_CutPeer : EtcdServer.CutPeer.spec (GF := GF) (hG := hG))
    (wp_MendPeer : EtcdServer.MendPeer.spec (GF := GF) (hG := hG)) :
    peerStep.spec (GF := GF) (hG := hG) := by
  intro hpp γn srvs ss kind a b
  wp_start as ⟨#Hsrvs, Hmem⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len $$ Hsrvs
  wp_auto
  wp_if_destruct
  · iapply HΦ; iexact Hmem
  have hA0 := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; iexact Hmem
  have hAn := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; iexact Hmem
  have hB0 := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; iexact Hmem
  have hBn := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; iexact Hmem
  have hAB := Hif
  (try wp_auto)
  -- in range: the two servers out of the slice, their members
  have hA : 0 ≤ sint.Z a ∧ (sint.Z a).toNat < ss.length := by
    rw [Hsl.1]; unfold sint.nat; constructor <;> word
  have hB : 0 ≤ sint.Z b ∧ (sint.Z b).toNat < ss.length := by
    rw [Hsl.1]; unfold sint.nat; constructor <;> word
  have hAb : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z srvs.len := by constructor <;> word
  have hBb : 0 ≤ sint.Z b ∧ sint.Z b < sint.Z srvs.len := by constructor <;> word
  list_elem ss (sint.Z a).toNat as sa
  list_elem ss (sint.Z b).toNat as sb
  simp only [hAb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z a) ss _ sa hA.1 $$ [] as -
  · iframe #; ipureintro; exact Hsa_lookup
  (try wp_auto)
  simp only [hBb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z b) ss _ sb hB.1 $$ [] as -
  · iframe #; ipureintro; exact Hsb_lookup
  (try wp_auto)
  -- the two servers' places in the network, each borrowed for its member id (`srvProcOk`'s)
  ihave ⟨Ha, Hclose⟩ := srvPeerCtl_acc γn ss _ sa Hsa_lookup $$ Hmem
  icases Ha with ⟨%ida, Ha⟩
  iunfold common.srvPeerCtl at Ha
  icases Ha with ⟨%τa, #Hma, Htka⟩
  ihave Hmem := Hclose $$ [Htka]
  · iexists ida; iunfold common.srvPeerCtl; iexists τa; iframe Htka; iexact Hma
  ihave ⟨Hb, Hclose⟩ := srvPeerCtl_acc γn ss _ sb Hsb_lookup $$ Hmem
  icases Hb with ⟨%idb, Hb⟩
  iunfold common.srvPeerCtl at Hb
  icases Hb with ⟨%τb, #Hmb, Htkb⟩
  ihave Hmem := Hclose $$ [Htkb]
  · iexists idb; iunfold common.srvPeerCtl; iexists τb; iframe Htkb; iexact Hmb
  ihave #Hida : srvMemberIDAddr sa ↦□ ida $$ []
  · iunfold srvNetMember at Hma
    icases Hma with ⟨#Hp, -⟩
    iunfold srvProcOk at Hp
    icases Hp with ⟨%l, %c, %st, %γ, -, -, #Hid, -, -, -, -, -, -, -, -⟩
    iexact Hid
  ihave #Hidb : srvMemberIDAddr sb ↦□ idb $$ []
  · iunfold srvNetMember at Hmb
    icases Hmb with ⟨#Hp, -⟩
    iunfold srvProcOk at Hp
    icases Hp with ⟨%l, %c, %st, %γ, -, -, #Hid, -, -, -, -, -, -, -, -⟩
    iexact Hid
  -- cut or mend, both directions, by the kind
  wp_if_destruct
  · wp_apply (wp_MemberID sb idb) $$ []
    · iframe #
    (try wp_auto)
    ihave ⟨Hx, Hclose⟩ := srvPeerCtl_acc γn ss _ sa Hsa_lookup $$ Hmem
    icases Hx with ⟨%idx, Hx⟩
    iunfold common.srvPeerCtl at Hx
    icases Hx with ⟨%τx, #Hmx, Htkx⟩
    wp_apply (wp_CutPeer hpp γn sa idx idb τx) $$ [Htkx] as Htkx
    · iframe; iframe #
    ihave Hmem := Hclose $$ [Htkx]
    · iexists idx; iunfold common.srvPeerCtl; iexists τx; iframe Htkx; iexact Hmx
    (try wp_auto)
    wp_apply (wp_MemberID sa ida) $$ []
    · iframe #
    (try wp_auto)
    ihave ⟨Hx, Hclose⟩ := srvPeerCtl_acc γn ss _ sb Hsb_lookup $$ Hmem
    icases Hx with ⟨%idx, Hx⟩
    iunfold common.srvPeerCtl at Hx
    icases Hx with ⟨%τx, #Hmx, Htkx⟩
    wp_apply (wp_CutPeer hpp γn sb idx ida τx) $$ [Htkx] as Htkx
    · iframe; iframe #
    ihave Hmem := Hclose $$ [Htkx]
    · iexists idx; iunfold common.srvPeerCtl; iexists τx; iframe Htkx; iexact Hmx
    (try wp_auto)
    iapply HΦ; iexact Hmem
  · wp_apply (wp_MemberID sb idb) $$ []
    · iframe #
    (try wp_auto)
    ihave ⟨Hx, Hclose⟩ := srvPeerCtl_acc γn ss _ sa Hsa_lookup $$ Hmem
    icases Hx with ⟨%idx, Hx⟩
    iunfold common.srvPeerCtl at Hx
    icases Hx with ⟨%τx, #Hmx, Htkx⟩
    wp_apply (wp_MendPeer hpp γn sa idx idb τx) $$ [Htkx] as Htkx
    · iframe; iframe #
    ihave Hmem := Hclose $$ [Htkx]
    · iexists idx; iunfold common.srvPeerCtl; iexists τx; iframe Htkx; iexact Hmx
    (try wp_auto)
    wp_apply (wp_MemberID sa ida) $$ []
    · iframe #
    (try wp_auto)
    ihave ⟨Hx, Hclose⟩ := srvPeerCtl_acc γn ss _ sb Hsb_lookup $$ Hmem
    icases Hx with ⟨%idx, Hx⟩
    iunfold common.srvPeerCtl at Hx
    icases Hx with ⟨%τx, #Hmx, Htkx⟩
    wp_apply (wp_MendPeer hpp γn sb idx ida τx) $$ [Htkx] as Htkx
    · iframe; iframe #
    ihave Hmem := Hclose $$ [Htkx]
    · iexists idx; iunfold common.srvPeerCtl; iexists τx; iframe Htkx; iexact Hmx
    (try wp_auto)
    iapply HΦ; iexact Hmem

end proof

end linkv3p
end EtcdGrove
end Perennial
