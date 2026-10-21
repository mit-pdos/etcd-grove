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

/-- The member id of a server of the list, and its place in the network. -/
theorem srvNetMember_lookup (γn : NetNames GF) (ss : List Loc) (k : Nat) (s : Loc)
    (hk : ss[k]? = some s) :
    ([∗list] s ∈ ss, ∃ id : w64, srvNetMember γn s id) ⊢ ∃ id : w64, srvNetMember γn s id := by
  iintro Hmem
  ihave H := (BigSepL.bigSepL_lookup
    (Φ := fun _ s => iprop(∃ id : w64, srvNetMember (GF := GF) γn s id)) hk) $$ Hmem
  iexact H

theorem peerStep.wp_proof
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_CutPeer : EtcdServer.CutPeer.spec (GF := GF) (hG := hG))
    (wp_MendPeer : EtcdServer.MendPeer.spec (GF := GF) (hG := hG)) :
    peerStep.spec (GF := GF) (hG := hG) := by
  intro γn srvs ss kind a b
  wp_start as ⟨#Hsrvs, #Hmem⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len $$ Hsrvs
  wp_auto
  wp_if_destruct
  · iapply HΦ; itrivial
  have hA0 := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; itrivial
  have hAn := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; itrivial
  have hB0 := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; itrivial
  have hBn := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; itrivial
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
  ihave #Hma := srvNetMember_lookup γn ss _ sa Hsa_lookup $$ Hmem
  icases Hma with ⟨%ida, #Hma⟩
  ihave #Hmb := srvNetMember_lookup γn ss _ sb Hsb_lookup $$ Hmem
  icases Hmb with ⟨%idb, #Hmb⟩
  -- the member ids (`srvProcOk`'s)
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
    wp_apply (wp_CutPeer γn sa ida idb) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_MemberID sa ida) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_CutPeer γn sb idb ida) $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ; itrivial
  · wp_apply (wp_MemberID sb idb) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_MendPeer γn sa ida idb) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_MemberID sa ida) $$ []
    · iframe #
    (try wp_auto)
    wp_apply (wp_MendPeer γn sb idb ida) $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end linkv3p
end EtcdGrove
end Perennial
