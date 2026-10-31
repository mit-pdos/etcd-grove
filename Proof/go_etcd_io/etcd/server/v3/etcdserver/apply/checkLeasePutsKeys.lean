/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
/-- `l.Keys()` by the lease owner, over its resource opened at `l` (`Lease.Keys.spec`): exactly
the keys `I` attaches to `id`, bounded since `I`'s are (`itemKeysShort`). -/
private theorem keys_open (hK : lease.Lease.Keys.spec (GF := GF) (hG := hG)) (γl : GName)
    (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64) (l : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
        lease.leaseOwnOpen γl L I id l }}
      (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!! go!"Keys"))
        (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString, sl ↦* ks ∗ lease.leaseOwnOpen γl L I id l ∗
        ⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝ ∗
        ⌜∀ k : GoString, I.lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id →
          k ∈ ks⌝ }} := by
  iintro %Φ ⟨#Hpkg, Ho⟩ HΦ
  iunfold lease.leaseOwnOpen at Ho
  icases Ho with ⟨%HIS, #Hl, Hio, Hslot, Hback⟩
  iapply (hK γl l id (.owner I)) $$ [Hio Hslot]
  · iframe Hpkg Hl; rw [lease.keysPre_owner]; iframe Hio Hslot
  iintro !> %sl %ks ⟨Hs, Hpre, Hpost, %Hnd⟩
  ihave Hpre : iprop(lease.leaseItemsOwn l I id ∗
      sync.ownRWMutex (lease.lsF go!"mu" l) (lease.leaseItems γl l)) $$ [Hpre]
  · rw [← lease.keysPre_owner]; iexact Hpre
  icases Hpre with ⟨Hio, Hslot⟩
  ihave %Hks : ⌜∀ k : GoString, k ∈ ks ↔
      I.lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id⌝ $$ [Hpost]
  · rw [← lease.keysPost_owner]; iexact Hpost
  iapply HΦ
  iexists ks
  iframe Hs
  isplitl [Hio Hslot Hback]
  · iunfold lease.leaseOwnOpen; iframe Hl Hio Hslot Hback; ipureintro; exact HIS
  ipureintro
  exact ⟨fun k hk => HIS _ id ((Hks k).1 hk), fun k hk => (Hks k).2 hk⟩

/-- The passed checks of a prefix of the keys: their writes. -/
private def keysPerms (ks : List GoString) : List apply.Perm3 := ks.map (fun k => (k, [], .write))

theorem apply.checkLeasePutsKeys.wp_proof (hK : lease.Lease.Keys.spec (GF := GF) (hG := hG)) :
    apply.checkLeasePutsKeys.spec (GF := GF) (hG := hG) := by
  intro st γ P f RD on RW ai info dq l id γl L I
  wp_start as ⟨#Hst, Hai, Hv, Hrd⟩
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  iunfold apply.isAuthStore at Hst
  icases Hst with ⟨%sti, %Hsti, #HPut, -, -, #HAdmin, -⟩
  subst Hsti
  wp_auto
  wp_apply HAdmin $$ [$Hai $Hrd] as %err ⟨Hai, Hrd, #HeI1, %Hoff, #Hadm⟩
  cases err with
  | nil =>
    wp_auto
    iapply HΦ; iframe Hai Hrd Hv; isplitl []
    · iapply authApplyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    iintro %_
    cases on with
    | on γa =>
      ihave ⟨⟨%i, %sa, #Hsa, %Hok⟩, -⟩ : iprop((∃ (i : Nat) (st : auth.AuthState),
          auth.authStateAt (GF := GF) γa i st ∗
          ⌜GoInterface.nil = GoInterface.nil → auth.adminOk st ((some info).map auth.authInfoM)⌝) ∗
          True) $$ [Hadm]
      · iunfold auth.adminVerdict at Hadm
        icases Hadm with ⟨H1, -⟩
        iframe H1
      unfold apply.leaseKeysClass
      ileft
      iexists i, sa
      iframe Hsa
      ipureintro
      simpa using Hok rfl
    | _ =>
      unfold apply.leaseKeysClass
      iintro; itrivial
  | ok e =>
  wp_auto
  wp_apply (keys_open hK γl L I id l) $$ [$Hlp $Hv] as %sl ⟨%ks, Hks, Hv, %Hksb, %Hkall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hks
  irename «as» => Has
  iunfold apply.permCheck2 at HPut
  ihave IH : iprop(∃ (n : w64) (k : GoString),
      "i" ∷ i_ptr ↦ n ∗ "key" ∷ key_ptr ↦ k ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝ ∗
      "#Hcls" ∷ apply.classRes on info (keysPerms (ks.take (sint.nat n)))) $$ [i key]
  · iexists W64 0, _
    iframe i key
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, show keysPerms [] = [] from rfl]
      iapply apply.classRes_nil
  wp_for IH
  wp_if_destruct
  · obtain ⟨kx, Hkx⟩ : ∃ kx, ks[(sint.Z n).toNat]? = some kx :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ kx Hn.1 $$ [Hks] as Hks
    · iframe; ipureintro; exact Hkx
    wp_apply wp_string_to_bytes kx as %bsl ⟨Hb, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    wp_apply HPut $$ [$Hai $Hb $Hrd] as %err ⟨Hai, -, Hrd, #HeI2, -, #Hv2⟩
    · ipureintro
      have h1 := Hksb kx (List.mem_of_getElem? Hkx)
      rw [Hbl.1] at h1
      have h3 := Hbl.2
      unfold sint.nat at h1
      word
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, kx
      iframe
      isplitl []
      · ipureintro; constructor <;> word
      · have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
        rw [hsn, List.take_add_one, show ks[sint.nat n]? = some kx from Hkx, Option.toList_some]
        simp only [keysPerms, List.map_append, List.map_cons, List.map_nil]
        iapply apply.classRes_app
        iframe Hcls
        iapply (apply.classRes_of_permVerdict on info kx [] .write) $$ Hv2
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iframe Hai Hrd Hv; isplitl []
      · first | iexact HeI1 | iexact HeI2 | iexact HeI3 | iexact HeI4 | iapply applyErrIs_nil
      isplitl []
      · ipureintro; intro h; cases Hoff h
      · iintro %h; cases h
  iapply HΦ; iframe Hai Hrd Hv; isplitl []
  · iapply authApplyErrIs_nil
  isplitl []
  · ipureintro; intro _; rfl
  iintro %_
  have hall : ks.take (sint.nat n) = ks := by
    apply List.take_of_length_le; unfold sint.nat at *; word
  ihave #Hcls2 : apply.classRes (GF := GF) on info (keysPerms ks) $$ []
  · rw [show keysPerms ks = keysPerms (ks.take (sint.nat n)) by rw [hall]]; iexact Hcls
  unfold apply.leaseKeysClass
  cases on with
  | on γa =>
    iright
    iintro %k %hk
    have hmem : ((k, [], .write) : apply.Perm3) ∈ keysPerms ks := by
      unfold keysPerms; exact List.mem_map_of_mem (Hkall k hk)
    ihave #Hok : apply.classOk (GF := GF) γa info (keysPerms ks) $$ []
    · rw [← apply.classRes_on]; iexact Hcls2
    iapply (apply.classOk_of_mem γa info (keysPerms ks) (k, [], .write) hmem) $$ Hok
  | _ => iintro; itrivial

end proof

end EtcdGrove
end Perennial
