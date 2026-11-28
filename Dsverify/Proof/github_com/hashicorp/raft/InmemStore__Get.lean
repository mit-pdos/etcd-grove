/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InmemStore__Get.lean (241f27e).
-/
/-
The proof of `raft.(*InmemStore).Get`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.InmemStore__Get
public import Perennial.Proof.errors.NewVar

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

/-- `errors.New(msg)` returns a fresh `*errorString` holding `msg` (persistent points-to). -/
theorem github_com.hashicorp.raft.wp_New_errorString_pt (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        x ↦□ errors.errorString.mk msg }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  ipersist Hx
  wp_auto
  iapply HΦ
  iexact Hx

theorem github_com.hashicorp.raft.InmemStore.Get.wp_proof :
    github_com.hashicorp.raft.InmemStore.Get.spec (GF := GF) (hG := hG) :=
  fun γs i key kb tid => by
  wp_start as ⟨#His, #Hkey, Htok⟩
  iNamed His
  unfold inmemPool
  icases Hpool with ⟨%γp, #Hpool⟩
  iapply wp_fupd
  wp_auto
  wp_apply (lc := 3) wp_with_defer as %defer Hdefer
  imod qpool.borrow_lc inmemPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock (i.[InmemStore, go!"l"]) (storeInv γs i)) $$ [$Hown]
    with ⟨Hrlocked, HP⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc2 HP with HP
  icases (storeInv_unfold γs i _).mp $$ HP with
    ⟨%c, Hgc, Hlow, Hhigh, Hlogsf, Hlogs, Hkvf, Hkv, Hkvintf, Hkvint, Hgl, Hgk, %Hok, #Hpers⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HAU⟩
  imod lc_fupd_elim_later (E := ∅) $$ Hlc3 HAU with ⟨%st, Hkvw, Hclose⟩
  ihave %Hst := kvView_agree γs _ st c.st $$ Hkvw Hgk
  subst Hst
  imod Hclose $$ Hkvw with HΦ
  imodintro
  iframe Hnc
  wp_apply (wp_bytes_to_string key kb DFrac.discard) $$ [$Hkey] with -
  wp_apply (wp_map_lookup1 go.string (go.GoType.SliceType go.byte) c.mkv c.kvm kb
    (DFrac.own sync.rfrac)) $$ [$Hkv] with Hkv
  wp_if_destruct
  · -- `val == nil`: not found
    ihave %Hempty : (⌜∀ vb, c.st.bytes !! kb = some vb → vb = []⌝ : IProp GF) $$ []
    · cases hkv : c.kvm !! kb with
      | none =>
        ipureintro
        intro vb hvb
        have := (Hok.2.2 kb).mpr (by rw [hvb]; rfl)
        rw [hkv] at this; cases this
      | some s =>
        rw [hkv, Option.getD_some] at Hif
        subst Hif
        ihave Hp2 := Hpers
        iNamed Hp2
        icases Hpkv $$ %kb %slice.nil %hkv with ⟨%vb', %Hvb', Hs⟩
        ihave %Hl := ownSlice_len $$ Hs
        ipureintro
        intro vb hvb
        rw [Hvb'] at hvb; cases hvb
        apply List.eq_nil_of_length_eq_zero
        rw [Hl.1]; rfl
    wp_apply (github_com.hashicorp.raft.wp_New_errorString_pt _) as %x #Hx
    wp_apply (sync.RWMutex.wp_RUnlock (i.[InmemStore, go!"l"]) (storeInv γs i))
      $$ [$Hrlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk] with Hown
    · inext
      iapply (storeInv_unfold γs i _).mpr
      iexists c
      iframe
      iframe #
      ipureintro; exact Hok
    imod qpool.giveBack inmemPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
      with Htok
    imodintro
    ispecialize HΦ $$ Htok
    icases HΦ with ⟨-, HΦ⟩
    iapply HΦ
    · ipureintro; exact Hempty
    · unfold isNotFoundErr
      iexists x
      iframe #
      ipureintro; rfl
  · -- found
    obtain ⟨s, hs⟩ : ∃ s, c.kvm !! kb = some s := by
      cases hkv : c.kvm !! kb with
      | none => rw [hkv] at Hif; exact absurd rfl Hif
      | some s => exact ⟨s, rfl⟩
    rw [hs, Option.getD_some]
    ihave Hp2 := Hpers
    iNamed Hp2
    icases Hpkv $$ %kb %s %hs with ⟨%vb, %Hvb, #Hs⟩
    wp_apply (sync.RWMutex.wp_RUnlock (i.[InmemStore, go!"l"]) (storeInv γs i))
      $$ [$Hrlocked Hgc Hlow Hhigh Hlogsf Hlogs Hkvf Hkv Hkvintf Hkvint Hgl Hgk] with Hown
    · inext
      iapply (storeInv_unfold γs i _).mpr
      iexists c
      iframe
      iframe #
      ipureintro; exact Hok
    imod qpool.giveBack inmemPoolN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
      with Htok
    imodintro
    ispecialize HΦ $$ Htok
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ $$ %vb %Hvb %s Hs

end proof

end Perennial
