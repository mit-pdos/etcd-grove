/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Close.wp_proof : mvcc.watchStream.Close.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ
  wp_start as ⟨Hws, Htok⟩
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%g, #Hg, #HgS⟩, -⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  cases closed with
  | true =>
    simp only [↓reduceIte]
    iunfold mvcc.watchStreamOpen at Hcl Htok
    icases token_exclusive γ $$ Hcl Htok with ⟨⟩
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hcl with ⟨%L, HCR, #HL⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ f : GoFunc,
      "cancel" ∷ cancel_ptr ↦ f ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "#Hdone" ∷ □ (∀ (id : w64) (w : Loc), ⌜id ∈ keys.take i.toNat⌝ -∗ ⌜WM !! id = some w⌝ -∗
        P.WC w))) $$ Hcm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [cancel]
  · iexists _
    simp only [named]
    iframe cancel
    isplitr
    · ipureintro; exact Int.le_refl _
    imodintro
    iintro %id %w %hin %_
    simp at hin
  isplitr
  · imodintro
    iintro %i %key %c ⟨%Hkey, %Hc⟩ HP
    iNamed HP
    obtain ⟨w, hw⟩ : ∃ w, WM !! key = some w := by
      have h := Hdom key
      rw [Hc] at h
      exact Option.isSome_iff_exists.1 (by simpa using h.symm)
    ihave #Hcspec := Hcs $$ %key %c %w %Hc %hw
    iunfold mvcc.cancelSpec at Hcspec
    wp_auto
    wp_apply Hcspec as #Hwc
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _
    simp only [named]
    iframe cancel
    isplitr
    · ipureintro; omega
    imodintro
    iintro %id %w' %hin %hw'
    have htake : (i + 1).toNat = i.toNat + 1 := by omega
    rw [htake, List.take_add_one, Hkey] at hin
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hin
    rcases hin with hin | rfl
    · iapply Hdone $$ %id %w' %hin %hw'
    · rw [hw] at hw'
      cases hw'
      iexact Hwc
  iintro HP Hcm
  iNamed HP
  wp_auto
  have htk : List.take (↑CM.size : Int).toNat keys = keys := by
    rw [List.take_of_length_le]; omega
  rw [htk] at *
  wp_apply Hclose $$ [$HCR]
  · imodintro
    iintro %w %hin
    icases HL $$ %w %hin with (⟨%id, %hid⟩ | #Hwc)
    · have hk : id ∈ keys := by
        rw [Hkset, Hdom id, hid]; rfl
      iapply Hdone $$ %id %w %hk %hid
    · iexact Hwc
  iunfold gaugeSpec at HgS
  icases HgS with ⟨-, #HDec, -⟩
  wp_apply HDec
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Htok]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, true, cm, wm, CM, WM
    simp only [named, ↓reduceIte]
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hnn⟩
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
