/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c): the meta key read
through `metaReadSpec`, its value decoded by `BytesToRev`.
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The read at a flag (the spec until review round 5's S1; `nc`: a reader that finds nothing),
the cases `none` and `some CmpRecs.empty` of `UnsafeReadScheduledCompact.spec`. -/
abbrev mvcc.UnsafeReadScheduledCompact.specNC : Prop :=
  ∀ (rt : GoInterfaceOk) (nc : Bool) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ mvcc.metaReadSpec rt nc Rd Tok ∗ mvcc.rdCap Rd Tok ∗ Tok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact)) (Val #(GoInterface.ok rt)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); Tok ∗
      ⌜(found = true → 0 ≤ sint.Z x) ∧ (found = false → x = W64 0) ∧
        (nc = true → found = false)⌝ }}

theorem mvcc.UnsafeReadScheduledCompact.wp_proofNC
    (h0 : mvcc.BytesToRev.spec (GF := GF) (hG := hG)) :
    mvcc.UnsafeReadScheduledCompact.specNC (GF := GF) (hG := hG) := by
  intro rt nc Rd Tok
  wp_start as ⟨#Hrd, #Hcap, Htok⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%skn, #Hskn, #Hsknv⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨⟨%bM, #HMetaG, -⟩, -⟩
  iunfold mvcc.metaReadSpec at Hrd
  (try wp_auto)
  wp_bind (App (App (App (App (Val #(methods rt.ty _ rt.v)) (Val #bM)) (Val #skn)) (Val #(slice.nil)))
    (Val #(W64 0)))
  ihave #Hrd' := Hrd $$ %bM %skn %mvcc.schedKeyBytes %DFrac.discard []
  · ipureintro; exact Or.inl rfl
  iapply Hrd' $$ [Htok]
  · iframe HMetaG Htok
    unfold mvcc.schedKeyBytes
    iexact Hsknv
  inext
  iintro %ks %vs ⟨Htok, -, Hr⟩
  icases Hr with (⟨#Hks, #Hvs⟩ | ⟨%ksl, %vsl, %v, %Hnc, #Hks, -, #Hvs, Hvsl, %Hv⟩)
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl0 : vs.len = W64 0 := by
      simp only [List.length_nil] at h1; unfold sint.nat at h1; word
    wp_if_destruct
    all_goals try (exfalso; exact Hif hl0)
    (try wp_auto)
    iapply HΦ
    iframe Htok
    ipureintro
    simp
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    obtain ⟨x, hx0, rfl⟩ := Hv
    iunfold mvcc.rdCap at Hcap
    icases Hcap $$ %vsl %(mvcc.revBytes ⟨x, W64 0⟩ false) Hvsl Htok with ⟨%dqv, Hvb, Hback⟩
    ihave Hvsl' : vsl ↦*{dqv} (mvcc.revBytes ⟨x, W64 0⟩ false ++ []) $$ [Hvb]
    · rw [List.append_nil]; iexact Hvb
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl1 : vs.len ≠ W64 0 := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1; intro h; rw [h] at h1
      simp at h1
    wp_if_destruct
    all_goals try (exfalso; exact hl1 Hif)
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vs.len := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1
      refine ⟨by decide, ?_⟩
      rw [show sint.Z (W64 0) = 0 by decide]
      have h3 : (sint.Z vs.len).toNat = 1 := h1.symm
      omega
    simp only [Hb0, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index vs (sint.Z (W64 0)) _ DFrac.discard vsl (by decide) $$ [$Hvs] as -
    · ipureintro; rfl
    wp_apply (h0 vsl ⟨x, W64 0⟩ [] dqv (by simp) hx0 (show (0 : Int) ≤ sint.Z (W64 0) by decide)) $$ [$Hvsl'] as Hvsl'
    (try wp_auto)
    iapply HΦ
    isplitl [Hvsl' Hback]
    · iapply Hback
      rw [List.append_nil] at *
      iexact Hvsl'
    ipureintro
    try simp only [mvcc.revVal_main]
    refine ⟨fun _ => hx0, (fun h => by cases h), fun h => ?_⟩
    subst h; cases Hnc


set_option maxHeartbeats 800000 in
/-- **The read under an optional record set** (review round 5's S1): at `none` and at no record,
the read at a flag (`wp_proofNC`); under records, the key's record exactly (the reader returns
it, `metaReadSpecR`). -/
theorem mvcc.UnsafeReadScheduledCompact.wp_proof
    (h0 : mvcc.BytesToRev.spec (GF := GF) (hG := hG)) :
    mvcc.UnsafeReadScheduledCompact.spec (GF := GF) (hG := hG) := by
  have hT := mvcc.UnsafeReadScheduledCompact.wp_proofNC (GF := GF) (hG := hG) h0
  intro rt rs Rd Tok
  rcases rs with _ | r
  · rw [mvcc.metaReadSpecR_none]
    iintro %Φ ⟨#Hpkg, #Hrd, #Hcap, Htok⟩ HΦ
    iapply (hT rt false Rd Tok) $$ [$Htok]
    · iframe #
    iintro !> %x %found ⟨Htok, %Hf⟩
    iapply HΦ
    iframe Htok
    ipureintro
    exact ⟨Hf.1, Hf.2.1, fun r h => by cases h⟩
  by_cases hr : r = mvcc.CmpRecs.empty
  · subst hr
    rw [mvcc.metaReadSpecR_empty]
    iintro %Φ ⟨#Hpkg, #Hrd, #Hcap, Htok⟩ HΦ
    iapply (hT rt true Rd Tok) $$ [$Htok]
    · iframe #
    iintro !> %x %found ⟨Htok, %Hf⟩
    iapply HΦ
    iframe Htok
    ipureintro
    obtain ⟨h0', h1, h2⟩ := Hf
    refine ⟨h0', h1, fun r' hr' => ?_⟩
    cases hr'
    right; exact ⟨h2 rfl, rfl, h1 (h2 rfl)⟩
  unfold mvcc.metaReadSpecR
  simp only [hr, ↓reduceIte]
  wp_start as ⟨#Hrd, #Hcap, Htok⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%skn, #Hskn, #Hsknv⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨⟨%bM, #HMetaG, -⟩, -⟩
  (try wp_auto)
  wp_bind (App (App (App (App (Val #(methods rt.ty _ rt.v)) (Val #bM)) (Val #skn)) (Val #(slice.nil)))
    (Val #(W64 0)))
  ihave #Hrd' := Hrd $$ %bM %skn %mvcc.schedKeyBytes %DFrac.discard []
  · ipureintro; exact Or.inl rfl
  iapply Hrd' $$ [Htok]
  · iframe HMetaG Htok
    unfold mvcc.schedKeyBytes
    iexact Hsknv
  inext
  iintro %ks %vs ⟨Htok, -, Hr⟩
  rw [mvcc.CmpRecs.at_sched]
  icases Hr with (⟨%Hnone, #Hks, #Hvs⟩ | ⟨%ksl, %vsl, %x, %Hx, #Hks, -, #Hvs, Hvsl⟩)
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl0 : vs.len = W64 0 := by
      simp only [List.length_nil] at h1; unfold sint.nat at h1; word
    wp_if_destruct
    all_goals try (exfalso; exact Hif hl0)
    (try wp_auto)
    iapply HΦ
    iframe Htok
    ipureintro
    refine ⟨fun h => (by cases h), fun _ => rfl, fun r' hr' => ?_⟩
    cases hr'
    right; exact ⟨by trivial, Hnone, by trivial⟩
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    obtain ⟨hxr, hx0⟩ := Hx
    iunfold mvcc.rdCap at Hcap
    icases Hcap $$ %vsl %(mvcc.revBytes ⟨x, W64 0⟩ false) Hvsl Htok with ⟨%dqv, Hvb, Hback⟩
    ihave Hvsl' : vsl ↦*{dqv} (mvcc.revBytes ⟨x, W64 0⟩ false ++ []) $$ [Hvb]
    · rw [List.append_nil]; iexact Hvb
    (try wp_auto)
    obtain ⟨h1, h2⟩ := Hlen
    have hl1 : vs.len ≠ W64 0 := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1; intro h; rw [h] at h1
      simp at h1
    wp_if_destruct
    all_goals try (exfalso; exact hl1 Hif)
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vs.len := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1
      refine ⟨by decide, ?_⟩
      rw [show sint.Z (W64 0) = 0 by decide]
      have h3 : (sint.Z vs.len).toNat = 1 := h1.symm
      omega
    simp only [Hb0, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index vs (sint.Z (W64 0)) _ DFrac.discard vsl (by decide) $$ [$Hvs] as -
    · ipureintro; rfl
    wp_apply (h0 vsl ⟨x, W64 0⟩ [] dqv (by simp) hx0 (show (0 : Int) ≤ sint.Z (W64 0) by decide)) $$ [$Hvsl'] as Hvsl'
    (try wp_auto)
    iapply HΦ
    isplitl [Hvsl' Hback]
    · iapply Hback
      rw [List.append_nil] at *
      iexact Hvsl'
    ipureintro
    try simp only [mvcc.revVal_main]
    refine ⟨fun _ => hx0, fun h => (by cases h), fun r' hr' => ?_⟩
    cases hr'
    left; exact ⟨by trivial, hxr⟩

end proof

end EtcdGrove
end Perennial
