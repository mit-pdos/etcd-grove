/-
`hashMap.FreeCount` (U2 internal; ported from the old proof).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__hashmapFreeCountSlow
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Callees

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The count of a consistent `hashMap` is the number of free ids. -/
theorem fc_cnt {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) : cnt = W64 (free.length : Int) := by
  have := h.2.2.2.1; have := h.2.2.2.2; word

/-- `f.FreeCount()`: the number of free ids (the optional check, that the count agrees with
the spans, holds). -/
abbrev hashMap.FreeCount.spec : Prop :=
  ∀ (h s : Loc) (free : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownHashPart (GF := GF) h s free }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"FreeCount")) (Val #()))
  {{ RET #(W64 (free.length : Int)); ownHashPart h s free }}

theorem hashMap.FreeCount.wp_proof (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG))
    (hSlow : hashMap.hashmapFreeCountSlow.spec (GF := GF) (hG := hG)) :
    hashMap.FreeCount.spec (GF := GF) (hG := hG) := by
  intro h s free
  wp_start as Hpart
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply (hVerify _ iprop(f_ptr ↦ h ∗ ownHashPart h s free)) $$ [f Hpart]
  · isplit
    · wp_auto
      wp_apply (hSlow h s free) $$ [Hpart] as Hpart
      · iexact Hpart
      unfold ownHashPart
      iNamed Hpart
      unfold hmRaw
      iNamed Hraw
      wp_auto
      rw [← fc_cnt Hok]
      wp_auto
      iframe
      iexists cnt, sp, bwm, sets
      simp only [named]
      iframe
      ipureintro; exact Hok
    · iframe
  iintro ⟨f, Hpart⟩
  unfold ownHashPart
  iNamed Hpart
  unfold hmRaw
  iNamed Hraw
  wp_auto
  rw [← fc_cnt Hok]
  iapply HΦ
  iexists cnt, sp, bwm, sets
  simp only [named]
  iframe
  ipureintro; exact Hok

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
