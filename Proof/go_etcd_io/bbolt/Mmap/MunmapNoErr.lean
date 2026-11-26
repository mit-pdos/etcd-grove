/-
`munmap(db)` and `DB.munmap` with no error of the environment (`FsNoErr`, which refutes
`unix.Munmap`'s error arms): `unix.Munmap` returns `nil`, so `munmap(db)` does, and
`DB.munmap` logs and wraps nothing; the mapping is gone from the `OsMeta`. What `DB.Close_noErr.spec`
rests on (`Open/CloseNoErr.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Munmap
public import Spec.golang_org.x.sys.unix.Munmap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section munmap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`munmap(db)` with no error** (`munmapM.spec`'s success arm). -/
abbrev munmapM.specNoErr : Prop :=
  FsNoErr →
  ∀ (db base : Loc) (len : w64) (data : Loc) (dsz : w64) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat → bNsOk p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗ bCsInv p ∗
      db.[DB, go!"dataref"] ↦ (⟨base, len, len⟩ : GoSlice) ∗ db.[DB, go!"data"] ↦ data ∗
      db.[DB, go!"datasz"] ↦ dsz ∗
      bMeta p C L m ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val #(functions munmap [])) (Val #db))
  {{ RET #(errnoErr 0);
      db.[DB, go!"dataref"] ↦ slice.nil ∗ db.[DB, go!"data"] ↦ null ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      bMeta p C L { m with maps := GMap.delete base m.maps } }}

theorem munmapM.wp_proofNoErr
    (hMunmap : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG))
    (hMunmapC : golang_org.x.sys.unix.Munmap.specCrashILR (GF := GF) (hG := hG)) :
    munmapM.specNoErr (GF := GF) (hG := hG) := by
  intro hfs db base len data dsz p C L m vf hlen hmap hns
  wp_start as ⟨#Hos, #Hinv, Hdr, Hd, Hsz, Hm, Hc⟩
  wp_auto
  have hne : (⟨base, len, len⟩ : GoSlice) ≠ slice.nil := by
    intro h; have := congrArg GoSlice.len h; simp [slice.nil] at this; subst this; simp at hlen
  rw [decide_eq_false hne]
  wp_auto
  wp_apply wp_bMunmap hMunmap hMunmapC base len p C L m vf hlen hmap hns $$ [Hm Hc] as %e Hr
  · iframe; iframe #
  icases Hr with (⟨%he, Hm⟩ | ⟨%he, -⟩)
  rotate_left
  · exact absurd hfs he.2
  subst he
  try wp_auto
  iapply HΦ
  iframe

/-- **`db.munmap()` of the mapping `base`/`l` with no error** (`DB.munmap.spec`'s success arm):
`nil`, the fields cleared, the mapping gone from OsFs. -/
abbrev DB.munmap.specNoErr : Prop :=
  FsNoErr →
  ∀ (db base : Loc) (l : Nat) (lg : GoInterface) (p : BFile) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) (vf : Nat → val),
  db ≠ null → 0 < l → m.maps !! base = some l → bNsOk p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗ bCsInv p ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
      mapFields db (DFrac.own 1) (some (base, l)) ∗ db.[DB, go!"datasz"] ↦ W64 (l : Int) ∗
      bMeta p C L m ∗ cellsR (GF := GF) base 0 l vf }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ RET #(interface.nil : GoInterface);
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      bMeta p C L { m with maps := GMap.delete base m.maps } }}

theorem DB.munmap.wp_proofNoErr (hM : munmapM.specNoErr (GF := GF) (hG := hG)) :
    DB.munmap.specNoErr (GF := GF) (hG := hG) := by
  intro hfs db base l lg p C L m vf hdb hl hmap hns
  wp_start as ⟨#Hos, #Hinv, #Hlg, #Hlgok, Hmf, Hsz, Hm, Hc⟩
  simp only [mapFields]
  icases Hmf with ⟨Hdr, Hd, Hm0, Hm1, %hb⟩
  have hlen : (W64 (l : Int)).toNat = l := by word
  have hlen' : 0 < (W64 (l : Int)).toInt := by word
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply hM hfs db base (W64 (l : Int)) base (W64 (l : Int)) p C L m vf hlen'
    (by rw [hlen]; exact hmap) hns $$ [Hdr Hd Hsz Hm Hc] as ⟨Hdr, Hd, Hsz, Hm⟩
  · rw [hlen]; iframe; iframe #
  try simp only [errnoErr, ↓reduceIte]
  try wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  iframe

end munmap

end bbolt
end EtcdGrove
end Perennial
