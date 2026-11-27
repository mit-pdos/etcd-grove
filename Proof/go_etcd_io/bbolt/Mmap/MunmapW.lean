/-
`DB.munmap` whose error witnesses that **the file system can fail** (session S3f of
`notes/bbolt-integration-plan.md`): `DB.munmap.spec` with `⌜¬ FsNoErr⌝` in its error arm, by cases on
`FsNoErr` (`DB.munmap.specNoErr`, or `DB.munmap.spec`). A remap's failed `munmap` leaks the mapping
(`junkRes_leak`), and the leak records the witness, which `DB.Close_own.spec` reports.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.MunmapNoErr
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section munmap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.munmap()`**, an error witnessing `¬ FsNoErr` (see the file header). -/
abbrev DB.munmap.specW : Prop :=
  ∀ (db base : Loc) (l : Nat) (lg : GoInterface) (p : BFile) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) (vf : Nat → val),
  db ≠ null → 0 < l → m.maps !! base = some l → bNsOk p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗ bCsInv p ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
      mapFields db (DFrac.own 1) (some (base, l)) ∗ db.[DB, go!"datasz"] ↦ W64 (l : Int) ∗
      bMeta p C L m ∗ cellsR (GF := GF) base 0 l vf }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ (err : GoInterface), RET #err;
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      ((⌜err = interface.nil⌝ ∗
          bMeta p C L { m with maps := GMap.delete base m.maps }) ∨
       (⌜err ≠ interface.nil ∧ errPtrTyped err ∧ ¬ FsNoErr⌝ ∗ fmtErrorOk err ∗
        (bMeta p C L { m with maps := GMap.delete base m.maps } ∨
         (bMeta p C L m ∗ cellsR base 0 l vf)))) }}

theorem DB.munmap.wp_proofW (hS : DB.munmap.spec (GF := GF) (hG := hG))
    (hNE : DB.munmap.specNoErr (GF := GF) (hG := hG)) :
    DB.munmap.specW (GF := GF) (hG := hG) := by
  intro db base l lg p C L m vf hdb hl hmap hns
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · iapply hNE hne db base l lg p C L m vf hdb hl hmap hns $$ Hpre
    inext
    iintro ⟨Hmf, Hsz, Hm⟩
    iapply HΦ
    iframe Hmf Hsz
    ileft
    iframe Hm
    ipureintro; rfl
  · iapply hS db base l lg p C L m vf hdb hl hmap hns $$ Hpre
    inext
    iintro %err ⟨Hmf, Hsz, Hr⟩
    iapply HΦ
    iframe Hmf Hsz
    icases Hr with (H | ⟨%he, #Hok, Hr⟩)
    · ileft; iexact H
    · iright
      iframe Hok Hr
      ipureintro; exact ⟨he.1, he.2, hne⟩

end munmap

end bbolt
end EtcdGrove
end Perennial
