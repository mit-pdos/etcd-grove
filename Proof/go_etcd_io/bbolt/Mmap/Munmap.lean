/-
`DB.munmap` (U4, `notes/bbolt-proof-plan.md`): `munmap(db)` (`munmapM`), its error logged and
wrapped by `fmt.Errorf`; the deferred `db.invalidate()` clears the mapping fields and the metas'
pointers whatever happened (`mapFields … none`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.ErrPtr
public import Proof.go_etcd_io.bbolt.Mmap.Unmap
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.fmt.Errorf
public import Proof.go_etcd_io.bbolt.Mmap.FileSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section munmap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.munmap()` of the mapping `base`/`l`** (whole: the mapping fields, `datasz` and every
cell's client half): the fields cleared (`mapFields … none`, `datasz` 0); the mapping gone from
OsFs, or, on an error (`fmtErrorOk`), possibly still there with its cells. -/
abbrev DB.munmap.spec : Prop :=
  ∀ (db base : Loc) (l : Nat) (lg : GoInterface) (p : GoString) (m : OsMeta) (vf : Nat → val),
  db ≠ null → 0 < l → m.maps !! base = some l →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
      mapFields db (DFrac.own 1) (some (base, l)) ∗ db.[DB, go!"datasz"] ↦ W64 (l : Int) ∗
      osMeta p (DFrac.own 1) (some m) ∗ cellsR (GF := GF) base 0 l vf }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ (err : GoInterface), RET #err;
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      ((⌜err = interface.nil⌝ ∗
          osMeta p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps })) ∨
       (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err ∗
        (osMeta p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps }) ∨
         (osMeta p (DFrac.own 1) (some m) ∗ cellsR base 0 l vf)))) }}

theorem DB.munmap.wp_proof (hM : munmapM.spec (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    DB.munmap.spec (GF := GF) (hG := hG) := by
  intro db base l lg p m vf hdb hl hmap
  wp_start as ⟨#Hos, #Hlg, #Hlgok, Hmf, Hsz, Hm, Hc⟩
  ihave %hgoos : ⌜goosLinux⌝ $$ []
  · iapply goosLinux_of_pkgInit $$ Hpkg
  ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
  · iapply goarchAmd64_of_pkgInit $$ Hpkg
  simp only [mapFields]
  icases Hmf with ⟨Hdr, Hd, Hm0, Hm1, %hb⟩
  have hlen : (W64 (l : Int)).toNat = l := by word
  have hlen' : 0 < (W64 (l : Int)).toInt := by word
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply hM db base (W64 (l : Int)) base (W64 (l : Int)) p m vf hlen' (by rw [hlen]; exact hmap)
    $$ [Hdr Hd Hsz Hm Hc] as %e ⟨Hdr, Hd, Hsz, Hr⟩
  · rw [hlen]; iframe; iframe #
  rw [hlen]
  try wp_auto
  unfold goosLinux at hgoos
  unfold goarchAmd64 at hgoarch
  by_cases he : e = 0
  · subst he
    simp only [errnoErr, ↓reduceIte]
    icases Hr with (⟨-, Hm⟩ | ⟨%hne, -⟩)
    · wp_auto
      wp_method_call
      wp_auto
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; rfl
    · exact absurd rfl hne
  · have hS := hErr e he
    obtain ⟨ii, hii⟩ : ∃ ii, errnoErr e = GoInterface.ok ii :=
      ⟨⟨syscall.Errno.ty, #e⟩, by simp only [errnoErr, he, ↓reduceIte, interface.mkOk]⟩
    rw [hii] at hS ⊢
    ihave #HeS := hS
    try rw [hgoos, hgoarch]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply hLogger db lg hdb $$ []
    · iframe; iframe #
    try wp_auto
    cases lg with
    | nil => unfold boltLogger; iexfalso; iexact Hlgok
    | ok li =>
    simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl,
      show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl, List.set_cons_succ, List.set_cons_zero]
    wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 100, W8 118] _
      [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
        interface.mkOk go.int #(W64 0), GoInterface.ok ii] _ iprop(True) _
      (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
    · iframe
    · log_args_ok
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei ⟨-, #HiS, %Hty, %Hptr⟩
    · iframe
      fmt_args_intro
      isplitl
      · fmt_arg_method; iapply fmtErrorOk_argOk $$ HeS
      · itrivial
    try wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => nomatch h), errPtrTyped_of_ptr _ Hptr⟩
    isplitr
    · iapply fmtErrorOk_of_errorf ei Hty $$ HiS
    icases Hr with (⟨%h0, -⟩ | ⟨-, Hr⟩)
    · exact absurd h0 he
    · iexact Hr

end munmap

end bbolt
end EtcdGrove
end Perennial
