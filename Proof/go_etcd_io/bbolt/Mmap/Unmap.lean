/-
bbolt's `munmap(db)` (`bolt_unix.go`) on a mapped database (U4, `notes/bbolt-proof-plan.md`):
`unix.Munmap(db.dataref)`, then `dataref`, `data` and `datasz` cleared, whatever its result. The
nil-mapping case (`db.dataref == nil`, a no-op) is not used by the remap.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.golang_org.x.sys.unix.Munmap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section unmap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`munmap(db)` of the mapping `base`/`len`**: the cells' client halves and the file's
`OsMeta` given, the fields cleared; the error is `unix.Munmap`'s errno. -/
abbrev munmapM.spec : Prop :=
  ∀ (db base : Loc) (len : w64) (data : Loc) (dsz : w64) (p : GoString) (m : OsMeta)
    (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"dataref"] ↦ (⟨base, len, len⟩ : GoSlice) ∗ db.[DB, go!"data"] ↦ data ∗
      db.[DB, go!"datasz"] ↦ dsz ∗
      osMeta p (DFrac.own 1) (some m) ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val #(functions munmap [])) (Val #db))
  {{ (e : w64), RET #(errnoErr e);
      db.[DB, go!"dataref"] ↦ slice.nil ∗ db.[DB, go!"data"] ↦ null ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      ((⌜e = 0⌝ ∗ osMeta p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps })) ∨
      (⌜e ≠ 0⌝ ∗
        (osMeta p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps }) ∨
         (osMeta p (DFrac.own 1) (some m) ∗ cellsR base 0 len.toNat vf)))) }}

theorem munmapM.wp_proof (hMunmap : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG)) :
    munmapM.spec (GF := GF) (hG := hG) := by
  intro db base len data dsz p m vf hlen hmap
  wp_start as ⟨#Hos, Hdr, Hd, Hsz, Hm, Hc⟩
  wp_auto
  have hne : (⟨base, len, len⟩ : GoSlice) ≠ slice.nil := by
    intro h; have := congrArg GoSlice.len h; simp [slice.nil] at this; subst this; simp at hlen
  rw [decide_eq_false hne]
  wp_auto
  wp_apply hMunmap base len p m vf hlen hmap $$ [Hm Hc] as %e Hr
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  iframe

end unmap

end bbolt
end EtcdGrove
end Perennial
