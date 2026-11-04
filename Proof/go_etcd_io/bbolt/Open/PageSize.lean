/-
`Open`'s page-size probe (U11, `notes/bbolt-proof-plan.md`; D18): `db.getPageSize()` and its two
helpers in `Open`'s owned phase (every field of `db` owned, no lock invariant yet), over a file
whose meta slots are a committed state's (`fileHolds`' `C`, `C.metaOk`): the page size is 4096, or
an error (`fmt` formats it).
-/
module

public import Proof.go_etcd_io.bbolt.Open.ReadHeld
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Mmap.RemapGaps
public import Proof.go_etcd_io.bbolt.Mmap.AllocPage
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Spec.go_etcd_io.bbolt.internal.common.Meta__PageSize
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes
public import Perennial.Proof.io

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.pageInBuffer(b, id)` with the page size owned (at any fraction: `Open`'s owned phase,
before the page size is final). -/
abbrev DB.pageInBuffer.spec_own : Prop :=
  ∀ (db : Loc) (b : GoSlice) (id : w64) (dq : DFrac),
  id.toNat * 4096 < b.len.toNat → b.len.toNat < 2 ^ 63 → 0 < b.ptr.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"pageSize"] ↦{dq} W64 4096 }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"pageInBuffer")) (Val #b))
      (Val #id))
  {{ RET #(b.ptr +ₗ ((id.toNat * 4096 : Nat) : Int)); db.[DB, go!"pageSize"] ↦{dq} W64 4096 }}

omit hos in
theorem DB.pageInBuffer.wp_proof_own : DB.pageInBuffer.spec_own (GF := GF) (hG := hG) := by
  intro db b id dq Hlt Hlen Hpos
  wp_start as Hps
  wp_auto
  have hz : sint.Z (id * W64 4096) = ((id.toNat * 4096 : Nat) : Int) := by word
  have hb : sint.Z b.len = (b.len.toNat : Int) := by word
  rw [hz, hb, ite_eq_left_of_eq_true _ _ (eq_true (⟨by omega, by omega⟩ : _ ∧ _)),
    sliceIndexRef_byte _ _ Hpos (by omega)]
  wp_auto
  iapply HΦ; iexact Hps

/-- **`db.getPageSizeFromFirstMeta()`**, the file's bytes `xs` held from offset 0 (at least a
page): the page size of the meta in page 0, or `ErrInvalid` if it is not valid, or a read error (a
`*PathError`). -/
abbrev DB.getPageSizeFromFirstMeta.spec_own : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqdb dqf dq dqb : DFrac) (d : OsFd)
    (xs : List (w8 × Bool)),
  d.readable = true → d.path = p → 4096 ≤ xs.length → xs.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      fileOwn f fd p dqf ∗ osFd fd dq d ∗ osBytes p 0 dqb xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"getPageSizeFromFirstMeta")) (Val #()))
  {{ (sz : w64) (cr : Bool) (err : GoInterface), RET (PairV (PairV #sz #cr) #err);
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      fileOwn f fd p dqf ∗ osFd fd dq d ∗ osBytes p 0 dqb xs ∗
      ((⌜err = interface.nil ∧ metaValid (metaOf (bytesAt (xs.map Prod.fst) 0 4096)) ∧
          sz = W64 ((metaOf (bytesAt (xs.map Prod.fst) 0 4096)).pageSize'.toNat : Int)⌝) ∨
       (globalAddr go_etcd_io.bbolt.errors.ErrInvalid ↦□ err ∗
          ⌜¬ metaValid (metaOf (bytesAt (xs.map Prod.fst) 0 4096))⌝) ∨
       (⌜∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ ∗
          fmtErrorOk err)) }}

theorem DB.getPageSizeFromFirstMeta.wp_proof_own
    (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG))
    (hPageSize : internal.common.Meta.PageSize.spec (GF := GF) (hG := hG)) :
    DB.getPageSizeFromFirstMeta.spec_own (GF := GF) (hG := hG) := by
  intro db f fd p dqdb dqf dq dqb d xs hrd hp hlen hx
  subst hp
  wp_start as ⟨#Hos, Hf, Hps, Hfo, Hfd, Hb⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
  icases Hei with ⟨%_, #-, %_, -, #HEi, -⟩
  unfold go_etcd_io.bbolt.errors.bboltErrVar
  icases HEi with ⟨%ei0, #HEi, -⟩
  wp_auto
  ihave Hsl := slice_array (GF := GF) buf_ptr _ _
    (by rw [show (zero_val (GoArray w8 4096)).arr = List.replicate 4096 (W8 0) from rfl, List.length_replicate]; omega) $$ buf
  rw [show (zero_val (GoArray w8 4096)).arr = List.replicate 4096 (W8 0) from rfl,
    show W64 (4096 : Int) = W64 4096 from rfl] at *
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 4096 - W64 0 = W64 4096 from rfl]
  wp_apply os.File.ReadAt.wp_held hRead f fd d.path dqf (slice.mk buf_ptr (W64 4096) (W64 4096))
    (List.replicate 4096 (W8 0)) (W64 0) dq dqb d xs _ hrd
    (by decide) (by rw [List.length_replicate]; omega)
    (by rw [List.length_replicate, show (W64 0).toNat = 0 from rfl]; omega) hx $$ [Hfo Hsl Hfd Hb] as %n %err
    ⟨Hfo, Hfd, Hb, %vs', Hsl, %hr, #Hek⟩
  · iframe; iframe #; rw [← fileOwn_eq]; iexact Hfo
  rw [List.length_replicate, show (W64 0).toNat = 0 from rfl, List.drop_zero] at hr
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨pe, rfl⟩
  · wp_auto
    have hX : (List.take 4096 (List.map Prod.fst xs)).length = 4096 := by simp; omega
    ihave %Hp := ownSlice_ptr_pos _ _ _ (by intro h; rw [h] at hX; simp at hX) $$ Hsl
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
      show W64 4096 - W64 0 = W64 4096 from rfl]
    wp_apply DB.pageInBuffer.wp_proof_own db (slice.mk buf_ptr (W64 4096) (W64 4096)) (W64 0) dqdb
      (by simp) (by simp) Hp $$ [Hps] as Hps
    · iframe
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hp $$ Hsl
      with ⟨Hbs, Hback⟩
    rw [flatMap_encode_w8]
    icases persistent_entails_left (internal.common.bytesPointsto_in_bounds _ _ _
      (by intro h; rw [h] at hX; simp at hX)) $$ Hbs with ⟨Hbs, %Hib⟩
    simp only [hX] at Hib
    wp_apply hMeta (buf_ptr +ₗ ((0 : Nat) : Int)) (by simpa [Loc.add] using Hp)
      (by simp [Loc.add]; omega)
    try wp_auto
    have e16 : buf_ptr +ₗ ((0 : Nat) : Int) +ₗ 16 = buf_ptr +ₗ ((16 : Nat) : Int) := by
      simp [Loc.add]
    rw [e16]
    icases bytesPointsto_view_read (V := Meta) buf_ptr (DFrac.own 1) _ 16 _ rfl
      (by rw [hX]; omega) Hp $$ Hbs with ⟨HM, HMb⟩
    wp_apply hValidate _ _ _ (by simp [Loc.add]; omega) $$ [HM] as %e1 ⟨HM, %He1⟩
    · iframe
    have hmeta : (decode ((List.take 4096 (List.map Prod.fst xs)).drop 16 |>.take 64) : Meta) =
        metaOf (bytesAt (List.map Prod.fst xs) 0 4096) := rfl
    rw [hmeta] at He1 ⊢
    cases e1 with
    | nil =>
      wp_auto
      wp_apply hPageSize _ _ _ $$ [HM] as HM
      · iframe
      try wp_auto
      iapply HΦ
      rw [fileOwn_eq]
      iframe
      ileft
      ipureintro
      exact ⟨rfl, He1.1 rfl, by word⟩
    | ok ei =>
      wp_auto
      iapply HΦ
      rw [fileOwn_eq]
      iframe
      iright; ileft
      iframe HEi
      ipureintro
      exact fun h => nomatch He1.2 h
  · have hty : (go.GoType.PointerType io.fs.PathError.ty = go.GoType.PointerType
        _root_.Perennial.errors.errorString.ty) = False := by
      apply propext; constructor
      · intro h; unfold io.fs.PathError.ty _root_.Perennial.errors.errorString.ty at h; simp at h
      · intro h; exact h.elim
    wp_auto
    iapply HΦ
    rw [fileOwn_eq]
    iframe
    iright; iright
    isplitr
    · ipureintro; exact ⟨pe, rfl⟩
    · iapply fmtErrorOkOrNil_ne (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)
        (by intro h; cases h) $$ Hek

end spec

end bbolt
end EtcdGrove
end Perennial
