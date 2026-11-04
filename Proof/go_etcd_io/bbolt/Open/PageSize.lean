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

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

omit [GooseExts] in
/-- The probe positions `getPageSizeFromSecondMeta` reaches on a well-formed file (1, 2, 4 KiB). -/
theorem shl1024 (j : w64) (h : j.toNat ≤ 2) :
    (W64 1024 <<< j) = W64 ((1024 * 2 ^ j.toNat : Nat) : Int) := by
  obtain h0 | h1 | h2 : j.toNat = 0 ∨ j.toNat = 1 ∨ j.toNat = 2 := by omega
  · have : j = W64 0 := BitVec.eq_of_toNat_eq (by simp [h0])
    subst this; rfl
  · have : j = W64 1 := BitVec.eq_of_toNat_eq (by simp [h1])
    subst this; rfl
  · have : j = W64 2 := BitVec.eq_of_toNat_eq (by simp [h2])
    subst this; rfl

/-- A pointer error is `errPtrTyped`. -/
theorem errPtrTyped_mkOk (T : go.GoType) (l : Loc) [GoGlobalContext] :
    errPtrTyped (interface.mkOk (go.GoType.PointerType T) #l) := by
  intro ii h T' hT
  unfold interface.mkOk at h
  cases h
  exact ⟨l, rfl⟩

end pure

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

/-- **`db.getPageSizeFromSecondMeta()`**, the file's bytes `xs` held from offset 0 with its
`OsMeta` (at least two pages), over a file whose probes at 1 and 2 KiB hold no valid meta and whose
page 1 holds a valid meta of page size 4096 (`C.metaOk` with meta 0 invalid): the page size 4096,
or an error (`Stat`'s, or a read's `*PathError`). -/
abbrev DB.getPageSizeFromSecondMeta.spec_own : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqdb dqf dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta)
    (xs : List (w8 × Bool)),
  d.readable = true → d.path = p → xs.length = m.size → 8192 ≤ m.size → m.size < 2 ^ 62 →
  ¬ metaValid (metaOf (bytesAt (xs.map Prod.fst) 1024 4096)) →
  ¬ metaValid (metaOf (bytesAt (xs.map Prod.fst) 2048 4096)) →
  metaValid (metaOf (bytesAt (xs.map Prod.fst) 4096 4096)) →
  (metaOf (bytesAt (xs.map Prod.fst) 4096 4096)).pageSize'.toNat = 4096 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      fileOwn f fd p dqf ∗ osFd fd dq d ∗ osMeta p dqm (some m) ∗ osBytes p 0 dqb xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"getPageSizeFromSecondMeta")) (Val #()))
  {{ (sz : w64) (cr : Bool) (err : GoInterface), RET (PairV (PairV #sz #cr) #err);
      db.[DB, go!"file"] ↦{dqdb} f ∗ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 ∗
      fileOwn f fd p dqf ∗ osFd fd dq d ∗ osMeta p dqm (some m) ∗ osBytes p 0 dqb xs ∗
      ((⌜err = interface.nil ∧ sz = W64 4096⌝) ∨
       (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err)) }}

theorem DB.getPageSizeFromSecondMeta.wp_proof_own
    (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG))
    (hPageSize : internal.common.Meta.PageSize.spec (GF := GF) (hG := hG)) :
    DB.getPageSizeFromSecondMeta.spec_own (GF := GF) (hG := hG) := by
  intro db f fd p dqdb dqf dq dqm dqb d m xs hrd hp hxl hsz hsz' hv0 hv1 hv2 hps2
  subst hp
  wp_start as ⟨#Hos, Hf, Hps, Hfo, Hfd, Hm, Hb⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  wp_auto
  wp_apply hStat f fd d.path dqf dq dqm d m $$ [Hfo Hfd Hm] as %fi %err ⟨Hfo, Hfd, Hm, Hr, #Hek⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  try wp_auto
  icases Hr with (⟨%fs, %Hfs, Hst⟩ | %Hfs)
  · obtain ⟨rfl, rfl⟩ := Hfs
    wp_auto
    wp_apply hSize fs (W64 (m.size : Int)) $$ [Hst] as Hst
    · iframe
    try wp_auto
    ihave IH : (∃ (j : w64) (cr : Bool), "i" ∷ i_ptr ↦ j ∗ "metaCanRead" ∷ metaCanRead_ptr ↦ cr ∗
        "%Hj" ∷ ⌜j.toNat ≤ 2⌝ ∗ "Hfo" ∷ os.ownFile f fd d.path dqf ∗ "Hfd" ∷ osFd fd dq d ∗
        "Hb" ∷ osBytes d.path 0 dqb xs ∗ "Hps" ∷ db.[DB, go!"pageSize"] ↦{dqdb} W64 4096 :
        IProp GF) $$ [i metaCanRead Hfo Hfd Hb Hps]
    · iexists W64 0, zero_val Bool
      simp only [named]
      iframe
      ipureintro; decide
    wp_for IH
    have hj14 : sint.Z j ≤ sint.Z (W64 14) := by word
    rw [decide_eq_true hj14]
    simp only [↓reduceIte]
    try wp_auto
    have hshl := shl1024 j Hj
    have hP : 1024 * 2 ^ j.toNat ≤ 4096 := by
      rcases (by omega : j.toNat = 0 ∨ j.toNat = 1 ∨ j.toNat = 2) with h | h | h <;> simp [h]
    generalize hPd : 1024 * 2 ^ j.toNat = P at hshl hP
    rw [hshl]
    have hbrk : ¬ sint.Z (W64 (m.size : Int) - W64 1024) ≤ sint.Z (W64 (P : Int)) := by word
    rw [decide_eq_false hbrk]
    try wp_auto
    ihave Hsl := slice_array (GF := GF) buf_ptr _ _
      (by rw [show (zero_val (GoArray w8 4096)).arr = List.replicate 4096 (W8 0) from rfl,
        List.length_replicate]; omega) $$ buf
    rw [show (zero_val (GoArray w8 4096)).arr = List.replicate 4096 (W8 0) from rfl,
      show W64 (4096 : Int) = W64 4096 from rfl] at *
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
      show W64 4096 - W64 0 = W64 4096 from rfl]
    have hPn : (W64 (P : Int)).toNat = P := by word
    wp_apply os.File.ReadAt.wp_held hRead f fd d.path dqf (slice.mk buf_ptr (W64 4096) (W64 4096))
      (List.replicate 4096 (W8 0)) (W64 (P : Int)) dq dqb d xs _ hrd
      (by word) (by rw [List.length_replicate]; omega)
      (by rw [List.length_replicate, hPn]; omega) (by omega) $$ [Hfo Hsl Hfd Hb] as %n %err
      ⟨Hfo, Hfd, Hb, %vs', Hsl, %hr, #Hek2⟩
    · iframe; iframe #
    rw [List.length_replicate, hPn] at hr
    rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨pe, rfl⟩
    · wp_auto
      have hX : (List.take 4096 (List.drop P (List.map Prod.fst xs))).length = 4096 := by
        simp; omega
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
      have hmeta : (decode ((List.take 4096 (List.drop P (List.map Prod.fst xs))).drop 16
          |>.take 64) : Meta) = metaOf (bytesAt (List.map Prod.fst xs) P 4096) := rfl
      rw [hmeta] at He1 ⊢
      cases e1 with
      | nil =>
        have hv := He1.1 rfl
        have hj2 : P = 4096 := by
          subst hPd
          rcases (by omega : j.toNat = 0 ∨ j.toNat = 1 ∨ j.toNat = 2) with h | h | h <;>
            simp [h] at hv ⊢ <;> first | exact absurd hv hv0 | exact absurd hv hv1
        subst hj2
        wp_auto
        wp_apply hPageSize _ _ _ $$ [HM] as HM
        · iframe
        try wp_auto
        iapply wp_for_post_return
        wp_auto
        iapply HΦ
        rw [fileOwn_eq]
        iframe
        ileft
        ipureintro
        refine ⟨rfl, ?_⟩
        have h4 : uint.Z (metaOf (bytesAt (List.map Prod.fst xs) 4096 4096)).pageSize' = 4096 := by
          have := hps2; word
        show W64 (uint.Z (metaOf (bytesAt (List.map Prod.fst xs) 4096 4096)).pageSize') = W64 4096
        rw [h4]
      | ok ei =>
        have hj2 : j.toNat < 2 := by
          apply Classical.byContradiction; intro hc
          have : P = 4096 := by subst hPd; rw [show j.toNat = 2 by omega]
          subst this
          exact nomatch He1.2 hv2
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, true
        simp only [named]
        iframe
        ipureintro
        word
    · wp_auto
      iapply wp_for_post_return
      wp_auto
      iapply HΦ
      rw [fileOwn_eq]
      iframe
      iright
      isplitr
      · ipureintro; exact ⟨(by intro h; cases h), errPtrTyped_mkOk _ _⟩
      · iapply fmtErrorOkOrNil_ne (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)
          (by intro h; cases h) $$ Hek2
  · obtain ⟨hne, rfl⟩ := Hfs
    cases err with
    | nil => exact absurd rfl hne
    | ok ii =>
      ihave #Hek : fmtErrorOk (GF := GF) (GoInterface.ok ii) $$ []
      · iapply fmtErrorOkOrNil_ne _ hne $$ Hek
      ihave %Hpt := fmtErrorOk_errPtrTyped _ $$ Hek
      wp_auto
      iapply HΦ
      rw [fileOwn_eq]
      iframe
      iright
      iframe Hek
      ipureintro; exact ⟨hne, Hpt⟩

end spec

end bbolt
end EtcdGrove
end Perennial
