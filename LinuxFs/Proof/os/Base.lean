/-
Shared definitions of the specs of `os`'s trusted models (`TrustedCode/os.lean`, this repository's
`os`, project `bboltfs`): the typed points-to of the model's `file` and `fileStat`, and the
resource of an open `*os.File` (`ownFile`) and of the `fileStat` its `Stat` returns
(`ownFileStat`).

The model's `file` and `fileStat` are trusted types (`Code/os.toml`); goose emits no field-access
assumptions for them (`file.TypeAssumptions` has no `get_fd`/`set_fd`, unlike `File`'s
`get_file`), so `TrustedCode/os.lean` states them by hand (`file.FieldAssumptions`,
`fileStat.FieldAssumptions`), and their `IntoValTyped`, which a `GoAlloc` of one needs (in
`OpenFile` and `Stat`), takes them as instance hypotheses. Their fields are owned one by one
(`structFieldRef os.file go!"fd" inner ↦ fd`), which is all that loads and stores need.
-/
module

public import LinuxFs.GeneratedProof.os
public import LinuxFs.Proof.syscall.Base
public import GooseLang.Ext.Fs.Truncate

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

namespace os

/-- The bytes `ys` from `off` on after a `WriteAt` of `data` at `off` that wrote its first `j`
bytes (in one attempt or several), over a file of `OsMeta` `m` whose bytes there were `xs`: the
bytes below the size it leaves, each with the value of a write of the first `j` bytes
(`pwByte`), and with its candidates before the write (its old ones, for a byte below the old
size), then one or more holding the data's byte (each attempt announces it). -/
def PwOut (m : OsMeta) (off : Nat) (data : List w8) (j : Nat) (xs ys : List ByteG) : Prop :=
  ys.length = min (off + data.length) (pwSize m.size off j) - off ∧
  ∀ i (hi : i < ys.length), ys[i].1 = pwByte off data j xs (off + i) ∧
    ∃ c0 extra, ys[i].2 = c0 ++ extra ∧ extra ≠ [] ∧ (∀ q ∈ extra, q.1 = data.getD i 0) ∧
      ∀ (h : i < xs.length), c0 = xs[i].2

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : os.Assumptions]

theorem file_ty_eq : os.model.file = os.file.ty := by
  unfold os.file.ty; rfl

theorem File_ty_eq : os.model.File = os.File.ty := by
  unfold os.File.ty; rfl

theorem fileStat_ty_eq : os.model.fileStat = os.fileStat.ty := by
  unfold os.fileStat.ty; rfl

/-! The typed points-to of the model's `file` and `fileStat`, as goose emits it for a translated
struct; their `IntoValTyped` needs the struct-field facts of `TrustedCode/os.lean`
(`file.FieldAssumptions`, `fileStat.FieldAssumptions`), which goose cannot emit for a trusted
layout. -/

instance file_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"fd" go.int, go.field_decl.FieldDecl go!"name" go.string,
        go.field_decl.FieldDecl go!"off" go.int64]
      [go.field_decl.FieldDecl go!"fd" go.int, go.field_decl.FieldDecl go!"name" go.string,
        go.field_decl.FieldDecl go!"off" go.int64] :=
  ⟨rfl⟩

instance fileStat_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"name" go.string,
        go.field_decl.FieldDecl go!"size" go.int64,
        go.field_decl.FieldDecl go!"mode" io.fs.FileMode.ty]
      [go.field_decl.FieldDecl go!"name" go.string,
        go.field_decl.FieldDecl go!"size" go.int64,
        go.field_decl.FieldDecl go!"mode" io.fs.FileMode.ty] :=
  ⟨rfl⟩

noncomputable instance file_typed_pointsto : TypedPointsto (GF := GF) os.file where
  typedPointstoDef l v dq := iprop(
    "fd" ∷ typedPointsto (structFieldRef os.file go!"fd" l) v.fd' dq ∗
    "name" ∷ typedPointsto (structFieldRef os.file go!"name" l) v.name' dq ∗
    "off" ∷ typedPointsto (structFieldRef os.file go!"off" l) v.off' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance file_into_val_typed [os.file.FieldAssumptions] :
    IntoValTypedUnderlying (GF := GF) os.file os.file.underlying := by
  solve_into_val_typed_struct

noncomputable instance fileStat_typed_pointsto : TypedPointsto (GF := GF) os.fileStat where
  typedPointstoDef l v dq := iprop(
    "name" ∷ typedPointsto (structFieldRef os.fileStat go!"name" l) v.name' dq ∗
    "size" ∷ typedPointsto (structFieldRef os.fileStat go!"size" l) v.size' dq ∗
    "mode" ∷ typedPointsto (structFieldRef os.fileStat go!"mode" l) v.mode' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance fileStat_into_val_typed [os.fileStat.FieldAssumptions] :
    IntoValTypedUnderlying (GF := GF) os.fileStat os.fileStat.underlying := by
  solve_into_val_typed_struct

include sem package_sem' in
/-- The `*os.File` `f` is open on the fd `fd`, named `name`: `f` points to a `File` whose inner
`file` holds the fd (a fraction `dq` of it: `Close` writes it) and the name. -/
def ownFile (f : Loc) (fd : w64) (name : GoString) (dq : DFrac) : IProp GF :=
  iprop(∃ inner : Loc, f ↦□ (os.File.mk inner) ∗
    structFieldRef os.file go!"fd" inner ↦{dq} fd ∗
    structFieldRef os.file go!"name" inner ↦□ name)

include sem package_sem' in
/-- The `fileStat` at `fs` (what `(*File).Stat` returns, as a `FileInfo`) holds the size `sz`, and
some mode and name. -/
def ownFileStat (fs : Loc) (sz : w64) : IProp GF :=
  iprop(structFieldRef os.fileStat go!"size" fs ↦□ sz ∗
    (∃ mode : w32, structFieldRef os.fileStat go!"mode" fs ↦□ mode) ∗
    ∃ name : GoString, structFieldRef os.fileStat go!"name" fs ↦□ name)

/-- One of the ranges `rs` of bytes held (each `(off, dq, xs)`: `osBytes p off dq xs`) says that
byte `i` of the file is `b`. -/
def heldByte (rs : List (Nat × DFrac × List ByteG)) (i : Nat) (b : w8) : Prop :=
  ∃ r ∈ rs, r.1 ≤ i ∧ (r.2.2[i - r.1]?).map Prod.fst = some b

variable [syscall.Assumptions] in
/-- `f.wrapErr(op, Errno(e))` (`model.wrapErrno`) for the file whose inner `file` is `inner`: a
fresh `*PathError` as an `error`. -/
theorem wp_wrapErrno (op : GoString) (inner : Loc) (name : GoString) (e : w64)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗
      (∀ pe : Loc, Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val os.model.wrapErrno) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn HΦ
  unfold os.model.wrapErrno os.model.pathError
  rw [file_ty_eq]
  wp_auto
  wp_apply wp_errno
  iapply HΦ

end def_

/-! ## Resizes -/

theorem osMeta_eq {a b : OsMeta} (h1 : a.size = b.size) (h2 : a.lo = b.lo) (h3 : a.hi = b.hi)
    (h4 : a.maps = b.maps) (h5 : a.dlo = b.dlo) (h6 : a.dhi = b.dhi) (h7 : a.zf = b.zf)
    (h8 : a.tc = b.tc) (h9 : a.cut = b.cut) (h10 : a.cz = b.cz) (h11 : a.rz = b.rz) : a = b := by
  cases a; cases b; simp_all

theorem rsPost_tc (tr : Bool) (m : OsMeta) (tg sz' b : Nat) :
    (rsPost tr m tg sz').tc !! b =
      if inRange (min m.size tg) (rsHi tr m.size tg) b then none else m.tc !! b :=
  announce_tc m _ _ tg b

theorem rsPost_size' (tr : Bool) (m : OsMeta) (tg sz' : Nat) : (rsPost tr m tg sz').size = sz' :=
  rfl

theorem rsPost_eq (tr : Bool) (m : OsMeta) (tg sz' : Nat) :
    rsPost tr m tg sz' =
      { m.announce (min m.size tg) (rsHi tr m.size tg) tg with size := sz', cz := rsCz tr m tg } :=
  rfl

theorem rsPost_cz (tr : Bool) (m : OsMeta) (tg sz' : Nat) :
    (rsPost tr m tg sz').cz = rsCz tr m tg := rfl

/-- An `ftruncate` to `tg` leaves the page cache known zero past the size to the end of the page
holding the larger of the old and new ends. -/
theorem rsPost_cz_true (m : OsMeta) (tg sz' : Nat) :
    pageEnd (max m.size tg) ≤ (rsPost true m tg sz').cz := by
  simp only [rsPost_cz, rsCz, rsHi, if_true]; omega

/-- A resize never forgets the page cache known zero. -/
theorem le_rsPost_cz (tr : Bool) (m : OsMeta) (tg sz' : Nat) : m.cz ≤ (rsPost tr m tg sz').cz :=
  le_rsCz tr m tg

/-- `fileutil.ZeroToEnd`'s resizes from `o` (an `ftruncate` to `o`, then a growth back to the size,
by `fallocate` or `ftruncate`) leave the page cache known zero past the size to the end of its last
page: a sync then makes the zeros known from the size on (`OsMeta.synced_zf_size`). -/
theorem zeroToEnd_cz (m : OsMeta) (o : Nat) (ho : o ≤ m.size) (tr : Bool) (sz' : Nat) :
    pageEnd m.size ≤ (rsPost tr (rsPost true m o o) m.size sz').cz := by
  have h1 := rsPost_cz_true m o o
  have h2 := le_rsPost_cz tr (rsPost true m o o) m.size sz'
  rw [Nat.max_eq_left ho] at h1
  omega

/-- The cz of a resize to the size the file has, after one that landed. -/
theorem rsCz_same (tr : Bool) (m : OsMeta) (tg : Nat) :
    rsCz tr (rsPost tr m tg tg) tg = rsCz tr m tg := by
  cases tr with
  | false =>
    unfold rsCz
    simp only [Bool.false_eq_true, if_false, rsPost_size', Nat.lt_irrefl, false_and]
    rfl
  | true =>
    have h1 := rsHi_same_le true m.size tg
    have hz : (rsPost true m tg tg).zf =
        (m.announce (min m.size tg) (rsHi true m.size tg) tg).zf := rfl
    have h2 : pageEnd (((rsPost true m tg tg).zf).getD 0) ≤ rsCz true m tg := by
      rw [hz, announce_zf]
      unfold rsCz
      simp only [if_true]
      cases m.zf with
      | none => simp [pageEnd]
      | some z =>
        simp only [Option.map_some, Option.getD_some]
        simp only [rsHi, if_true]
        split <;> simp only [pageEnd] <;> omega
    have h3 : (rsPost true m tg tg).cz = rsCz true m tg := rfl
    have h4 : rsCz true (rsPost true m tg tg) tg = max (rsPost true m tg tg).cz
        (max (rsHi true tg tg) (pageEnd (((rsPost true m tg tg).zf).getD 0))) := rfl
    have h5 : rsHi true m.size tg ≤ rsCz true m tg := by
      unfold rsCz; simp only [if_true]; omega
    rw [h4]
    omega

theorem touch_dlo (m : OsMeta) (lo hi : Nat) :
    (m.touch lo hi).dlo = if hi ≤ lo then m.dlo else if m.dhi ≤ m.dlo then lo else min m.dlo lo := by
  unfold OsMeta.touch
  by_cases h1 : hi ≤ lo <;> by_cases h2 : m.dhi ≤ m.dlo <;> simp [h1, h2]

theorem touch_dhi (m : OsMeta) (lo hi : Nat) :
    (m.touch lo hi).dhi = if hi ≤ lo then m.dhi else if m.dhi ≤ m.dlo then hi else max m.dhi hi := by
  unfold OsMeta.touch
  by_cases h1 : hi ≤ lo <;> by_cases h2 : m.dhi ≤ m.dlo <;> simp [h1, h2]

/-- Announcing a part of an announced range again, with the same target, changes nothing. -/
theorem announce_sub (m : OsMeta) (lo hi lo2 hi2 tg : Nat) (hl : lo ≤ lo2) (hh : hi2 ≤ hi) :
    (m.announce lo hi tg).announce lo2 hi2 tg = m.announce lo hi tg := by
  apply osMeta_eq
  · simp
  · simp only [announce_lo]; omega
  · simp only [announce_hi]; omega
  · simp
  · simp only [announce_dlo, announce_dhi, touch_dlo, touch_dhi]
    by_cases h1 : hi ≤ lo <;> by_cases h2 : m.dhi ≤ m.dlo <;> simp only [h1, h2, if_true, if_false] <;>
      (repeat' split) <;> omega
  · simp only [announce_dhi, announce_dlo, touch_dlo, touch_dhi]
    by_cases h1 : hi ≤ lo <;> by_cases h2 : m.dhi ≤ m.dlo <;> simp only [h1, h2, if_true, if_false] <;>
      (repeat' split) <;> omega
  · simp only [announce_zf, Option.map_map]
    cases m.zf with
    | none => rfl
    | some z =>
      simp only [Option.map_some, Function.comp_def, Option.some.injEq]
      by_cases hl1 : lo < hi <;> by_cases hl2 : lo2 < hi2 <;> simp only [hl1, hl2, if_true, if_false] <;>
        omega
  · apply GMap.ext; intro b
    simp only [announce_tc]
    by_cases hb : inRange lo2 hi2 b = true
    · have hb' : inRange lo hi b = true := by
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢; omega
      simp only [hb, hb', if_true]
    · simp only [hb, Bool.false_eq_true, if_false]
  · simp
  · simp
  · simp

/-- Announcing a range again changes nothing. -/
theorem announce_idem (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).announce lo hi tg = m.announce lo hi tg :=
  announce_sub m lo hi lo hi tg (Nat.le_refl _) (Nat.le_refl _)

/-- The size does not matter to an announce. -/
theorem announce_setSize (X : OsMeta) (s lo hi tg : Nat) :
    ({ X with size := s } : OsMeta).announce lo hi tg = { X.announce lo hi tg with size := s } := by
  apply osMeta_eq <;> simp [announce_dlo, announce_dhi, touch_dlo, touch_dhi, announce_tc]
  apply GMap.ext; intro b; simp [announce_tc]

theorem announce_setSizeCz (X : OsMeta) (s c lo hi tg : Nat) :
    ({ X with size := s, cz := c } : OsMeta).announce lo hi tg =
      { X.announce lo hi tg with size := s, cz := c } := by
  apply osMeta_eq <;> simp [announce_dlo, announce_dhi, touch_dlo, touch_dhi, announce_tc]
  apply GMap.ext; intro b; simp [announce_tc]

/-- A resize to the size a file has, after one that landed, changes nothing. -/
theorem rsPost_rsPost (tr : Bool) (m : OsMeta) (tg : Nat) :
    rsPost tr (rsPost tr m tg tg) tg tg = rsPost tr m tg tg := by
  rw [rsPost_eq tr (rsPost tr m tg tg), rsPost_size', rsCz_same, rsPost_eq tr m tg tg,
    announce_setSizeCz, announce_sub _ _ _ _ _ _ (by omega) (by simpa using rsHi_same_le tr m.size tg)]

theorem announce_rsPost (tr : Bool) (m : OsMeta) (tg : Nat) :
    (rsPost tr m tg tg).announce (min (rsPost tr m tg tg).size tg) (rsHi tr (rsPost tr m tg tg).size tg)
      tg = rsPost tr m tg tg := by
  rw [rsPost_size', rsPost_eq tr m tg tg, announce_setSizeCz,
    announce_sub _ _ _ _ _ _ (by omega) (by simpa using rsHi_same_le tr m.size tg)]

/-- The page cache known zero after a resize does not depend on its own announcement. -/
theorem rsCz_announce (tr : Bool) (m : OsMeta) (tg : Nat) :
    rsCz tr (m.announce (min m.size tg) (rsHi tr m.size tg) tg) tg = rsCz tr m tg := by
  unfold rsCz
  simp only [announce_size, announce_cz, announce_zf]
  cases m.zf with
  | none => rfl
  | some z =>
    simp only [Option.map_some, Option.getD_some]
    cases tr
    · simp only [rsHi, Bool.false_eq_true, if_false]
      by_cases h : m.size < tg
      · have e1 : min m.size tg = m.size := by omega
        have e2 : max m.size tg = tg := by omega
        have e3 : max (max z tg) tg = max z tg := by omega
        simp only [e1, e2, h, if_true, e3]
      · simp only [h, _root_.false_and, if_false]
    · simp only [rsHi, if_true]
      split
      · simp only [pageEnd]; omega
      · rfl

theorem rsPost_announce (tr : Bool) (m : OsMeta) (tg sz' : Nat) :
    rsPost tr (m.announce (min m.size tg) (rsHi tr m.size tg) tg) tg sz' = rsPost tr m tg sz' := by
  unfold rsPost
  rw [announce_size, announce_idem, rsCz_announce]

section resize
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]

/-- `zeroToEnd_cz` with the sync: zeros known from the size on. -/
theorem zeroToEnd_synced_zf [go.BasicIntoValInj] (m : OsMeta) (o : Nat) (ho : o ≤ m.size) (tr : Bool) :
    (rsPost tr (rsPost true m o o) m.size m.size).synced.zf = some m.size :=
  OsMeta.synced_zf_size _ (zeroToEnd_cz m o ho tr m.size)
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

theorem mcellsAny_nil (M : GMap Loc Nat) (lo hi : Nat) (h : hi ≤ lo) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  unfold mcellsAny
  refine (BigSepM.bigSepM_emp (m := M)).2.trans (BigSepM.bigSepM_mono fun _ => ?_)
  iintro -
  iexists (fun _ => default)
  unfold cellsR
  rw [show min hi _ - min lo _ = 0 by omega]
  simp only [List.range'_zero]
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- A resize of the file `p` from `m` to the size `tg` that landed (perhaps after attempts that
did not): its `OsMeta` as the resize leaves it (`rsPost`), the bytes it grew the file over,
zeros, and the client's halves of the cells over the range, showing the new contents. -/
def ftDone (p : Ino) (m : OsMeta) (tg : Nat) : IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = tg - m.size⌝ ∗
    osMeta p (DFrac.own 1) (rsPost true m tg tg) ∗
    osBytes p m.size (DFrac.own 1) (zs.map (fun c => ((0 : w8), c))) ∗
    mcells m.maps (min m.size tg) (rsHi true m.size tg) (rsCell tg))

/-- A resize of the file `p` from `m` to `tg` that did not land: its `OsMeta` as its first step
left it, the bytes it would have cut off (`xs`'s values, with new candidates) and the client's
halves of the cells over the range. -/
def ftUndone (p : Ino) (m : OsMeta) (tg : Nat) (xs : List ByteG) : IProp GF :=
  iprop(∃ xs' : List ByteG, ⌜xs'.map Prod.fst = xs.map Prod.fst⌝ ∗
    osMeta p (DFrac.own 1) (m.announce (min m.size tg) (rsHi true m.size tg) tg) ∗
    osBytes p (min m.size tg) (DFrac.own 1) xs' ∗
    mcellsAny m.maps (min m.size tg) (rsHi true m.size tg))

end resize
end os

end Perennial
