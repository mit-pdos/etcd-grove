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

public import GeneratedProof.os
public import Proof.syscall.Base
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
    EqualsUnfold [go.field_decl.FieldDecl go!"size" go.int64]
      [go.field_decl.FieldDecl go!"size" go.int64] :=
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
    "size" ∷ typedPointsto (structFieldRef os.fileStat go!"size" l) v.size' dq ∗
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
/-- The `fileStat` at `fs` (what `(*File).Stat` returns, as a `FileInfo`) holds the size `sz`. -/
def ownFileStat (fs : Loc) (sz : w64) : IProp GF :=
  iprop(structFieldRef os.fileStat go!"size" fs ↦□ sz)

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
    (h8 : a.tc = b.tc) (h9 : a.cut = b.cut) : a = b := by
  cases a; cases b; simp_all

theorem rsPost_tc (m : OsMeta) (tg sz' b : Nat) :
    (rsPost m tg sz').tc !! b =
      if inRange (min m.size tg) (max m.size tg) b then none else m.tc !! b :=
  announce_tc m _ _ tg b

theorem rsPost_size' (m : OsMeta) (tg sz' : Nat) : (rsPost m tg sz').size = sz' := rfl

theorem touch_dlo (m : OsMeta) (lo hi : Nat) :
    (m.touch lo hi).dlo = if hi ≤ lo then m.dlo else if m.dhi ≤ m.dlo then lo else min m.dlo lo := by
  unfold OsMeta.touch
  by_cases h1 : hi ≤ lo <;> by_cases h2 : m.dhi ≤ m.dlo <;> simp [h1, h2]

theorem touch_dhi (m : OsMeta) (lo hi : Nat) :
    (m.touch lo hi).dhi = if hi ≤ lo then m.dhi else if m.dhi ≤ m.dlo then hi else max m.dhi hi := by
  unfold OsMeta.touch
  by_cases h1 : hi ≤ lo <;> by_cases h2 : m.dhi ≤ m.dlo <;> simp [h1, h2]

/-- Announcing a range again changes nothing. -/
theorem announce_idem (m : OsMeta) (lo hi tg : Nat) :
    (m.announce lo hi tg).announce lo hi tg = m.announce lo hi tg := by
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
      by_cases hl : lo < hi <;> simp [hl, Nat.max_assoc]
  · apply GMap.ext; intro b
    simp only [announce_tc]
    split <;> rfl
  · simp [rsPost]

/-- A resize to the size a file has, after one that landed, changes nothing. -/
theorem rsPost_rsPost (m : OsMeta) (tg : Nat) : rsPost (rsPost m tg tg) tg tg = rsPost m tg tg := by
  apply osMeta_eq
  · rfl
  · simp only [rsPost, announce_lo]; omega
  · simp only [rsPost, announce_hi]; omega
  · simp [rsPost]
  · simp only [rsPost, announce_dlo]; unfold OsMeta.touch; simp
  · simp only [rsPost, announce_dhi]; unfold OsMeta.touch; simp
  · simp [rsPost, announce_zf, Function.comp_def]
  · apply GMap.ext; intro b
    rw [rsPost_tc, rsPost_size']
    simp only [Nat.min_self, Nat.max_self]
    rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)]
  · simp [rsPost]

theorem announce_rsPost (m : OsMeta) (tg : Nat) :
    (rsPost m tg tg).announce (min (rsPost m tg tg).size tg) (max (rsPost m tg tg).size tg) tg =
      rsPost m tg tg := by
  apply osMeta_eq
  · simp [rsPost]
  · simp only [rsPost, announce_lo]; omega
  · simp only [rsPost, announce_hi]; omega
  · simp [rsPost]
  · simp only [rsPost, announce_dlo]; unfold OsMeta.touch; simp
  · simp only [rsPost, announce_dhi]; unfold OsMeta.touch; simp
  · simp [rsPost, announce_zf, Function.comp_def]
  · apply GMap.ext; intro b
    rw [announce_tc]
    simp only [rsPost_size', Nat.min_self, Nat.max_self]
    rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)]
  · simp [rsPost]

theorem rsPost_announce (m : OsMeta) (tg sz' : Nat) :
    rsPost (m.announce (min m.size tg) (max m.size tg) tg) tg sz' = rsPost m tg sz' := by
  unfold rsPost
  rw [announce_size, announce_idem]

section resize
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
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
    osMeta p (DFrac.own 1) (rsPost m tg tg) ∗
    osBytes p m.size (DFrac.own 1) (zs.map (fun c => ((0 : w8), c))) ∗
    mcells m.maps (min m.size tg) (max m.size tg) (rsCell tg))

/-- A resize of the file `p` from `m` to `tg` that did not land: its `OsMeta` as its first step
left it, the bytes it would have cut off (`xs`'s values, with new candidates) and the client's
halves of the cells over the range. -/
def ftUndone (p : Ino) (m : OsMeta) (tg : Nat) (xs : List ByteG) : IProp GF :=
  iprop(∃ xs' : List ByteG, ⌜xs'.map Prod.fst = xs.map Prod.fst⌝ ∗
    osMeta p (DFrac.own 1) (m.announce (min m.size tg) (max m.size tg) tg) ∗
    osBytes p (min m.size tg) (DFrac.own 1) xs' ∗
    mcellsAny m.maps (min m.size tg) (max m.size tg))

end resize
end os

end Perennial
