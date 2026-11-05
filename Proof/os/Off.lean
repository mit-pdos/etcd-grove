/-
Specs of `os`'s trusted models of the file offset (`TrustedCode/os.lean`'s `Seek`, `Write`,
`Read`, over the `off` field of the trusted `file`): `os.ownOff f o` owns the offset of the `*File`
`f`, `o`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base
public import Spec.os.File__WriteAt
public import GooseLang.Ext.OsFs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions]

/-- The offset of the `*File` `f` is `o` (its `file`'s `off` field, whole). -/
def os.ownOff (f : Loc) (o : w64) : IProp GF :=
  iprop(∃ inner : Loc, f ↦□ (os.File.mk inner) ∗ structFieldRef os.file go!"off" inner ↦ o)

/-- `f.Seek(off, io.SeekStart)`, `0 ≤ off < 2^62`: the offset becomes `off`. -/
theorem os.File.Seek.wp_start (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (o off : w64)
    (h0 : 0 ≤ off.toInt) (hmax : off.toInt < 2 ^ 62) :
    {{ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Seek")) (Val #off))
        (Val #(W64 0)))
    {{ RET (PairV #off #GoInterface.nil); os.ownFile f fd name dqf ∗ os.ownOff f off }} := by
  unfold os.ownFile os.ownOff
  wp_start as ⟨⟨%inner, #Hf, Hfd, #Hn⟩, ⟨%inner', #Hf', Ho⟩⟩
  icombine Hf Hf' gives %hin
  cases hin
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl, show W64 0 + off = off from BitVec.zero_add off]
  have hz : sint.Z (W64 0) = 0 := rfl
  have hm : sint.Z (W64 0x4000000000000000) = 2 ^ 62 := rfl
  try rw [decide_eq_false (show ¬ sint.Z off < sint.Z (W64 0) by simp only [sint.Z] at *; omega)]
  try wp_auto
  try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z off by
    rw [hm]; simp only [sint.Z]; omega)]
  try wp_auto
  try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 0) by rw [hm, hz]; omega)]
  try wp_auto
  try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z off by
    rw [hm]; simp only [sint.Z]; omega)]
  try wp_auto
  iapply HΦ
  isplitl [Hfd]
  · iexists inner; iframe; isplitl [] <;> iassumption
  · iexists inner; iframe; iassumption

/-- `f.Seek(0, io.SeekCurrent)`, the offset `0 ≤ o < 2^62`: `o`, unchanged. -/
theorem os.File.Seek.wp_cur (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (o : w64)
    (h0 : 0 ≤ o.toInt) (hmax : o.toInt < 2 ^ 62) :
    {{ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Seek")) (Val #(W64 0)))
        (Val #(W64 1)))
    {{ RET (PairV #o #GoInterface.nil); os.ownFile f fd name dqf ∗ os.ownOff f o }} := by
  unfold os.ownFile os.ownOff
  wp_start as ⟨⟨%inner, #Hf, Hfd, #Hn⟩, ⟨%inner', #Hf', Ho⟩⟩
  icombine Hf Hf' gives %hin
  cases hin
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl]
  have hz : sint.Z (W64 0) = 0 := rfl
  have hm : sint.Z (W64 0x4000000000000000) = 2 ^ 62 := rfl
  try rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by simp only [sint.Z] at *; omega)]
  try wp_auto
  try rw [show o + W64 0 = o from BitVec.add_zero o]
  try rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by simp only [sint.Z] at *; omega)]
  try wp_auto
  try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z o by
    rw [hm]; simp only [sint.Z]; omega)]
  try wp_auto
  try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z o by
    rw [hm]; simp only [sint.Z]; omega)]
  try wp_auto
  try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 0) by rw [hm, hz]; omega)]
  try wp_auto
  iapply HΦ
  isplitl [Hfd]
  · iexists inner; iframe; isplitl [] <;> iassumption
  · iexists inner; iframe; iassumption

/-- `f.Seek(0, io.SeekEnd)` of a file of size below `2^62`, with a fraction of its `OsMeta`: the
size, the offset set to it; or an error, the offset unchanged. -/
theorem os.File.Seek.wp_end (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (o : w64)
    (dq dqm : DFrac) (d : OsFd) (m : OsMeta) (hsz : m.size < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path dqm (some m) }}
      (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Seek")) (Val #(W64 0)))
        (Val #(W64 2)))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); os.ownFile f fd name dqf ∗
        osFd fd dq d ∗ osMeta d.path dqm (some m) ∗
        ((⌜n = W64 m.size ∧ err = interface.nil⌝ ∗ os.ownOff f (W64 m.size)) ∨
         (⌜err ≠ interface.nil⌝ ∗ os.ownOff f o)) }} := by
  unfold os.ownFile os.ownOff
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, ⟨%inner', #Hf', Ho⟩, Hosfd, Hm⟩
  icombine Hf Hf' gives %hin
  cases hin
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFstat fd dq dqm d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %sz %e %hr Hosfd Hm
  rcases hr with ⟨rfl, rfl⟩ | ⟨he, rfl⟩
  · rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    rw [show os.model.offMax = W64 0x4000000000000000 from rfl,
      show W64 m.size + W64 0 = W64 m.size from BitVec.add_zero _]
    have hz : sint.Z (W64 0) = 0 := rfl
    have hm : sint.Z (W64 0x4000000000000000) = 2 ^ 62 := rfl
    have hs : sint.Z (W64 (m.size : Int)) = m.size := by
      show BitVec.toInt _ = _
      rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
    try rw [decide_eq_false (show ¬ sint.Z (W64 (m.size : Int)) < sint.Z (W64 0) by rw [hs, hz]; omega)]
    try wp_auto
    try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 (m.size : Int)) by
      rw [hm, hs]; omega)]
    try wp_auto
    try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 (m.size : Int)) by
      rw [hm, hs]; omega)]
    try wp_auto
    try rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (W64 0) by rw [hm, hz]; omega)]
    try wp_auto
    iapply HΦ
    iframe Hosfd Hm
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    · ileft
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexists inner; iframe; iassumption
  · have he' : ¬ e = W64 0 := he
    simp only [decide_eq_false he', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe Hosfd Hm
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    · iright
      isplitr
      · ipureintro; intro h; cases h
      iexists inner; iframe; iassumption

/-- `f.Write(b)` at the offset `o` (`0 ≤ o`, `o + len(b) < 2^62`), over `WriteAt`'s spec at `o`:
`WriteAt`'s result and state; the offset moves past `b` on success, and becomes unknown (-1) on
an error. -/
theorem os.File.Write.wp_spec (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (o : w64) (dq : DFrac) (d : OsFd) (q : Qp) (m : OsMeta) (xs : List (w8 × Bool))
    (hwr : d.writable = true) (h0 : 0 ≤ o.toInt) (hn : 0 < data.length)
    (hn2 : data.length ≤ 0x40000000)
    (hxs : xs.length = min (o.toNat + data.length) m.size - min o.toNat m.size)
    (hq : m.size < o.toNat + data.length → q = 1) (hmax : o.toInt + data.length < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path (DFrac.own q) (some m) ∗
        osBytes (GF := GF) d.path (min o.toNat m.size) (DFrac.own 1) xs ∗
        mcellsAny (GF := GF) m.maps (min o.toNat m.size) (o.toNat + data.length) }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Write")) (Val #sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
        (∃ (j : Nat) (ys : List (w8 × Bool)) (h : Nat),
          ⌜j ≤ data.length ∧
            ys.map Prod.fst = (pwBytes m.size o.toNat data j xs).map Prod.fst ∧ m.hi ≤ h ∧
            ((j = data.length ∧ n = W64 data.length ∧ err = interface.nil) ∨
             (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
          osMeta d.path (DFrac.own q) (some { m with size := pwSize m.size o.toNat j, hi := h }) ∗
          osBytes d.path (min o.toNat m.size) (DFrac.own 1) ys ∗
          mcellsAny m.maps (min o.toNat m.size) (o.toNat + data.length)) ∗
        ((⌜err = interface.nil⌝ ∗ os.ownOff f (o + W64 data.length)) ∨
         (⌜err ≠ interface.nil⌝ ∗ os.ownOff f (W64 (-1)))) }} := by
  unfold os.ownOff
  wp_start as ⟨#Hinv, Hf, ⟨%inner, #Hfi, Ho⟩, Hsl, Hosfd, Hm, Hbs, Hmc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hfi
  iStructNamed Hf2
  icases ownSlice_len sl _ data $$ Hsl with %Hlen
  wp_auto
  have hsl : sl.len = W64 data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega)]
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl, hsl]
  try wp_auto
  have hsum : sint.Z (o + W64 (data.length : Int)) = o.toInt + data.length := by
    simp only [sint.Z]; word
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (o + W64 (data.length : Int)) by
    rw [hsum, show sint.Z (W64 0x4000000000000000) = 2 ^ 62 from rfl]; omega)]
  wp_auto
  wp_apply wp_WriteAt f fd name dqf sl data dqs o dq d q m xs hwr h0 hn hn2 hxs hq
    $$ [Hinv Hf Hsl Hosfd Hm Hbs Hmc] as %n %err ⟨Hf, Hsl, Hosfd, %j, %ys, %h, %Hres, Hm, Hbs, Hmc⟩
  · iframe; iexact Hinv
  cases err with
  | nil =>
    wp_auto
    iapply HΦ
    iframe Hf Hsl Hosfd
    isplitl [Hm Hbs Hmc]
    · iexists j, ys, h
      iframe
      ipureintro; exact Hres
    ileft
    isplitr
    · ipureintro; rfl
    iexists inner; iframe; iassumption
  | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hsl Hosfd
    isplitl [Hm Hbs Hmc]
    · iexists j, ys, h
      iframe
      ipureintro; exact Hres
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists inner; iframe; iassumption

/-- `f.Read(b)` at the offset `o` of a non-empty `b` of at most `maxRW` bytes inside the file
(`o + len(b) ≤ size`, `< 2^62`), the bytes held at any fractions: `b` filled with them and the
offset moved past them; or an error, the offset unchanged. -/
theorem os.File.Read.wp_spec (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (vs : List w8) (o : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta) (xs : List (w8 × Bool))
    (hrd : d.readable = true) (h0 : 0 ≤ o.toInt) (hn : 0 < vs.length) (hn2 : vs.length ≤ 0x40000000)
    (hin : o.toNat + vs.length ≤ m.size) (hxl : xs.length = vs.length)
    (hmax : o.toInt + vs.length < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        sl ↦* vs ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path dqm (some m) ∗
        osBytes (GF := GF) d.path o.toNat dqb xs }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Read")) (Val #sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.path dqm (some m) ∗
        osBytes d.path o.toNat dqb xs ∗ ∃ vs' : List w8, sl ↦* vs' ∗ ⌜vs'.length = vs.length⌝ ∗
        ((⌜n = W64 vs.length ∧ err = interface.nil ∧ vs' = xs.map Prod.fst⌝ ∗
            os.ownOff f (o + W64 vs.length)) ∨
         (⌜n = W64 0 ∧ err ≠ interface.nil⌝ ∗ os.ownOff f o)) }} := by
  unfold os.ownFile os.ownOff
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, ⟨%inner', #Hf', Ho⟩, Hsl, Hosfd, Hm, Hbs⟩
  icombine Hf Hf' gives %hin'
  cases hin'
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  have hsl : sl.len = W64 vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  wp_auto
  have hl0 : ¬ sl.len = W64 0 := by
    intro h; rw [h, show sint.Z (W64 0) = 0 from rfl] at hslz; omega
  rw [decide_eq_false hl0]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z o < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega)]
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl]
  try wp_auto
  have hsum : sint.Z (o + sl.len) = o.toInt + vs.length := by
    rw [hsl]; simp only [sint.Z]; word
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (o + sl.len) by
    rw [hsum, show sint.Z (W64 0x4000000000000000) = 2 ^ 62 from rfl]; omega)]
  wp_auto
  iloeb as IH generalizing Hosfd Hm Hbs Hsl Ho Hfd HΦ
  have hmx : ¬ (sint.Z (W64 1073741824) < sint.Z sl.len) := by
    rw [hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmx]
  wp_auto
  wp_apply wp_osPRead fd o sl.len dq dqm dqb d m xs CoPset.subseteq_top hrd h0
    (by rw [hxl]; simp only [sint.Z] at hslz; have := BitVec.toInt_eq_toNat_cond sl.len; split at this <;> omega)
    $$ Hinv Hosfd Hm Hbs as %r %e %hre Hosfd Hm Hbs
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    rw [decide_eq_false hmx]
    iapply IH $$ Hosfd Hm Hbs Hsl Ho Hfd HΦ
  rw [decide_eq_false he4]
  wp_auto
  rcases hre with ⟨rfl, rfl⟩ | ⟨he0, -⟩
  rotate_left
  · have he0' : ¬ e = W64 0 := he0
    simp only [decide_eq_false he0', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe Hosfd Hm Hbs
    isplitl [Hfd]
    · iexists inner; iframe; isplitl [] <;> iassumption
    iexists vs
    iframe Hsl
    isplitr
    · ipureintro; rfl
    iright
    isplitr
    · ipureintro; exact ⟨rfl, by intro h; cases h⟩
    iexists inner; iframe; iassumption
  rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_string_to_bytes (xs.map Prod.fst) as %tmp ⟨Htmp, -⟩
  wp_apply wp_slice_copy sl vs tmp (xs.map Prod.fst) (DFrac.own 1) $$ [Hsl Htmp] as %mm ⟨%hmm, Hsl, -⟩
  · iframe
  have hrl' : (xs.map Prod.fst).length = vs.length := by simp [hxl]
  have hmmv : sint.nat mm = vs.length := by rw [hmm, hrl']; exact Nat.min_self _
  have hmmeq : mm = sl.len := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.nat, sint.Z] at hmmv hslz
    omega
  subst hmmeq
  rw [decide_eq_false hl0]
  wp_auto
  iapply HΦ
  iframe Hosfd Hm Hbs
  isplitl [Hfd]
  · iexists inner; iframe; isplitl [] <;> iassumption
  iexists _
  iframe Hsl
  isplitr
  · ipureintro; simp; omega
  ileft
  isplitr
  · ipureintro
    refine ⟨hsl, rfl, ?_⟩
    rw [← hrl', List.take_length, List.drop_eq_nil_of_le (by rw [hrl']; exact Nat.le_refl _), List.append_nil]
  rw [hsl]
  iexists inner; iframe; iassumption

end proof

end EtcdGrove
end Perennial
