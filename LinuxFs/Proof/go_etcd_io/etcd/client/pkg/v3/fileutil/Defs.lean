/-
Shared definitions of `fileutil`'s specs over the Linux file extension (the part's translation):

* `preGrown i m w`: the file `i`, which had the `OsMeta` `m`, grown to the size `w` by a resize
  (`fallocate`'s growth, `ftruncate`): its `OsMeta` some `m'` of that size with `m`'s mappings and
  at least its page cache known zero past the size (`OsMeta.cz`), and
  the bytes from the old size to `w` a zero run of unknown candidates (`osZerosA`, I4: the 64 MB
  segments are never held byte by byte);
* `errno_errTree`: an `Errno` error is a leaf error tree for `errors.As` with a `*Errno` target.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.os.Base
public import GooseLang.Ext.Fs.Zeros
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- What a growth keeps of the `OsMeta` `m` in `m'`: the cut (`OsMeta.cut`), and a crash's lower size
bound at most the size, if it was. -/
def GrowMeta (m m' : OsMeta) : Prop := m'.cut = m.cut ∧ (m.lo ≤ m.size → m'.lo ≤ m'.size)

theorem GrowMeta.refl (m : OsMeta) : GrowMeta m m := ⟨rfl, id⟩

theorem GrowMeta.trans {m m1 m' : OsMeta} (h1 : GrowMeta m m1) (h2 : GrowMeta m1 m') :
    GrowMeta m m' := ⟨h2.1.trans h1.1, fun h => h2.2 (h1.2 h)⟩

theorem touch_size' (m : OsMeta) (lo hi : Nat) : (m.touch lo hi).size = m.size := by
  unfold OsMeta.touch; split
  · rfl
  · split <;> rfl

/-- A change's first step keeps the cut, and the lower bound below the size. -/
theorem growMeta_announce (m : OsMeta) (lo hi tg : Nat) : GrowMeta m (m.announce lo hi tg) := by
  refine ⟨by simp, fun h => ?_⟩
  simp only [OsMeta.announce, touch_size']
  omega

/-- A resize that landed with a size `sz'` past the old one, or at its target. -/
theorem growMeta_rsPost (tr : Bool) (m : OsMeta) (tg sz' : Nat) (hsz : m.size ≤ sz' ∨ sz' = tg) :
    GrowMeta m (rsPost tr m tg sz') := by
  refine ⟨by simp [rsPost], fun h => ?_⟩
  simp only [rsPost, OsMeta.announce]
  omega

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The file `i`, of `OsMeta` `m` before, grown to the size `w`: its `OsMeta` (of that size, with
`m`'s mappings, the page cache known zero past the size at least as far) and its new bytes,
zeros. -/
def preGrown (i : Ino) (m : OsMeta) (w : Nat) : IProp GF :=
  iprop(∃ m' : OsMeta, ⌜m'.size = w ∧ m'.maps = m.maps ∧ m.cz ≤ m'.cz ∧ GrowMeta m m'⌝ ∗
    osMeta i (DFrac.own 1) m' ∗ osZerosA i m.size (w - m.size) (DFrac.own 1))

theorem preGrown_unfold (i : Ino) (m : OsMeta) (w : Nat) :
    preGrown (GF := GF) i m w ⊣⊢ ∃ m' : OsMeta,
      ⌜m'.size = w ∧ m'.maps = m.maps ∧ m.cz ≤ m'.cz ∧ GrowMeta m m'⌝ ∗
      osMeta i (DFrac.own 1) m' ∗ osZerosA i m.size (w - m.size) (DFrac.own 1) := .rfl

/-- Not grown. -/
theorem preGrown_same (i : Ino) (m : OsMeta) :
    osMeta (GF := GF) i (DFrac.own 1) m ⊢ preGrown i m m.size := by
  iintro Hm
  unfold preGrown
  iexists m
  iframe Hm
  isplitr
  · ipureintro; exact ⟨rfl, rfl, Nat.le_refl _, GrowMeta.refl m⟩
  rw [Nat.sub_self]
  iapply (osZerosA_unfold i m.size 0 _).2
  iexists []
  isplitr
  · ipureintro; rfl
  rw [List.map_nil]; unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro

/-- Two growths in a row are one. -/
theorem preGrown_trans (i : Ino) (m m1 : OsMeta) (w : Nat) (h1 : m.size ≤ m1.size)
    (h2 : m1.size ≤ w) (hmaps : m1.maps = m.maps) (hcz : m.cz ≤ m1.cz) (hg : GrowMeta m m1) :
    osZerosA (GF := GF) i m.size (m1.size - m.size) (DFrac.own 1) ∗ preGrown i m1 w ⊢
      preGrown i m w := by
  iintro ⟨Hz, Hg⟩
  unfold preGrown
  icases Hg with ⟨%m', %hm', Hm, Hz'⟩
  iexists m'
  iframe Hm
  isplitr
  · ipureintro; exact ⟨hm'.1, hm'.2.1.trans hmaps, Nat.le_trans hcz hm'.2.2.1, hg.trans hm'.2.2.2⟩
  have hw : w - m.size = (m1.size - m.size) + (w - m1.size) := by omega
  rw [hw]
  iapply (osZerosA_add i m.size _ _ _).2
  rw [show m.size + (m1.size - m.size) = m1.size by omega]
  iframe

/-- A resize that grew the file landed (`rsDone`): grown. -/
theorem rsDone_preGrown {tr : Bool} (p : Ino) (tg sz' : Nat) (m : OsMeta) (n : Nat)
    (hsz : m.size ≤ sz' ∨ sz' = tg) :
    rsDone (GF := GF) tr p tg sz' m n ⊢ preGrown (GF := GF) p m sz' := by
  iintro H
  icases rsDone_zerosA tr p tg sz' m n $$ H with ⟨Hm, Hz, -⟩
  unfold preGrown
  iexists rsPost tr m tg sz'
  iframe
  ipureintro
  refine ⟨rfl, ?_, ?_, growMeta_rsPost tr m tg sz' hsz⟩
  · simp [rsPost, OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl
  · simp only [rsPost, rsCz]; split <;> omega

/-- A growth that did not land (`rsUndone`, nothing cut off): not grown. -/
theorem rsUndone_preGrown {tr : Bool} (p : Ino) (tg : Nat) (m : OsMeta) (n : Nat) :
    rsUndone (GF := GF) tr p tg m [] n ⊢ preGrown (GF := GF) p m m.size := by
  unfold rsUndone
  iintro ⟨Hm, -, -⟩
  unfold preGrown
  iexists m.announce (min m.size tg) (rsHi tr m.size tg) tg
  iframe Hm
  isplitr
  · ipureintro
    suffices h : _ ∧ _ ∧ _ from ⟨h.1, h.2.1, h.2.2, growMeta_announce ..⟩
    simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> simp
  rw [Nat.sub_self]
  iapply (osZerosA_unfold p m.size 0 _).2
  iexists []
  isplitr
  · ipureintro; rfl
  rw [List.map_nil]; unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro

/-- A truncate that grew the file landed (`os.ftDone`): grown. -/
theorem ftDone_preGrown (p : Ino) (m : OsMeta) (tg : Nat) :
    os.ftDone (GF := GF) p m tg ⊢ preGrown (GF := GF) p m tg := by
  unfold os.ftDone
  iintro ⟨%zs, %hzs, Hm, Hb, -⟩
  unfold preGrown
  iexists rsPost true m tg tg
  iframe Hm
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_, growMeta_rsPost true m tg tg (Or.inr rfl)⟩
    · simp [rsPost, OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl
    · simp only [rsPost, rsCz, if_true]; omega
  iapply (osZerosA_unfold p m.size _ _).2
  iexists zs
  iframe Hb
  ipureintro; exact hzs

/-- A truncate that grew nothing landed (`os.ftUndone`, nothing to cut off): not grown. -/
theorem ftUndone_preGrown (p : Ino) (m : OsMeta) (tg : Nat) :
    os.ftUndone (GF := GF) p m tg [] ⊢ preGrown (GF := GF) p m m.size := by
  unfold os.ftUndone
  iintro ⟨%xs', %hxs, Hm, -, -⟩
  unfold preGrown
  iexists m.announce (min m.size tg) (rsHi true m.size tg) tg
  iframe Hm
  isplitr
  · ipureintro
    suffices h : _ ∧ _ ∧ _ from ⟨h.1, h.2.1, h.2.2, growMeta_announce ..⟩
    simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> simp
  rw [Nat.sub_self]
  iapply (osZerosA_unfold p m.size 0 _).2
  iexists []
  isplitr
  · ipureintro; rfl
  rw [List.map_nil]; unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro

/-- No mapping, no cells. -/
theorem mcellsAny_empty (M : GMap Loc Nat) (hM : M = ∅) (lo hi : Nat) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  subst hM
  unfold mcellsAny
  iapply BigSepM.bigSepM_empty.2; iempintro

/-- An `Errno` error is a leaf (its method set: `Error`, `Is`, `Temporary`, `Timeout`). -/
theorem errno_leaf [syscall.Assumptions] (e : w64) :
    errors.isLeafError ⟨syscall.Errno.ty, #e⟩ := by
  have h := fun m => go.method_set_is (t := syscall.Errno.ty) m
  have hAs := h go!"As"; have hU := h go!"Unwrap"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU
  simp [errors.isLeafError, hAs, hU]

/-- An `Errno` error's value has the target's Lean type (`w64`) for a `*Errno` target. -/
theorem errno_asTyped [syscall.Assumptions] (e : w64) :
    errors.AsTypeTyped w64 syscall.Errno.ty ⟨syscall.Errno.ty, #e⟩ := by
  unfold errors.AsTypeTyped
  rw [go.underlying_unfold (t := syscall.Errno.ty)]
  simp only [syscall.Errno.underlying]
  rw [go.is_underlying (t := go.uintptr)]
  split
  · rename_i h; exact absurd h (by decide)
  · intro _; exact ⟨e, rfl⟩

/-- A `*Errno` is a valid `errors.As` target (`Errno` implements `error`). -/
theorem errno_asTarget [syscall.Assumptions] : errors.AsTarget syscall.Errno.ty :=
  Or.inr (by go_type_set)

/-- `errors.As(errnoErr e, &errno)`'s error tree. -/
theorem errno_errTree [syscall.Assumptions] [errors.Assumptions] (e : w64) :
    ⊢ errors.isErrorTree (GF := GF) (· = interface.ok ⟨syscall.Errno.ty, #e⟩) w64 syscall.Errno.ty :=
  errors.isErrorTree_leaf _ (errno_leaf e) (errno_asTyped e)

end defs

end EtcdGrove
end Perennial
