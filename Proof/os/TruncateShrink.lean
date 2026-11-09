/-
`(*File).Truncate(sz)` shrinking a file with no mappings (`TrustedCode/os.lean`'s model, over the
extension's `GooseLang/Ext/OsFs/TruncateShrink.lean`), as `fileutil.ZeroToEnd` does. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.os.Base
public import GooseLang.Ext.Fs.TruncateShrink

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `f.Truncate(sz)` shrinking (or keeping the size of) a file with no mappings, with its
`OsMeta` and the bytes past `sz`, whole: on success its `OsMeta` is `m.shrunk sz`; on failure the
client keeps the fd. -/
theorem os.File.Truncate.wp_shrink (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64)
    (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List (w8 × Bool)) (hfd0 : 0 ≤ fd.toInt)
    (hwr : d.writable = true) (hsz : 0 ≤ sz.toInt) (hshr : sz.toNat ≤ m.size) (hmaps : m.maps = ∅)
    (hxs : xs.length = m.size - sz.toNat) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
        osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
        osBytes (GF := GF) d.ino sz.toNat (DFrac.own 1) xs }}
      (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        ((⌜err = interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) (m.shrunk sz.toNat)) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm, Hb⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  have h1 : ¬ (sint.Z fd < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd0
  rw [decide_eq_false h1]
  wp_auto
  have h2 : ¬ (sint.Z sz < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hsz
  rw [decide_eq_false h2]
  wp_auto
  ihave HS : ∃ (m0 : OsMeta) (xs0 : List (w8 × Bool)), ⌜m0.shrunk sz.toNat = m.shrunk sz.toNat ∧
      m0.maps = ∅ ∧ sz.toNat ≤ m0.size ∧ xs0.length = m0.size - sz.toNat⌝ ∗
      osMeta d.ino (DFrac.own 1) (m0) ∗ osBytes d.ino sz.toNat (DFrac.own 1) xs0 $$ [Hm Hb]
  · iexists m, xs; iframe; ipureintro; exact ⟨rfl, hmaps, hshr, hxs⟩
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  icases HS with ⟨%m0, %xs0, %hm0, Hm, Hb⟩
  obtain ⟨hs0, hmp0, hsh0, hxl0⟩ := hm0
  wp_apply wp_osFtruncateShrinkStart fd sz dq d m0 xs0 CoPset.subseteq_top hwr hsz hsh0 hmp0 hxl0
    $$ Hinv Hosfd Hm Hb as %t Hosfd Ht
  wp_apply wp_osFtruncateShrinkFinish t d.ino sz.toNat m0 xs0 CoPset.subseteq_top hsh0 hmp0
    $$ Hinv Ht as %e Hr
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    icases Hr with (⟨%he, -⟩ | ⟨-, (Hm | ⟨%ys, %hys, Hm, Hb⟩)⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · iapply IH $$ [Hm] Hosfd Hfd HΦ
      iexists (m0.shrunk sz.toNat), []
      iframe
      isplitr
      · ipureintro
        refine ⟨by rw [OsMeta.shrunk_shrunk, hs0], by rw [OsMeta.shrunk_maps, hmp0], ?_, ?_⟩
        · rw [OsMeta.shrunk_size]; exact Nat.le_refl _
        · rw [OsMeta.shrunk_size]; simp
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
    · iapply IH $$ [Hm Hb] Hosfd Hfd HΦ
      iexists { shMeta m0 sz.toNat with vk := none }, ys
      iframe
      ipureintro
      have hyl : ys.length = xs0.length := by
        have := congrArg List.length hys; simpa using this
      refine ⟨?_, hmp0, hsh0, by rw [hyl, hxl0]; rfl⟩
      rw [← hs0]; simp only [OsMeta.shrunk, shMeta, Nat.min_assoc, Nat.min_self]
  · rw [decide_eq_false he4]
    wp_auto
    icases Hr with (⟨%he, Hm⟩ | ⟨%he, -⟩)
    · subst he
      rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      ileft
      rw [hs0]
      iframe
      ipureintro; rfl
    · have he0' : ¬ e = W64 0 := he
      rw [decide_eq_false he0']
      wp_auto
      wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      iright
      ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
