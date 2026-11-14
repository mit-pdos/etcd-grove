/-
Lean-first (no Rocq counterpart).

# The restart's check, transliterated (W4c U5)

`addCand` and `checkRestart` (`examples/etcd/wal/wal.go`) as Lean functions of the Go ones' shape, so
that their specs return them:

* `tAddCand img unl pur cs`: the candidate `(img, unl, pur)` added to `cs`, its bounds merged (max) into
  the first candidate with an equal history;
* `tRaiseUnl imgs opens u`: the unlock bound `u` raised by the `openBound` of each pending `Open`;
* `tImgReads img pur c`: whether some purged prefix `kk ≤ min pur |img|` of the image reads `c`
  (`walReadCut`);
* `tCheckNext o c`: the next candidates (every image of every candidate's history at its mark that
  reads `c`), and `tCheckRestart o c` the oracle `checkRestart` returns.

`tCheckNext_ne_nil` is the check's success: some candidate's image reads `c` from a purged prefix
within its bound.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section pure
variable [GooseExts]

/-- `addCand`: the candidate `(img, unl, pur)` added to `cs`, merging its bounds (max) into the first
candidate with an equal history. -/
def tAddCand (img : List TOp) (unl pur : w64) : List TCand → List TCand
  | [] => [⟨img, unl, pur⟩]
  | c :: cs =>
    if c.h = img then
      { c with unl := if uint.nat c.unl < uint.nat unl then unl else c.unl,
               pur := if uint.nat c.pur < uint.nat pur then pur else c.pur } :: cs
    else c :: tAddCand img unl pur cs

/-- `checkRestart`'s unlock bound: `u` raised by each pending `Open`'s `openBound` over the images. -/
def tRaiseUnl (imgs : List (List TOp)) (opens : List w64) (u : w64) : w64 :=
  opens.foldl (fun u s => if uint.nat u < uint.nat (tOpenBound imgs s) then tOpenBound imgs s else u) u

/-- Whether the image `img` reads `c` from some purged prefix `kk ≤ min pur |img|`. -/
def tImgReads (img : List TOp) (pur : w64) (c : TContents) : Bool :=
  (List.range (min (uint.nat pur) img.length + 1)).any
    (fun kk => decide (tReadCut img (W64 kk) = some c))

/-- `checkRestart`'s step for candidate `cd`: each of its images that reads `c` added to `nx`. -/
def tCandNext (o : TOracle) (c : TContents) (nx : List TCand) (cd : TCand) : List TCand :=
  (tImgs (tCandHist o cd) (tCandMark o cd)).foldl
    (fun nx img => if tImgReads img cd.pur c then
      tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
      else nx) nx

/-- `checkRestart`'s next candidates. -/
def tCheckNext (o : TOracle) (c : TContents) : List TCand := o.cands.foldl (tCandNext o c) []

/-- The oracle `checkRestart` returns. -/
def tCheckRestart (o : TOracle) (c : TContents) : TOracle :=
  ⟨true, tCheckNext o c, [], W64 0, c.hs, []⟩

/-- `checkRestart`'s premises on the oracle: every candidate's history well formed and short (its mark
an `int`), the synced mark within `since`. -/
def tCheckWf (o : TOracle) : Prop :=
  uint.nat o.synced ≤ o.since.length ∧
    ∀ cd ∈ o.cands, tHistWf (tCandHist o cd) ∧ (tCandHist o cd).length < 2 ^ 62

/-! ## Lemmas -/

theorem tAddCand_ne_nil (img : List TOp) (unl pur : w64) (cs : List TCand) :
    tAddCand img unl pur cs ≠ [] := by
  cases cs with
  | nil => simp [tAddCand]
  | cons c cs => unfold tAddCand; split <;> simp

/-- `tAddCand` at the first candidate with an equal history: its bounds raised in place. -/
theorem tAddCand_set (img : List TOp) (unl pur : w64) : ∀ (cs : List TCand) (j : Nat) (c : TCand),
    cs[j]? = some c → (∀ i < j, ∀ c', cs[i]? = some c' → c'.h ≠ img) → c.h = img →
    tAddCand img unl pur cs = cs.set j
      { c with unl := if uint.nat c.unl < uint.nat unl then unl else c.unl,
               pur := if uint.nat c.pur < uint.nat pur then pur else c.pur } := by
  intro cs
  induction cs with
  | nil => intro j c h; simp at h
  | cons c0 cs ih =>
    intro j c hc hpre hh
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      simp [tAddCand, hh]
    | succ j =>
      have h0 : c0.h ≠ img := hpre 0 (Nat.zero_lt_succ _) c0 rfl
      simp only [tAddCand, h0, if_false, List.set_cons_succ]
      congr 1
      exact ih j c hc (fun i hi c' hc' => hpre (i + 1) (by omega) c' hc') hh

/-- `tAddCand` with no candidate of an equal history: appended. -/
theorem tAddCand_none (img : List TOp) (unl pur : w64) : ∀ (cs : List TCand),
    (∀ c ∈ cs, c.h ≠ img) → tAddCand img unl pur cs = cs ++ [⟨img, unl, pur⟩] := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c0 cs ih =>
    intro hall
    simp only [tAddCand, hall c0 (List.mem_cons_self ..), if_false, List.cons_append]
    rw [ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))]

/-- A step from a non-empty list stays non-empty. -/
theorem tCandNext_ne_nil (o : TOracle) (c : TContents) (cd : TCand) :
    ∀ (imgs : List (List TOp)) (nx : List TCand), nx ≠ [] →
      imgs.foldl (fun nx img => if tImgReads img cd.pur c then
        tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
        else nx) nx ≠ [] := by
  intro imgs
  induction imgs with
  | nil => intro nx h; exact h
  | cons img imgs ih =>
    intro nx h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact tAddCand_ne_nil _ _ _ _
    · exact h

theorem tCandNext_of_reads (o : TOracle) (c : TContents) (cd : TCand) :
    ∀ (imgs : List (List TOp)) (nx : List TCand), (∃ img ∈ imgs, tImgReads img cd.pur c = true) →
      imgs.foldl (fun nx img => if tImgReads img cd.pur c then
        tAddCand img (tRaiseUnl (tImgs (tCandHist o cd) (tCandMark o cd)) o.opens cd.unl) cd.pur nx
        else nx) nx ≠ [] := by
  intro imgs
  induction imgs with
  | nil => intro nx ⟨_, h, _⟩; cases h
  | cons img imgs ih =>
    intro nx ⟨img', hm, hr⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · apply tCandNext_ne_nil
      rw [if_pos hr]; exact tAddCand_ne_nil _ _ _ _
    · exact ih _ ⟨img', hm, hr⟩

theorem tCheckNext_fold_ne_nil (o : TOracle) (c : TContents) :
    ∀ (cs : List TCand) (nx : List TCand), nx ≠ [] → cs.foldl (tCandNext o c) nx ≠ [] := by
  intro cs
  induction cs with
  | nil => intro nx h; exact h
  | cons cd cs ih =>
    intro nx h
    simp only [List.foldl_cons]
    exact ih _ (tCandNext_ne_nil o c cd _ _ h)

theorem tImgReads_true {img : List TOp} {pur : w64} {c : TContents} {kk : Nat}
    (hkk : kk ≤ uint.nat pur ∧ kk ≤ img.length) (hr : tReadCut img (W64 kk) = some c) :
    tImgReads img pur c = true := by
  unfold tImgReads
  rw [List.any_eq_true]
  exact ⟨kk, List.mem_range.2 (by omega), by simpa using hr⟩

theorem tImgReads_false {img : List TOp} {pur : w64} {c : TContents}
    (h : ∀ j, j ≤ min (uint.nat pur) img.length → tReadCut img (W64 j) ≠ some c) :
    tImgReads img pur c = false := by
  unfold tImgReads
  rw [Bool.eq_false_iff]
  intro ht
  rw [List.any_eq_true] at ht
  obtain ⟨j, hj, hr⟩ := ht
  exact h j (by have := List.mem_range.1 hj; omega) (by simpa using hr)

/-- **The check succeeds** when some candidate's image at its mark reads `c` from a purged prefix
within its purge bound. -/
theorem tCheckNext_ne_nil {o : TOracle} {c : TContents} {cd : TCand} {img : List TOp} {kk : Nat}
    (hcd : cd ∈ o.cands) (himg : img ∈ tImgs (tCandHist o cd) (tCandMark o cd))
    (hkk : kk ≤ uint.nat cd.pur ∧ kk ≤ img.length) (hr : tReadCut img (W64 kk) = some c) :
    tCheckNext o c ≠ [] := by
  have hreads : tImgReads img cd.pur c = true := by
    unfold tImgReads
    rw [List.any_eq_true]
    exact ⟨kk, List.mem_range.2 (by omega), by simpa using hr⟩
  unfold tCheckNext
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hcd
  rw [hl, List.foldl_append, List.foldl_cons]
  apply tCheckNext_fold_ne_nil
  exact tCandNext_of_reads o c cd _ _ ⟨img, himg, hreads⟩

/-- An image's operations are the history's or a torn prefix of one: a well-formed history's images
are well formed. -/
theorem tHistWf_of_mem_tImgs {h : List TOp} {n : Nat} {img : List TOp} (hw : tHistWf h)
    (himg : img ∈ tImgs h n) : tHistWf img := by
  unfold tImgs at himg
  rw [List.mem_flatMap] at himg
  obtain ⟨j, -, hj⟩ := himg
  rcases List.mem_cons.1 hj with rfl | hj
  · exact tHistWf_take hw j
  · unfold tTornImgs at hj
    cases hoj : h[j]? with
    | none => rw [hoj] at hj; cases hj
    | some o =>
      rw [hoj] at hj
      simp only at hj
      split at hj
      · cases hj
      · rename_i hsn
        rw [List.mem_map] at hj
        obtain ⟨k, -, rfl⟩ := hj
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact tHistWf_take hw j x hx
        · rw [List.mem_singleton] at hx
          subst hx
          have ho : tOpWf o := hw o (List.mem_of_getElem? hoj)
          refine ⟨fun h => by simp [tTornOp] at h, fun _ e he => ?_, fun _ => by simp [tTornOp, tHs0]⟩
          exact ho.2.1 (by simpa using hsn) e (List.mem_of_mem_take he)

end pure

end etcd_wal
end EtcdGrove
end Perennial
