/-
`purgeRound.wp_proof` (unit `locks`, session 10; `notes/wal-units/locks.md`): one round of
`fileutil.purgeFile`'s loop on the WAL directory, while the WAL's handle is lent (`walOpenWFI_lend`).

* `fileutil.ReadDir(dir)` under the handle's half of the directory's claim `(j, .except X, hj)`: every name
  of the claim is listed; `X` is the pipeline's names (`walDirKey_tmps`), none ending in `"wal"`, so every
  name the round keeps (`fs`, those ending in `"wal"`, sorted) is in the claim, and every `.wal` name is
  among them.
* The removal loop: at `fs[n]`, the claim's `.wal` names are among `fs[n:]` (the earlier ones removed) and
  its entries at `fs[n:]` are as listed. The name is a file (a `.wal` name: `walInv_walFiles`; another: the
  invariant's leftover, lent and given back, `walInv_lendOther`), opened and locked (`TryLockFile` over
  `purge_openTriple`); the lock is not the tail's (`walTailLk_excl`), so a `.wal` name is not the tail's,
  hence (the tail being the largest `.wal` name) not the last, and not a locked segment's
  (`walDirLks_purgeStep`); it is the smallest `.wal` name of the claim, so `os.Remove` commits with the
  segment's update (`walPurge_osAUnc`, the caller's repeatable commit) or a leftover's
  (`walPurgeOther_osAUnc`). The lock is closed (`wp_lockedClose`).
* Every exit gives the handle back (`WalSub`: only `.wal` names but the tail's removed).

Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.purgeRound
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile
public import Spec.os.RemoveN
public import Spec.os.File__Close
public import Spec.strings.HasSuffix
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeRoundLaws
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs WalEnc

section pure
variable [GooseExts]

/-- The round's filter: the names ending in `"wal"`. -/
def prKeep (v : GoString) : Bool := decide (go!"wal" <:+ v)

theorem pr_filter_take_succ (srt : List GoString) (i : Nat) (v : GoString) (hv : srt[i]? = some v) :
    (srt.take (i + 1)).filter prKeep = (srt.take i).filter prKeep ++ (if prKeep v then [v] else []) := by
  rw [List.take_add_one, hv]
  simp only [Option.toList_some, List.filter_append, List.filter_cons, List.filter_nil]

theorem pr_keep_of_wal {b : GoString} (h : walNameP b = true) : prKeep b = true := by
  unfold walNameP at h
  unfold prKeep
  simp only [decide_eq_true_eq] at h ⊢
  exact List.IsSuffix.trans (by decide) h

theorem pr_not_tmps {b : GoString} (h : prKeep b = true) : b ∉ walTmps := by
  intro hm
  simp only [walTmps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> revert h <;> decide

theorem pr_quarter_three : qQuarter + ((1 : Qp).half + qQuarter) = 1 := by
  apply Subtype.ext
  show (1 : Rat) / 2 / 2 + ((1 : Rat) / 2 + (1 : Rat) / 2 / 2) = 1
  grind

theorem pr_quarter_half : qQuarter + qQuarter = (1 : Qp).half := Qp.half_add_half _

/-- An index-sorted list is pairwise sorted. -/
theorem pr_pairwise_of_idx {l : List GoString}
    (h : ∀ (i j : Nat) (xi xj : GoString), l[i]? = some xi → l[j]? = some xj → i < j → go.GoStringLe xi xj) :
    l.Pairwise go.GoStringLe := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact h i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij

/-- The round's kept names: sorted, without repeats, strictly increasing. -/
theorem pr_lt_of {l : List GoString} (hp : l.Pairwise go.GoStringLe) (hn : l.Nodup) :
    l.Pairwise go.GoStringLt := by
  have h2 := hp.and hn
  refine h2.imp ?_
  rintro a b ⟨h1 | h1, hne⟩
  · exact absurd h1 hne
  · exact h1

/-- The names from position `n`: the `n`-th, then the later ones, all larger. -/
theorem pr_drop_cons {l : List GoString} {n : Nat} (hn : n < l.length) :
    l.drop n = l[n] :: l.drop (n + 1) := List.drop_eq_getElem_cons hn

theorem pr_mem_drop_cases {l : List GoString} (hl : l.Pairwise go.GoStringLt) {n : Nat} (hn : n < l.length)
    {b : GoString} (hb : b ∈ l.drop n) : b = l[n] ∨ (go.GoStringLt l[n] b ∧ b ∈ l.drop (n + 1)) := by
  rw [pr_drop_cons hn] at hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact Or.inl rfl
  · right
    refine ⟨?_, hb⟩
    have hd : (l.drop n).Pairwise go.GoStringLt := hl.sublist (List.drop_sublist _ _)
    rw [pr_drop_cons hn] at hd
    exact List.rel_of_pairwise_cons hd hb

theorem pr_lt_irrefl (b : GoString) : ¬ go.GoStringLt b b := by
  unfold go.GoStringLt
  induction b with
  | nil => intro h; cases h
  | cons a t ih =>
    intro h
    cases h with
    | rel h => exact Int.lt_irrefl _ h
    | cons h => exact ih h

theorem pr_not_mem_later {l : List GoString} (hl : l.Pairwise go.GoStringLt) {n : Nat} (hn : n < l.length) :
    l[n] ∉ l.drop (n + 1) := by
  intro hm
  rcases pr_mem_drop_cases hl hn (by rw [pr_drop_cons hn]; exact List.mem_cons_of_mem _ hm) with h | ⟨h, -⟩
  · have hd : (l.drop n).Pairwise go.GoStringLt := hl.sublist (List.drop_sublist _ _)
    rw [pr_drop_cons hn] at hd
    exact pr_lt_irrefl _ (List.rel_of_pairwise_cons hd hm)
  · exact pr_lt_irrefl _ h

/-- The names of the claim after a removal of `bt`: the `.wal` names but `bt` unchanged. -/
theorem pr_walSubAt {X : List GoString} (hX : ∀ b ∈ X, walNameP b = false) {hj hjN : NamesH} {bt : GoString}
    (hc : hjN.cur = purgeNames X bt hj) : WalSubAt hj hjN bt := by
  intro b hb
  rw [hc]
  by_cases he : b = bt
  · subst he; exact Or.inr ⟨rfl, purgeNames_bt⟩
  · left
    exact purgeNames_lookup (fun hm => by rw [hX b hm] at hb; cases hb) he

/-- **The loop's invariant, one name further** (the claim after the removal of `l[n]`). -/
theorem pr_step {l : List GoString} (hl : l.Pairwise go.GoStringLt) {n : Nat} (hn : n < l.length)
    {X : List GoString} (hlN : ∀ b ∈ l, b ∉ X)
    {hj hj' hjN : NamesH} (h2 : ∀ b ∈ l.drop n, hj'.cur !! b = hj.cur !! b)
    (h3 : ∀ b, walNameP b = true → (hj'.cur !! b).isSome → b ∈ l.drop n)
    (hc : hjN.cur = purgeNames X l[n] hj') :
    (∀ b ∈ l.drop (n + 1), hjN.cur !! b = hj.cur !! b) ∧
    (∀ b, walNameP b = true → (hjN.cur !! b).isSome → b ∈ l.drop (n + 1)) := by
  rw [hc]
  have hsub : ∀ b ∈ l.drop (n + 1), b ∈ l.drop n := fun b hb => by
    rw [pr_drop_cons hn]; exact List.mem_cons_of_mem _ hb
  refine ⟨fun b hb => ?_, fun b hb hs => ?_⟩
  · have hne : b ≠ l[n] := fun e => pr_not_mem_later hl hn (e ▸ hb)
    rw [purgeNames_lookup (hlN b (List.mem_of_mem_drop (hsub b hb))) hne]
    exact h2 b (hsub b hb)
  · have hne : b ≠ l[n] := fun e => by rw [e, purgeNames_bt] at hs; cases hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    have hv' := purgeNames_sub hv
    rcases pr_mem_drop_cases hl hn (h3 b hb (by rw [hv']; rfl)) with h | ⟨-, h⟩
    · exact absurd h hne
    · exact h

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **A name of the WAL directory's claim the round keeps is a file**: a `.wal` name's (`walInv_walFiles`),
another's (the invariant's leftover, lent and given back: `walInv_lendOther`, `walInv_unlendOther`). -/
theorem pr_fileOf (W : WalGS GF) (Mr : WalMarshal) (R0 : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (o : WalOut) (bt : GoString) (nd : Node)
    (hD : lendKey j bt ∉ o.D) (hcur : hj.cur !! bt = some nd) :
    ⊢ WalFs.walInv (W := W) walCodec Mr R0 jr r -∗ notCrashed -∗ walDirKey (W := W) dir (incOf I dir) j X -∗
      walIncQ (W := W) I -∗
      osNames j (.except X) (DFrac.own (1 : Qp).half) hj -∗ walOutFrag (W := W) o ={⊤}=∗
      notCrashed ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walOutFrag (W := W) o ∗
        walIncQ (W := W) I ∗
        ⌜∃ i, nd = .file i⌝ := by
  iintro #Hinv Hnc #Hkey HIq Hn Ho
  by_cases hbw : walNameP bt = true
  · imod walInv_walFiles walCodec Mr R0 jr r ⊤ CoPset.subseteq_top dir I j X hj (1 : Qp).half
      $$ Hinv Hnc Hkey HIq Hn with ⟨Hnc, Hn, HIq, %hfiles⟩
    imodintro
    iframe Hnc Hn Ho HIq
    ipureintro; exact hfiles bt nd hbw hcur
  · have hbw' : walNameP bt = false := by simpa using hbw
    imod walInv_lendOther walCodec Mr R0 jr r ⊤ CoPset.subseteq_top dir I j X hj (DFrac.own (1 : Qp).half) o bt nd
      hbw' hD hcur $$ Hinv Hnc Hkey HIq Hn Ho with ⟨Hnc, Hn, HIq, Ho, Hte⟩
    rcases nd with i | dn
    rotate_left
    · simp only [tmpEnt]; icases Hte with ⟨⟩
    imod walInv_unlendOther walCodec Mr R0 jr r ⊤ CoPset.subseteq_top dir I j X hj (DFrac.own (1 : Qp).half)
      (o.addClaim (lendKey j bt)) bt (.file i) hbw' (List.mem_cons_self ..) hcur $$ Hinv Hnc Hkey HIq Hn Ho Hte
      with ⟨Hnc, Hn, HIq, Ho⟩
    have ho : (o.addClaim (lendKey j bt)).delClaim (lendKey j bt) = o := by
      obtain ⟨O, D, T⟩ := o
      simp only [WalOut.addClaim, WalOut.delClaim, WalOut.mk.injEq, true_and, and_true]
      rw [List.filter_cons_of_neg (by simp)]
      exact List.filter_eq_self.2 (fun a ha => by
        simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact hD ha)
    rw [ho]
    imodintro
    iframe Hnc Hn Ho HIq
    ipureintro; exact ⟨i, rfl⟩

/-- **The round's `os.Remove` of a name of the claim** (the file `i` at `bt`, locked by the round, neither the
tail's nor a locked segment's): with a segment's update (`walPurge_osAUnc`, the caller's commit) or a
leftover's (`walPurgeOther_osAUnc`); the claim's names after it unchanged, or without `bt`, as they are when
the call succeeds. -/
theorem pr_remove (wp_Remove : os.Remove.specFileSncN (GF := GF) (hG := hG)) (W : WalGS GF)
    (Mr : WalMarshal) (R0 : Roots) (jr : Ino) (r : GoString) (dir : GoString) (j : Ino) (X : List GoString)
    (hj' : NamesH) (γ : GName) (tg : TailG) (γt : GName) (b : Nat) (ino : Ino) (Pc : IProp GF) (inc : Nat)
    (I : GMap GoString Nat) (R : Roots) (q qc : Qp) (bt : GoString) (i : Ino) (nm0 : GoString) (ls : List (GoString × Ino))
    (hXw : ∀ b ∈ X, walNameP b = false) (hnd : hj'.cur !! bt = some (.file i)) (hbX : bt ∉ X)
    (hbok : NameOk bt)
    (hseg : walNameP bt = true →
      (∀ b' n', hj'.cur !! b' = some n' → walNameP b' = true → b' = bt ∨ go.GoStringLt bt b') ∧
      (∃ b' n', hj'.cur !! b' = some n' ∧ walNameP b' = true ∧ go.GoStringLt bt b') ∧
      ∃ sq ix : Nat, bt = walFileName sq ix ∧ sq < 2 ^ 64)
    (hlk : LkRel hj' tg.2.2.1 nm0 ls b) (h0 : bt ≠ nm0) (hnl : bt ∉ ls.map (·.1)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ WalFs.walInv (W := W) walCodec Mr R0 jr r ∗
        walPurgeAcc (W := W) dir inc Pc ∗ walDirKey (W := W) dir (incOf I dir) j X ∗ walIncQ (W := W) I ∗
        osPathS R dir (DFrac.own q) j ∗ osCallPerm (callKey R dir) qc ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj' ∗
        walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) (<[dir := b]> (∅ : GMap GoString Nat)) ∗
        walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ tg ∗ walCutFrag (W := W) none ∗ Pc }}
      (App (Val (@! os.Remove)) (Val #(child dir bt)))
    {{ (rerr : GoInterface), RET #rerr; osPathS R dir (DFrac.own q) j ∗ osCallPerm (callKey R dir) qc ∗
        ∃ hjN : NamesH, osNames j (.except X) (DFrac.own (1 : Qp).half) hjN ∗
        walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) (<[dir := b]> (∅ : GMap GoString Nat)) ∗
        walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ tg ∗ walCutFrag (W := W) none ∗ walIncQ (W := W) I ∗ Pc ∗
        ⌜WalSubAt hj' hjN bt ∧ (rerr = interface.nil → hjN.cur = purgeNames X bt hj')⌝ }} := by
  iintro %Φ ⟨#Hos, #Hsh, #Hinv, #Hacc, #Hkey, HIq, Hp, Hc, Hn, Htf, Ho, Htk, Hv, Hcf, HPc⟩ HΦ
  ihave Hn2 := (osNames_frac j (.except X) qQuarter qQuarter hj').1 $$ [Hn]
  · rw [pr_quarter_half]; iexact Hn
  icases Hn2 with ⟨Hq1, Hq2⟩
  have hoD : (j, NameSet.except X) ∈ ({ O := [ino], D := [(j, NameSet.except X)], T := [dir] } : WalOut).D := by
    simp
  by_cases hbw : walNameP bt = true
  · obtain ⟨hfirst, hlast, sq, ix, hbtn, hsq⟩ := hseg hbw
    ihave Hau := walPurge_osAUnc Mr R0 jr r dir I j X hj' γ tg γt b ⟨[ino], [(j, .except X)], [dir]⟩ Pc inc bt i sq ix
      nm0 ls hoD hnd hbw hfirst hlast hbtn hsq hlk h0 hnl $$ Hinv Hacc [Htk Hv Hq1 Ho Hcf Htf HPc HIq]
    · unfold walPurgeP; iframe; iexact Hkey
    iapply wp_Remove dir bt j i (.except X) R (DFrac.own q) hj' qQuarter ((1 : Qp).half + qQuarter) qc _
      hbok hbX hnd pr_quarter_three $$ [Hp Hc Hq2 Hau]
    · iframe; isplitl []; iexact Hos; iexact Hsh
    inext
    iintro %rerr ⟨Hp, Hc, %oc, %hoc, HQ, Hout⟩
    iapply HΦ
    iframe Hp Hc
    rcases oc with _ | ⟨x, s0⟩
    · unfold rmFileOutN
      simp only [walPurgeQ, walPurgeP, logOut, claimOut]
      icases HQ with ⟨-, HIq, Htk, Hv, Hq1, Ho, Hcf, Htf, HPc⟩
      icases Hout with ⟨-, Hq2⟩
      iexists hj'
      iframe Htk Hv Ho Hcf Htf HPc HIq
      isplitl [Hq1 Hq2]
      · rw [← pr_quarter_half]; iapply (osNames_frac j (.except X) qQuarter qQuarter hj').2; iframe
      ipureintro
      exact ⟨fun _ _ => Or.inl rfl, fun he => absurd (hoc he) (by simp)⟩
    · unfold rmFileOutN
      simp only [walPurgeQ, walPurgeP, logOut, claimOut, purgeClaim]
      icases HQ with ⟨-, HIq, Htk, Hv, Hq1, Ho, Hcf, Htf, HPc⟩
      icases Hout with ⟨-, Hq2⟩
      iexists hj'.log x (rmFileEnt j bt i s0) (purgeNames X bt hj')
      iframe Htk Hv Ho Hcf Htf HPc HIq
      isplitl [Hq1 Hq2]
      · rw [← pr_quarter_half]; iapply (osNames_frac j (.except X) qQuarter qQuarter _).2
        iframe Hq1
        unfold purgeNames; iexact Hq2
      ipureintro
      exact ⟨pr_walSubAt hXw rfl, fun _ => rfl⟩
  · have hbw' : walNameP bt = false := by simpa using hbw
    ihave Hau := walPurgeOther_osAUnc Mr R0 jr r dir I j X hj' ⟨[ino], [(j, .except X)], [dir]⟩ bt i hoD hnd hbw'
      hbX $$ Hinv [Hq1 Ho HIq]
    · unfold walPurgeOP; iframe; iexact Hkey
    iapply wp_Remove dir bt j i (.except X) R (DFrac.own q) hj' qQuarter ((1 : Qp).half + qQuarter) qc _
      hbok hbX hnd pr_quarter_three $$ [Hp Hc Hq2 Hau]
    · iframe; isplitl []; iexact Hos; iexact Hsh
    inext
    iintro %rerr ⟨Hp, Hc, %oc, %hoc, HQ, Hout⟩
    iapply HΦ
    iframe Hp Hc
    rcases oc with _ | ⟨x, s0⟩
    · unfold rmFileOutN
      simp only [walPurgeOQ, walPurgeOP, logOut, claimOut]
      icases HQ with ⟨-, HIq, Hq1, Ho⟩
      icases Hout with ⟨-, Hq2⟩
      iexists hj'
      iframe Htk Hv Ho Hcf Htf HPc HIq
      isplitl [Hq1 Hq2]
      · rw [← pr_quarter_half]; iapply (osNames_frac j (.except X) qQuarter qQuarter hj').2; iframe
      ipureintro
      exact ⟨fun _ _ => Or.inl rfl, fun he => absurd (hoc he) (by simp)⟩
    · unfold rmFileOutN
      simp only [walPurgeOQ, walPurgeOP, logOut, claimOut, purgeClaim]
      icases HQ with ⟨-, HIq, Hq1, Ho⟩
      icases Hout with ⟨-, Hq2⟩
      iexists hj'.log x (rmFileEnt j bt i s0) (purgeNames X bt hj')
      iframe Htk Hv Ho Hcf Htf HPc HIq
      isplitl [Hq1 Hq2]
      · rw [← pr_quarter_half]; iapply (osNames_frac j (.except X) qQuarter qQuarter _).2
        iframe Hq1
        unfold purgeNames; iexact Hq2
      ipureintro
      exact ⟨pr_walSubAt hXw rfl, fun _ => rfl⟩

set_option maxHeartbeats 4000000 in
theorem purgeRound.wp_proof
    (wp_ReadDir : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG))
    (wp_TryLock : go_etcd_io.etcd.client.pkg.v3.fileutil.TryLockFile.spec (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.specFileSncN (GF := GF) (hG := hG))
    (wp_HasSuffix : strings.HasSuffix.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    purgeRound.spec (GF := GF) (hG := hG) := by
  intro W P Mr R0 jr r lg w dir inc mx Pc hmx
  wp_start as ⟨#Hos, #Hinv, Hh, #Hacc, HPc⟩
  ihave #Hfu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  icases walOpenWFI_lend P Mr w dir inc $$ Hh with ⟨%j, %X, %hj, %R, %q, %nm0, %ino, %lfs, %γ, %tg, %tfd, %I,
    #Hkey, HIq, %hI, Hn, Hp, #Hsh, Hc, Ho, Hlk, Htk, Hv, Hcf, Htl, %hf, Hback⟩
  obtain ⟨hw0, hc0, hXw, hmax⟩ := hf
  ihave %hXt := walDirKey_tmps dir _ j X $$ Hkey
  wp_auto
  wp_apply wp_ReadDir dir slice.nil [] [] (DFrac.own 1) R j (DFrac.own q) (1 : Qp).half.half (.except X)
      (DFrac.own (1 : Qp).half) hj rfl $$ [Hp Hc Hn]
  · iframe
    isplitl []; iassumption
    isplitl []; iassumption
    isplitl []; iassumption
    isplitl []
    · iapply ownSlice_nil
    iapply BigSepL.bigSepL_nil.2
    iempintro
  iintro %rsl %err ⟨Hp, Hc, Hn, -, Hres⟩
  icases Hres with (⟨%names, %rs, %hrd, Hr⟩ | ⟨%he, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok e =>
      wp_auto
      iapply HΦ
      iframe HPc
      iapply Hback $$ %hj %(walSub_refl hj nm0) Hn Hp Hsh Hc Ho Hlk Htk Hv Hcf Htl HIq
  obtain ⟨rfl, hnok, hnm, hcnt, hout⟩ := hrd
  obtain ⟨srt, hperm, hsorted, hrs⟩ := hout
  simp only [fileutil.optsExt, List.foldl_nil, ↓reduceIte] at hrs
  subst rs
  wp_auto
  ihave %Hrl := ownSlice_len _ _ _ $$ Hr
  wp_apply (wp_slice_make2 (V := GoString) (W64 0)) as %t0 ⟨Ht0, Hc0⟩
  · ipureintro; decide
  (try wp_auto)
  ihave IH : iprop(∃ (k : w64) (tsl : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "fs" ∷ fs_ptr ↦ tsl ∗
      "Ht" ∷ tsl ↦* ((srt.take (sint.nat k)).filter prKeep) ∗
      "Htc" ∷ ownSliceCap GoString tsl (DFrac.own 1) ∗
      "Hr" ∷ rsl ↦* srt ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ srt.length⌝) $$ [i fs Ht0 Hc0 Hr]
  · iexists W64 0, t0
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
      List.replicate_zero]
    iframe
    ipureintro; simp
  wp_for IH
  obtain ⟨Hk0, Hkl⟩ := Hk
  wp_if_destruct
  · have hkl : sint.nat k < srt.length := by
      have : sint.Z k < sint.Z rsl.len := Hif
      word
    obtain ⟨v, hv⟩ : ∃ v, srt[sint.nat k]? = some v := ⟨_, List.getElem?_eq_getElem hkl⟩
    have htake := pr_filter_take_succ srt (sint.nat k) v hv
    rw [show sint.nat k + 1 = sint.nat (k + W64 1) by word] at htake
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by word⟩)]
    wp_apply wp_load_slice_index rsl (sint.Z k) srt (DFrac.own 1) v Hk0 $$ [Hr] as Hr
    · iframe; ipureintro; exact hv
    try wp_auto
    wp_apply wp_HasSuffix v go!"wal"
    try wp_auto
    by_cases hm : go!"wal" <:+ v
    · rw [decide_eq_true hm]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by word⟩)]
      wp_apply wp_load_slice_index rsl (sint.Z k) srt (DFrac.own 1) v Hk0 $$ [Hr] as Hr
      · iframe; ipureintro; exact hv
      try wp_auto
      wp_apply wp_slice_literal [v]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Ht $Htc $Hsl1] as %tsl' ⟨Ht, Htc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, tsl'
      simp only [named]
      rw [htake]
      simp only [prKeep, hm, decide_true, ↓reduceIte]
      iframe
      ipureintro; constructor <;> word
    · rw [decide_eq_false hm]
      wp_auto
      wp_for_post
      iframe
      iexists k + W64 1, tsl
      simp only [named]
      rw [htake]
      simp only [prKeep, hm, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro; constructor <;> word
  have hk : sint.nat k = srt.length := by
    have : ¬ sint.Z k < sint.Z rsl.len := Hif
    word
  rw [hk, List.take_length]
  try wp_auto
  -- the kept names
  generalize hL : srt.filter prKeep = L
  have hmemL : ∀ b, b ∈ L ↔ b ∈ names ∧ prKeep b = true := by
    intro b; rw [← hL, List.mem_filter, hperm.mem_iff]
  have hLX : ∀ b ∈ L, b ∉ X := fun b hb => by
    rw [hXt]; exact pr_not_tmps ((hmemL b).1 hb).2
  have hLsome : ∀ b ∈ L, (hj.cur !! b).isSome := fun b hb =>
    (hnm b (hLX b hb)).2 ((hmemL b).1 hb).1
  have hLok : ∀ b ∈ L, NameOk b := fun b hb => hnok b ((hmemL b).1 hb).1
  have hLnd : L.Nodup := by
    rw [List.nodup_iff_count]
    intro a
    by_cases ha : a ∈ L
    · rw [← hL]
      refine Nat.le_trans ((List.filter_sublist (p := prKeep) (l := srt)).count_le a) ?_
      rw [← hperm.count_eq]
      exact hcnt a (hLX a ha)
    · rw [List.count_eq_zero.2 ha]; omega
  have hLlt : L.Pairwise go.GoStringLt := by
    refine pr_lt_of ?_ hLnd
    rw [← hL]
    exact (pr_pairwise_of_idx hsorted).filter _
  have hLall : ∀ b, walNameP b = true → (hj.cur !! b).isSome → b ∈ L := fun b hb hs =>
    (hmemL b).2 ⟨(hnm b (fun hm => by rw [hXw b hm] at hb; cases hb)).1 hs, pr_keep_of_wal hb⟩
  ihave %HtL := ownSlice_len _ _ _ $$ Ht
  have hLlen : L.length < 2 ^ 63 := by
    rw [HtL.1]; have := HtL.2; word
  ihave IH2 : iprop(∃ (k : w64) (hj' : NamesH),
      "n" ∷ n_ptr ↦ k ∗ "Ht" ∷ tsl ↦* L ∗
      "Hn" ∷ osNames j (.except X) (DFrac.own (1 : Qp).half) hj' ∗
      "Hlk" ∷ walDirLks (W := W) dir hj' nm0 lfs tg.2.2.1 ∗ "Hp" ∷ osPathS R dir (DFrac.own q) j ∗
      "Hc" ∷ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
      "Ho" ∷ walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗
      "Htk" ∷ walTailKey (W := W) dir γ ∗ "Hv" ∷ tailVar (W := W) γ tg ∗ "Hcf" ∷ walCutFrag (W := W) none ∗
      "Htl" ∷ walTailLk tfd ino ∗ "HIq" ∷ walIncQ (W := W) I ∗ "HPc" ∷ Pc ∗
      "%Hi2" ∷ ⌜uint.nat k ≤ L.length ∧ WalSub hj hj' nm0 ∧
        (∀ b ∈ L.drop (uint.nat k), hj'.cur !! b = hj.cur !! b) ∧
        (∀ b, walNameP b = true → (hj'.cur !! b).isSome → b ∈ L.drop (uint.nat k))⌝)
      $$ [n Ht Hn Hlk Hp Hc Ho Htk Hv Hcf Htl HIq HPc]
  · iexists W64 0, hj
    iframe
    ipureintro
    refine ⟨by simp, walSub_refl hj nm0, fun _ _ => rfl, fun b hb hs => ?_⟩
    simpa using hLall b hb hs
  wp_for IH2
  obtain ⟨hkL, hsub, h2, h3⟩ := Hi2
  wp_if_destruct
  rotate_left
  · try wp_auto
    iapply HΦ
    iframe HPc
    iapply Hback $$ %hj' %hsub Hn Hp Hsh Hc Ho Hlk Htk Hv Hcf Htl HIq
  have hkn : uint.nat k < L.length := by
    have h1 : uint.Z (k + mx) < uint.Z tsl.len := Hif
    have h2 := HtL.2
    have h3 := HtL.1
    word
  have hk63 : sint.Z k = uint.nat k := by word
  try wp_auto
  obtain ⟨bt, hbtE⟩ : ∃ bt, L[uint.nat k] = bt := ⟨_, rfl⟩
  have hbt? : L[(sint.Z k).toNat]? = some bt := by
    rw [hk63, Int.toNat_natCast, List.getElem?_eq_getElem hkn, hbtE]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by have := HtL.1; have := HtL.2; word⟩)]
  wp_apply wp_load_slice_index tsl (sint.Z k) L (DFrac.own 1) bt (by omega) $$ [Ht] as Ht
  · iframe; ipureintro; exact hbt?
  try wp_auto
  have hbtD : bt ∈ L.drop (uint.nat k) := by rw [pr_drop_cons hkn, hbtE]; exact List.mem_cons_self ..
  have hbtL : bt ∈ L := List.mem_of_mem_drop hbtD
  have hcur' : hj'.cur !! bt = hj.cur !! bt := h2 bt hbtD
  obtain ⟨nd, hnd⟩ := Option.isSome_iff_exists.1 (hLsome bt hbtL)
  rw [← hcur'] at hnd
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod pr_fileOf W Mr R0 jr r dir I j X hj' ⟨[ino], [(j, .except X)], [dir]⟩ bt nd (by simp [lendKey]) hnd
    $$ Hinv Hnc Hkey HIq Hn Ho with ⟨Hnc, Hn, Ho, HIq, %hfi⟩
  imodintro
  iframe Hnc
  obtain ⟨i, rfl⟩ := hfi
  have hpath : dir ++ [47#8] ++ bt = child dir bt := by simp [child, slashB]
  rw [hpath]
  have hbX : bt ∉ X := hLX bt hbtL
  have hbok : NameOk bt := hLok bt hbtL
  wp_apply wp_TryLock (child dir bt) (W64 1) (W32 384) _ Unit _ _
      (purge_openTriple R dir bt (DFrac.own q) j i (.except X) (DFrac.own (1 : Qp).half) hj' (1 : Qp).half.half
        (W64 1) (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hbok hbX hnd)
      (by decide)
    $$ [Hp Hn Hc] as %lf %err ⟨Hpost, Herr⟩
  · isplitl []; · iexact Hos
    isplitl []; · iexact Hfu
    isplitl []; · iPkgInit
    isplitl []; · iexact Hos
    isplitl []; · iexact Hsh
    iframe
  iunfold fileutil.lockPost at Hpost
  icases Hpost with ⟨%x, (⟨%he, ⟨Hp, Hn, Hc⟩, %f, %fd, %i', %lk0, %hc, #Hlf, Hf, Hoff, Hfd, Hlk0, #Hkind⟩ |
    ⟨⟨%he, %hlf⟩, %b', ⟨Hp, Hn, Hc⟩⟩)⟩
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok e =>
      try wp_auto
      wp_for_post
      iapply HΦ
      iframe HPc
      iapply Hback $$ %hj' %hsub Hn Hp Hsh Hc Ho Hlk Htk Hv Hcf Htl HIq
  subst he
  obtain ⟨hfd0, hii⟩ := hc
  subst i'
  try wp_auto
  -- the lock is not the tail's: the name is not the tail's, nor a locked segment's
  icases walTailLk_excl tfd ino i lk0 fd $$ [Htl Hlk0] with ⟨Htl, Hlk0, %hino⟩
  · iframe; iexact Hkind
  have hnm0' : hj'.cur !! nm0 = some (.file ino) := by
    rcases hsub nm0 hw0 with e | ⟨hne, -⟩
    · rw [e]; exact hc0
    · exact absurd rfl hne
  have hne0 : bt ≠ nm0 := by
    rintro rfl; rw [hnm0'] at hnd; cases hnd; exact hino rfl
  icases walDirLks_purgeStep dir hj' nm0 lfs tg.2.2.1 i lk0 fd bt hnd hne0 $$ [Hlk Hlk0] with
    ⟨%γt, %b, %ls, Htf, Hlk0, %hlr, Hlkb⟩
  · iframe; iexact Hkind
  obtain ⟨hlkr, hnl⟩ := hlr
  have hseg : walNameP bt = true →
      (∀ b' n', hj'.cur !! b' = some n' → walNameP b' = true → b' = bt ∨ go.GoStringLt bt b') ∧
      (∃ b' n', hj'.cur !! b' = some n' ∧ walNameP b' = true ∧ go.GoStringLt bt b') ∧
      ∃ sq ix : Nat, bt = walFileName sq ix ∧ sq < 2 ^ 64 := by
    intro hbw
    refine ⟨fun b' n' hb' hw' => ?_, ⟨nm0, _, hnm0', hw0, ?_⟩, ?_⟩
    · rcases pr_mem_drop_cases hLlt hkn (h3 b' hw' (by rw [hb']; rfl)) with e | ⟨e, -⟩
      · left; rw [e, hbtE]
      · right; rw [← hbtE]; exact e
    · rcases hmax bt (.file i) (by rw [← hcur']; exact hnd) hbw with e | e
      · exact absurd e hne0
      · exact e
    · obtain ⟨sq, ix, hbtn, hsqlt⟩ := hlkr.2.2.2.2.1 bt (.file i) hnd hbw hne0 hnl
      exact ⟨sq, ix, hbtn, by have := hlkr.2.1; omega⟩
  wp_apply (pr_remove wp_Remove W Mr R0 jr r dir j X hj' γ tg γt b ino Pc inc I R q (1 : Qp).half.half bt i nm0 ls
      hXw hnd hbX hbok hseg hlkr hne0 hnl) $$ [Hp Hc Hn Htf Ho Htk Hv Hcf HIq HPc]
    as %rerr ⟨Hp, Hc, %hjN, Hn, Htf, Ho, Htk, Hv, Hcf, HIq, HPc, %hrm⟩
  · iframe; iframe #
  obtain ⟨hsa, hok⟩ := hrm
  ihave Hlk := Hlkb $$ %hjN %hsa Htf
  have hsubN : WalSub hj hjN nm0 := walSub_trans_at hsub hsa hne0
  ihave Hlocks := lkFd_locks lk0 i (W64 1) fd $$ [Hlk0 Hkind]
  · iframe; iexact Hkind
  cases rerr with
  | ok e =>
    try wp_auto
    wp_apply (wp_lockedClose wp_Close lf f fd (child dir bt) (fileutil.lkFd lk0 i (W64 1))) $$ [Hf Hfd Hlocks]
      as %cerr -
    · iframe; iframe #
    try wp_auto
    wp_for_post
    iapply HΦ
    iframe HPc
    iapply Hback $$ %hjN %hsubN Hn Hp Hsh Hc Ho Hlk Htk Hv Hcf Htl HIq
  | nil =>
    try wp_auto
    wp_apply (wp_lockedClose wp_Close lf f fd (child dir bt) (fileutil.lkFd lk0 i (W64 1))) $$ [Hf Hfd Hlocks]
      as %cerr -
    · iframe; iframe #
    try wp_auto
    have hc' : hjN.cur = purgeNames X L[uint.nat k] hj' := by rw [hbtE]; exact hok rfl
    obtain ⟨h2', h3'⟩ := pr_step hLlt hkn hLX h2 h3 hc'
    wp_for_post
    iframe
    iexists k + W64 1, hjN
    iframe
    have hk1 : uint.nat (k + W64 1) = uint.nat k + 1 := by word
    rw [hk1]
    ipureintro
    exact ⟨by omega, hsubN, h2', h3'⟩

end proof

end etcd_wal
end EtcdGrove
end Perennial
