/-
`fileutil.TouchDirAll` and `CreateDirAll` over `fsExt`: proofs (W4/W13 of `notes/wal-fsext-plan.md`),
over their callees' specs (`Exist`, `syncDir`, `os.MkdirAll.specS`, `IsDirWriteable`, `filepath`'s
`Clean`/`Dir`, `ReadDir`) and the two above-root hypotheses (`os.Stat.specAboveRoot`,
`syncDir.specAboveRoot`: the `Exist` loop may climb past the root). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import LinuxFs.Spec.os.MkdirAll
public import LinuxFs.Spec.path.filepath.Clean
public import LinuxFs.Spec.path.filepath.Dir
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchLemmas
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

/-- The directories `TouchDirAll`'s first loop has collected once its `d` is the path of the first `m - 1`
components of `full` (`d = parent/name` the path of all of them): the paths of the first `m`, …,
`|full|` components, outermost first. -/
def touchC (full : List GoString) (m : Nat) : List GoString :=
  (List.range' m (full.length + 1 - m)).map (fun i => os.ancPath (full.take i))

theorem touchC_cons (full : List GoString) (m : Nat) (hm : m ≤ full.length) :
    touchC full m = os.ancPath (full.take m) :: touchC full (m + 1) := by
  unfold touchC
  rw [show full.length + 1 - m = (full.length + 1 - (m + 1)) + 1 by omega, List.range'_succ]
  simp

theorem touchC_end (full : List GoString) : touchC full (full.length + 1) = [] := by
  simp [touchC]

theorem touchC_length (full : List GoString) (m : Nat) :
    (touchC full m).length = full.length + 1 - m := by
  simp [touchC]

theorem touchC_get (full : List GoString) (m i : Nat) (hi : i < (touchC full m).length) :
    (touchC full m)[i] = os.ancPath (full.take (m + i)) := by
  simp [touchC]

/-- The claims of a directory holding no directory cover its subtree. -/
theorem subCover_noDirs (J : Ino) (hJ : NamesH) (hno : ∀ b J', hJ.cur !! b ≠ some (.dir J')) :
    SubCover [(J, NameSet.except [], hJ)] (some (.dir J)) := by
  have key : ∀ A B, ClReach [(J, NameSet.except [], hJ)] A B → A = B := by
    intro A B hr
    cases hr with
    | refl => rfl
    | step _ J1 _ h b hm hb _ =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨-, -, rfl⟩ := hm
      exact absurd hb (hno b J1)
  intro J0 he J' hr
  have h1 : J0 = J := by cases he; rfl
  subst h1
  have := key _ _ hr
  subst this
  exact ⟨hJ, by simp⟩

theorem subCover_none (cl : List Claim) : SubCover cl none := by
  intro J he; cases he

/-- `verify.Assert(true, …)` returns. -/
theorem wp_verifyAssert_true (msg : GoString) (v : GoSlice) :
    {{ (emp : IProp GF) }}
      (App (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.verify.Assert)) (Val #true)) (Val #msg)) (Val #v))
    {{ RET #(); emp }} := by
  wp_start as -
  wp_auto
  iapply HΦ
  iempintro

/-- `Exist` of the path of the first `k` components of `full = rcs ++ cs ++ [name]` (`/rcs` a root,
`cs` the spine's, `name` absent): some answer, `false` for `full` itself. -/
theorem wp_existAnc (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (hStatAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG))
    (R : Roots) (rcs cs : List GoString) (name : GoString) (full : List GoString) (j0 jp : Ino) (qp : Qp)
    (h : NamesH) (k : Nat) (hfull : full = (rcs ++ cs) ++ [name]) (hR : RootsOk R)
    (hm : (joinPath [] rcs, j0) ∈ R) (hrcs : rcs ≠ []) (hcs : ∀ c ∈ cs, NameOk c) (hname : NameOk name)
    (hnone : h.cur !! name = none) (hk : k ≤ full.length) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs (DFrac.own qp) jp ∗
        osNames jp (.only [name]) (DFrac.own 1) h ∗ osCallPerm 1 }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #(os.ancPath (full.take k))))
    {{ (b : Bool), RET #b; osSpine j0 cs (DFrac.own qp) jp ∗ osNames jp (.only [name]) (DFrac.own 1) h ∗
        osCallPerm 1 ∗ ⌜k = full.length → b = false⌝ }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hs, Hn, Hperm⟩ HΦ
  by_cases hkn : k = full.length
  · subst hkn
    have hdir : os.ancPath (full.take full.length) = child (joinPath (joinPath [] rcs) cs) name := by
      rw [List.take_length, ancPath_ne (by subst hfull; simp), hfull, joinPath_snoc, joinPath_joinPath]
    rw [hdir]
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
    wp_apply wp_Exist (child (joinPath (joinPath [] rcs) cs) name) _ _
      (os.Stat.wp_absentS _ name R jp (.only [name]) (DFrac.own qp) (DFrac.own 1) h 1 hname
        (by simp [NameSet.Mem]) hnone) $$ [Hp Hn Hperm] as %b ⟨%err, %hb, Hp, Hn, Hperm, %herr⟩
    · iframe; isplitl [] <;> iassumption
    ihave Hs := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).1 $$ Hp
    iapply HΦ
    iframe
    ipureintro; intro _; simp [hb, herr]
  · have hfl : full.length = (rcs ++ cs).length + 1 := by subst hfull; simp; omega
    have hk' : k ≤ (rcs ++ cs).length := by omega
    rw [show full.take k = (rcs ++ cs).take k by subst hfull; rw [List.take_append_of_le_length hk']]
    wp_apply wp_Exist _ _ _ (wp_statAnc hStatAbove R rcs cs j0 jp (DFrac.own qp) 1 k hR hm hrcs hcs hk')
      $$ [Hs Hperm] as %b ⟨%err, %hb, Hs, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    ipureintro; intro h; exact absurd h hkn

theorem fileutil.TouchDirAll.wp_proof
    (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_MkdirAll : os.MkdirAll.specS (GF := GF) (hG := hG))
    (wp_IsDirWriteable : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG))
    (hSync : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.spec (GF := GF) (hG := hG))
    (hSyncAbove : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.specAboveRoot (GF := GF) (hG := hG))
    (hStatAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG)) :
    fileutil.TouchDirAll.spec (GF := GF) := by
  intro lg R jp d parent name qp h hd hname hlen hnone
  wp_start as ⟨#Hlg, #Hinv, #Hsi, Hp, Hperm, Hn⟩
  wp_auto
  ihave %hlgnn := zapLoggerOk_ne_null lg $$ Hlg
  simp only [hlgnn, decide_false, Bool.not_false]
  wp_apply wp_verifyAssert_true as -
  subst hd
  icases osPathS_cleanAbs_keep R parent _ jp $$ Hp with ⟨Hp, %hclean⟩
  wp_apply wp_Exist (child parent name) _ _
    (os.Stat.wp_absentS parent name R jp (.only [name]) (DFrac.own qp) (DFrac.own 1) h 1 hname
      (by simp [NameSet.Mem]) hnone) $$ [Hp Hn Hperm] as %b ⟨%err, %hb, Hp, Hn, Hperm, %herr⟩
  · iframe; isplitl [] <;> iassumption
  simp only [herr, decide_false] at hb
  subst hb
  wp_auto
  wp_apply wp_Clean (child parent name)
  iintro %cl %hcl
  rw [abs_child hclean hname] at hcl
  subst hcl
  iunfold osPathS at Hp
  icases Hp with ⟨%r, %j0, %cs, %hpp, Hs⟩
  obtain ⟨hR, hm, hcs, hpar⟩ := hpp
  obtain ⟨rcs, hrcs, hrcsok, hr⟩ := (hR.2.2 _ hm).1
  subst hr hpar
  wp_auto
  obtain ⟨full, hfull⟩ : ∃ full, full = (rcs ++ cs) ++ [name] := ⟨_, rfl⟩
  have hfok : ∀ c ∈ full, NameOk c := by
    intro c hc
    subst hfull
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with (hc | hc) | rfl
    · exact hrcsok c hc
    · exact hcs c hc
    · exact hname
  have hflen : full.length = (rcs ++ cs).length + 1 := by subst hfull; simp; omega
  have hdir : os.ancPath (full.take full.length) = child (joinPath (joinPath [] rcs) cs) name := by
    rw [List.take_length, ancPath_ne (by subst hfull; simp), hfull, joinPath_snoc, joinPath_joinPath]
  ihave IH : iprop(∃ (k : Nat) (sl : GoSlice),
      "d" ∷ d_ptr ↦ os.ancPath (full.take k) ∗ "created" ∷ created_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* touchC full (k + 1) ∗ "Hs" ∷ osSpine j0 cs (DFrac.own qp) jp ∗
      "Hn" ∷ osNames jp (.only [name]) (DFrac.own 1) h ∗ "Hperm" ∷ osCallPerm 1 ∗
      "%hk" ∷ ⌜k ≤ full.length⌝) $$ [d created Hs Hn Hperm]
  · iexists full.length, slice.nil
    rw [hdir, touchC_end]
    iframe
    isplitl []
    · iapply ownSlice_nil
    ipureintro; exact Nat.le_refl _
  wp_join iprop(∃ (j : Nat) (sl : GoSlice), created_ptr ↦ sl ∗ sl ↦* touchC full j ∗
      osSpine j0 cs (DFrac.own qp) jp ∗ osNames jp (.only [name]) (DFrac.own 1) h ∗ osCallPerm 1 ∗
      ⌜j ≤ full.length⌝)
    at (App (App (App (Val doFor) _) _) _) with [IH] as ⟨%j, %sl, created, Hsl, Hs, Hn, Hperm, %hj⟩
  · wp_for IH
    wp_apply wp_existAnc wp_Exist hStatAbove R rcs cs name full j0 jp qp h k hfull hR hm hrcs hcs hname
      hnone hk $$ [Hs Hn Hperm] as %b ⟨Hs, Hn, Hperm, %hb⟩
    · iframe; isplitl [] <;> iassumption
    cases b with
    | true =>
      have hkl : k < full.length := by
        rcases Nat.lt_or_eq_of_le hk with h' | h'
        · exact h'
        · exact absurd (hb h') (by decide)
      simp only [Bool.not_true]
      rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
        if_pos (by simp)]
      isplitr
      · itrivial
      iexists k + 1, sl
      iframe
      ipureintro; omega
    | false =>
      simp only [Bool.not_false]
      rw [if_pos (by simp)]
      wp_auto
      wp_apply wp_slice_literal (V := GoString) [os.ancPath (full.take k)]
      isplitr
      · ipureintro; rfl
      iintro %jsl ⟨Hjsl, Hcap⟩
      wp_auto
      wp_apply wp_slice_append _ [os.ancPath (full.take k)] sl (touchC full (k + 1)) (DFrac.own 1)
        $$ [Hjsl Hcap Hsl] as %s' ⟨Hs', -, -⟩
      · iframe
      rw [List.singleton_append, ← touchC_cons full k hk]
      wp_apply wp_Dir (os.ancPath (full.take k))
      iintro %dr %hdr
      rw [dir_take full hfok k hk] at hdr
      subst hdr
      wp_auto
      by_cases hk0 : k = 0
      · subst hk0
        rw [decide_eq_true (by rfl)]
        wp_auto
        iapply wp_for_post_break
        isplitr
        · ipureintro; rfl
        iexists 0, s'
        iframe
        ipureintro; omega
      · rw [decide_eq_false (by rw [← dir_take full hfok k hk]; exact dir_take_ne full hfok k (by omega) hk)]
        wp_auto
        wp_for_post
        wp_apply wp_Dir (os.ancPath (full.take k))
        iintro %dr %hdr
        rw [dir_take full hfok k hk] at hdr
        subst hdr
        wp_auto
        iexists k - 1, s'
        rw [show k - 1 + 1 = k by omega]
        iframe
        ipureintro; omega
  sorry

theorem fileutil.CreateDirAll.wp_proof (hT : fileutil.TouchDirAll.spec (GF := GF)) :
    fileutil.CreateDirAll.spec (GF := GF) := by
  sorry

end proof

end EtcdGrove
end Perennial
