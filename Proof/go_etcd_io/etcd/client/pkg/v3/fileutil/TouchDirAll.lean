/-
`fileutil.TouchDirAll` and `CreateDirAll` over `fsExt`: proofs (W4/W13 of `notes/wal-fsext-plan.md`),
over their callees' specs (`Exist`, `syncDir`, `os.MkdirAll.specS`, `IsDirWriteable`, `filepath`'s
`Clean`/`Dir`, `ReadDir`) and the two above-root hypotheses (`os.Stat.specAboveRoot`,
`syncDir.specAboveRoot`: the `Exist` loop may climb past the root). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import Spec.os.MkdirAll
public import Spec.path.filepath.Clean
public import Spec.path.filepath.Dir
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchLemmas
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteableLemmas
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllLemmas

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
  wp_start as ⟨#Hlg, #Hinv, #Hsi, #Hab, Hp, Hperm, Hn⟩
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
  have hkn : callKey R (child (joinPath (joinPath [] rcs) cs) name) = callKey R (joinPath [] rcs) := by
    rw [← joinPath_snoc]; exact callKey_joinPath hR hm _
  rw [callKey_joinPath hR hm cs]
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
      "Hn" ∷ osNames jp (.only [name]) (DFrac.own 1) h ∗ "Hperm" ∷ osCallPerm (callKey R (joinPath [] rcs)) 1 ∗
      "%hk" ∷ ⌜k ≤ full.length⌝) $$ [d created Hs Hn Hperm]
  · iexists full.length, slice.nil
    rw [hdir, touchC_end]
    iframe
    isplitl []
    · iapply ownSlice_nil
    ipureintro; exact Nat.le_refl _
  wp_join iprop(∃ (j : Nat) (sl : GoSlice), created_ptr ↦ sl ∗ sl ↦* touchC full j ∗
      osSpine j0 cs (DFrac.own qp) jp ∗ osNames jp (.only [name]) (DFrac.own 1) h ∗ osCallPerm (callKey R (joinPath [] rcs)) 1 ∗
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
  ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
  icases (osNames_join jp _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hq, Hr⟩
  ihave Hau := os.osAU_triv (A := Option (Nat × Nat × Ino))
    (osNames jp (.only [name]) (DFrac.own (1 : Qp).half) h)
    (mkOut jp name h (DFrac.own (1 : Qp).half)) $$ Hr
  wp_apply wp_MkdirAll (joinPath (joinPath [] rcs) cs) name (W32 448) R jp qp h (1 : Qp).half (1 : Qp).half
      (mkOut jp name h (DFrac.own (1 : Qp).half)) hname hnone (Qp.half_add_half 1)
      $$ [Hp Hperm Hq Hau] as %err ⟨#Hfe, Hp, Hperm, %o, %hok, HQ, Hout, Hnew⟩
  · rw [← callKey_joinPath hR hm cs]; iframe; isplitl [] <;> iassumption
  rw [callKey_joinPath hR hm cs]
  ihave Hout := mkOut_join jp name h o $$ [HQ Hout]
  · iframe
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ
    iframe
    ileft
    isplitr
    · ipureintro; intro hc; cases hc
    isplitr
    · iapply fmtErrorOkOrNil_ne _ (by intro hc; cases hc) $$ Hfe
    rcases o with _ | ⟨x, s, J⟩
    · dsimp only [mkOut]
      iexists h
      iapply tmpDirH_none jp name h hnone $$ Hout
    · dsimp only [mkOut, mkNew]
      icases Hout with ⟨-, Hn1⟩
      icases Hnew with ⟨%hJ, HJ, %hJc⟩
      iexists _
      iapply tmpDirH_dirE jp name (h.log x (mkEnt jp name J s) (<[name := Node.dir J]> h.cur)) J hJ
        (by simp [NamesH.log]) hJc.1 $$ [Hn1 HJ]
      iframe
  | nil =>
    obtain ⟨⟨x, s, J⟩, rfl⟩ := Option.isSome_iff_exists.1 (hok rfl)
    dsimp only [mkOut, mkNew]
    icases Hout with ⟨-, Hn1⟩
    icases Hnew with ⟨%hJ, HJ, %hJc⟩
    generalize hh1 : h.log x (mkEnt jp name J s) (<[name := Node.dir J]> h.cur) = h1
    have hcur1 : h1.cur !! name = some (.dir J) := by subst hh1; simp [NamesH.log]
    imod osNames_next R jp _ _ h1 CoPset.subseteq_top $$ Hsi Hn1 with ⟨Hn1, #Hlb⟩
    ihave Hs := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).1 $$ Hp
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have hCl := touchC_length full j
    wp_auto
    ihave IH : iprop(∃ (i : w64) (dv : GoString),
        "i" ∷ i_ptr ↦ i ∗ "d" ∷ d_ptr ↦ dv ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗
        "Hs" ∷ osSpine j0 cs (DFrac.own qp) jp ∗ "Hperm" ∷ osCallPerm (callKey R (joinPath [] rcs)) 1 ∗
        "Hc" ∷ (⌜sint.nat i < (touchC full j).length⌝ ∨ osCommitLb h1.next) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ (touchC full j).length⌝) $$ [i d err Hs Hperm]
    · iexists W64 0, _
      iframe
      isplitl []
      · ileft; ipureintro; rw [show sint.nat (W64 0) = 0 from rfl]; omega
      ipureintro
      refine ⟨by decide, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]; omega
    wp_for IH
    obtain ⟨hi0, hil⟩ := Hi
    wp_if_destruct
    · have Hlt : sint.nat i < (touchC full j).length := by rw [Hlen.1]; word
      have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      have He : (touchC full j)[(sint.Z i).toNat]? = some (os.ancPath (full.take (j + sint.nat i))) := by
        rw [show (sint.Z i).toNat = sint.nat i by word, List.getElem?_eq_getElem Hlt, touchC_get]
      have hji : j + sint.nat i ≤ full.length := by omega
      wp_apply wp_load_slice_index sl (sint.Z i) _ (DFrac.own 1) _ hi0 $$ [Hsl] as Hsl
      · iframe; ipureintro; exact He
      wp_apply wp_Dir (os.ancPath (full.take (j + sint.nat i)))
      iintro %dr %hdr
      rw [dir_take full hfok _ hji] at hdr
      subst hdr
      have hk' : j + sint.nat i - 1 ≤ (rcs ++ cs).length := by omega
      rw [show full.take (j + sint.nat i - 1) = (rcs ++ cs).take (j + sint.nat i - 1) by
        rw [hfull, List.take_append_of_le_length hk']]
      wp_apply wp_syncDirAnc hSync hSyncAbove R rcs cs j0 jp (DFrac.own qp) 1 h1.next (j + sint.nat i - 1)
        hR hm hrcs hcs hk' $$ [Hs Hperm] as %e ⟨#Hfe, Hs, Hperm, Hr⟩
      · iframe; iframe #
      cases e with
      | ok e =>
        wp_auto
        wp_for_post
        iapply HΦ
        ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
        iframe
        ileft
        isplitr
        · ipureintro; intro hc; cases hc
        isplitr
        · iapply fmtErrorOkOrNil_ne _ (by intro hc; cases hc) $$ Hfe
        iexists h1
        iapply tmpDirH_dirE jp name h1 J hJ hcur1 hJc.1 $$ [Hn1 HJ]
        iframe
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hi1]
        isplitl [Hr Hc]
        · by_cases hlast : sint.nat i + 1 < (touchC full j).length
          · ileft; ipureintro; exact hlast
          · iright
            have hge : rcs.length ≤ j + sint.nat i - 1 := by
              have : (rcs ++ cs).length = rcs.length + cs.length := List.length_append
              omega
            icases Hr $$ %hge with (%hc | ⟨-, #Hcm⟩)
            · exact absurd rfl hc
            · iexact Hcm
        ipureintro
        refine ⟨by word, by omega⟩
    · icases Hc with (%hc | #Hcm)
      · exfalso; rw [Hlen.1] at hc; word
      ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
      obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qp 1
      subst hqd
      icases (osPathS_frac R (joinPath (joinPath [] rcs) cs) ε a' jp).1 $$ Hp with ⟨Hpe, Hpa⟩
      icases (osNames_join jp (.only [name]) ε b' h1 hqq).2 $$ Hn1 with ⟨Hne, Hnb⟩
      ihave Hpc := osPathS_child R _ name (DFrac.own ε) jp J h1 hname hcur1 $$ Hpe Hne
      imod osNames_split R J (.except []) [go!".touch"] hJ CoPset.subseteq_top $$ Hsi HJ with ⟨Ht, Hrest⟩
      rw [show (NameSet.except []).inter [go!".touch"] = .only [go!".touch"] by simp [NameSet.inter],
        show (NameSet.except []).diff [go!".touch"] = .except [go!".touch"] by simp [NameSet.diff]]
      have hTn : (hJ.restrict J (.only [go!".touch"])).cur !! go!".touch" = none := by
        simp only [NamesH.restrict]
        rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), hJc.1]
        simp
      wp_apply wp_IsDirWriteable (child (joinPath (joinPath [] rcs) cs) name) R J (DFrac.own ε) _ 1 hlen hTn
        $$ [Hpc Hperm Ht]
      · rw [hkn]; iframe; isplitl [] <;> iassumption
      rw [hkn]
      iintro %err ⟨#Hfe, Hpc, Hperm, %hT, HT, Hd, %hTn⟩
      icases touchOut_tmpEnt _ $$ Hd with ⟨%hTd, Hd⟩
      icases os.osPathS_unchild R _ name jp J ε a' hname $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
      · iframe
      icases osNames_agree jp (.only [name]) _ _ h'' h1 $$ Hne Hnb with %he
      subst he
      ihave Hn1 := (osNames_join jp (.only [name]) ε b' h'' hqq).1 $$ [Hne Hnb]
      · iframe
      imod osNames_merge R J (.only [go!".touch"]) (.except [go!".touch"]) (.except []) hT _
        (by intro b; simp only [NameSet.Mem]; by_cases hb : b = go!".touch" <;> simp [hb])
        CoPset.subseteq_top $$ Hsi HT Hrest with ⟨%hM, HM, %hMf⟩
      have hMc := fun c => merged_cur hM hT _ J go!".touch" c hMf.1 hMf.2.1
      have hRc : ∀ c, (hJ.restrict J (.except [go!".touch"])).cur !! c = none := by
        intro c; simp only [NamesH.restrict]
        by_cases hc : c = go!".touch"
        · subst hc; rw [restrictN_lookup_not _ _ _ (by simp [NameSet.Mem])]
        · rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem, hc]), hJc.1]; simp
      have hnoM : ∀ (c : GoString) J', hM.cur !! c ≠ some (.dir J') := by
        intro c J' hc
        rw [hMc c] at hc
        split at hc
        · subst_vars; exact hTd J' hc
        · rw [hRc] at hc; cases hc
      wp_auto
      iapply HΦ
      iframe
      cases err with
      | ok e =>
        ileft
        isplitr
        · ipureintro; intro hc; cases hc
        isplitr
        · iapply fmtErrorOkOrNil_ne _ (by intro hc; cases hc) $$ Hfe
        iexists h''
        iapply tmpDirH_dir jp name h'' J hM hcur1 hnoM $$ [Hn1 HM Hd]
        iframe Hn1 HM
        rw [hMc go!".touch", if_pos rfl]
        iexact Hd
      | nil =>
        iclear Hd
        iright
        isplitr
        · ipureintro; rfl
        iexists h'', hM, J, h''.next
        iframe
        isplitl []
        rotate_left
        · iexact Hcm
        ipureintro
        refine ⟨hcur1, Nat.le_refl _, ?_⟩
        apply GMap.ext; intro c
        rw [hMc c]
        split
        · subst_vars; rw [hTn rfl]; simp
        · rw [hRc]; simp

theorem fileutil.CreateDirAll.wp_proof (hT : fileutil.TouchDirAll.spec (GF := GF))
    (wp_ReadDir : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG)) :
    fileutil.CreateDirAll.spec (GF := GF) := by
  intro lg R jp d parent name qp h hd hname hlen hnone
  wp_start as ⟨#Hlg, #Hinv, #Hsi, #Hab, Hp, Hperm, Hn⟩
  wp_auto
  wp_apply hT lg R jp d parent name qp h hd hname hlen hnone $$ [Hp Hperm Hn] as %err ⟨Hp, Hperm, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%herr, -, %h', Hsub⟩ | ⟨%herr, %h', %hJ, %J, %n, %hf, Hn, HJ, #Hc⟩)
  · cases err with
    | nil => exact absurd rfl herr
    | ok e =>
      wp_auto
      iapply HΦ
      iframe
      ileft
      isplitr
      · ipureintro; intro hc; cases hc
      iexists h'
      iexact Hsub
  subst herr hd
  wp_auto
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qp 1
  subst hqd
  icases (osPathS_frac R parent ε a' jp).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_join jp (.only [name]) ε b' h' hqq).2 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R _ name (DFrac.own ε) jp J h' hname hf.1 $$ Hpe Hne
  icases osCallPerm_child R parent name _ jp 1 $$ Hpa Hperm with ⟨Hpa, Hperm⟩
  wp_apply wp_ReadDir (child parent name) slice.nil [] [] (DFrac.own 1) R J (DFrac.own ε) 1 (.except [])
      (DFrac.own 1) hJ rfl $$ [Hpc Hperm HJ]
  · iframe
    isplitl []; iassumption
    isplitl []; iassumption
    isplitl []; iassumption
    isplitl []
    · iapply ownSlice_nil
    iapply BigSepL.bigSepL_nil.2
    iempintro
  iintro %r %e ⟨Hpc, Hperm, HJ, -, Hres⟩
  icases os.osPathS_unchild R _ name jp J ε a' hname $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osCallPerm_unchild R parent name _ jp 1 $$ Hp Hperm with ⟨Hp, Hperm⟩
  icases osNames_agree jp (.only [name]) _ _ h'' h' $$ Hne Hnb with %he
  subst he
  ihave Hn := (osNames_join jp (.only [name]) ε b' h'' hqq).1 $$ [Hne Hnb]
  · iframe
  icases Hres with (⟨%names, %rs, %hrd, Hr⟩ | ⟨%he, -⟩)
  · obtain ⟨rfl, -, hnm, -, hout⟩ := hrd
    have hnames : names = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro b hb
      have := (hnm b (by simp [NameSet.Mem])).2 hb
      rw [hf.2.2] at this; simp at this
    subst hnames
    obtain ⟨srt, hperm, -, hrs⟩ := hout
    have hsrt : srt = [] := (List.Perm.nil_eq hperm).symm
    subst hsrt
    simp only [fileutil.optsExt, List.foldl_nil, ↓reduceIte] at hrs
    subst hrs
    ihave %hl := ownSlice_len _ _ _ $$ Hr
    have hr0 : r.len = W64 0 := by simp at hl; word
    wp_auto
    rw [hr0]
    wp_auto
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists h'', hJ, J, n
    iframe
    isplitl []
    · ipureintro; exact hf
    iexact Hc
  · cases e with
    | nil => exact absurd rfl he
    | ok e =>
      wp_auto
      iapply HΦ
      iframe
      ileft
      isplitr
      · ipureintro; intro hc; cases hc
      iexists h''
      iapply tmpDirH_dirE jp name h'' J hJ hf.1 hf.2.2 $$ [Hn HJ]
      iframe

end proof

end EtcdGrove
end Perennial
