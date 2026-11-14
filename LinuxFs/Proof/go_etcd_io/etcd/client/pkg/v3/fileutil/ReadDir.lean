/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDir.lean` (both specs):
`applyOpts`' loop over the option closures (`fileutil.wp_applyOpts`), the directory read, the sort,
the extension filter. `sort.Strings` is taken unbounded (`sort.StringsAny.spec`, a hypothesis: the
names read have no bound). Its callees:
`os.Open.wp_dirS`, `File.Readdirnames.wp_dirS`, `File.Close.wp_dirS` (proved, `NsS.lean`),
`filepath.Ext.spec` (proved in the part).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import LinuxFs.Spec.path.filepath.Ext
public import LinuxFs.Spec.sort.StringsAny

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- The names of `l` whose extension is `ext` (`ReadDir`'s filter loop). -/
def fileutil.extFilt (ext : GoString) (l : List GoString) : List GoString :=
  l.filter (fun v => decide (filepath.extModel v = ext))

/-- `op.applyOpts(opts)` (`ReadDirOp.applyOpts`): each option sets the extension, the last wins. -/
theorem fileutil.wp_applyOpts (op : Loc) (sl : GoSlice) (gs : List GoFunc) (es : List GoString)
    (dqs : DFrac) (hlen : es.length = gs.length) :
    {{ ([∗list] i ↦ g ∈ gs, fileutil.withExtFn (GF := GF) g (es.getD i "")) ∗ sl ↦*{dqs} gs ∗
        op ↦ zero_val go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp }}
      (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.ty)
        go!"applyOpts" #op)) (Val #sl))
    {{ RET #(); sl ↦*{dqs} gs ∗
        op ↦ go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.mk (fileutil.optsExt es) }} := by
  wp_start as ⟨#Hgs, Hsl, Hop⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  (try wp_auto)
  ihave IH : iprop(∃ (k : w64) (ov : GoFunc),
      "i" ∷ i_ptr ↦ k ∗ "opt" ∷ opt_ptr ↦ ov ∗ "Hsl" ∷ sl ↦*{dqs} gs ∗
      "Hop" ∷ op ↦ go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.mk
        (fileutil.optsExt (es.take (sint.nat k))) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ gs.length⌝) $$ [i opt Hsl Hop]
  · iexists W64 0, _
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    have hz : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.mk (fileutil.optsExt []) =
        zero_val go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp := by
      have he : stringToGoString "" = [] := by simp [stringToGoString]
      simp only [fileutil.optsExt, List.foldl, he]; rfl
    rw [hz]
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH
  obtain ⟨Hk0, Hkl⟩ := Hk
  wp_if_destruct
  · have hkl : sint.nat k < gs.length := by
      have : sint.Z k < sint.Z sl.len := Hif
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by word⟩)]
    obtain ⟨g, hg⟩ : ∃ g, gs[sint.nat k]? = some g := ⟨_, List.getElem?_eq_getElem hkl⟩
    wp_apply wp_load_slice_index sl (sint.Z k) gs dqs g Hk0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hg
    try wp_auto
    ihave #Hg := BigSepL.bigSepL_lookup
      (Φ := fun i g => fileutil.withExtFn (GF := GF) g (es.getD i (stringToGoString ""))) hg $$ Hgs
    iunfold fileutil.withExtFn at Hg
    wp_bind (App (Val #g) (Val #op))
    iapply Hg $$ Hop
    inext
    iintro Hop
    wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, g
    simp only [named]
    iframe
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hk1]
    have hes : fileutil.optsExt (es.take (sint.nat k + 1)) = es.getD (sint.nat k) (stringToGoString "") := by
      have hke : sint.nat k < es.length := by omega
      unfold fileutil.optsExt
      rw [List.take_succ_eq_append_getElem hke, List.foldl_append, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hke]
      rfl
    rw [hes]
    iframe
    ipureintro
    exact ⟨by word, by omega⟩
  have hkn : sint.nat k = es.length := by
    have : ¬ sint.Z k < sint.Z sl.len := by
      intro h; apply Hif; first | exact h | rw [decide_eq_true h]
    rw [hlen]; word
  rw [hkn, List.take_length]
  (try wp_auto)
  iapply HΦ
  iframe


theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.wp_proof
    [sort.Assumptions] [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]
    (wp_Strings : sort.StringsAny.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG) := by
  intro d sl gs es dqs R j dq qc N dqn h hlen
  wp_start as ⟨#Hinv, #Hsi, #Hpkg, Hp, Hperm, Hn, Hsl, #Hgs⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  wp_apply fileutil.wp_applyOpts «$r0_ptr» sl gs es dqs hlen $$ [Hsl «$r0»] as ⟨Hsl, Hop⟩
  · iframe; iexact Hgs
  (try wp_auto)
  wp_apply os.Open.wp_dirS d R j dq qc $$ [Hp Hperm] as %f %err ⟨Hp, Hperm, Hr⟩
  · iframe; isplitl [] <;> iassumption
  icases Hr with (⟨%fd, %he, Hf, Hfd⟩ | ⟨%he, Herr⟩)
  · subst he
    wp_auto
    wp_apply os.File.Readdirnames.wp_dirS f fd d (DFrac.own 1) R j N dqn h _ (by decide)
      $$ [Hf Hfd Hn] as %nsl %err2 ⟨Hf, Hn, Hr2⟩
    · iframe; isplitl [] <;> iassumption
    icases Hr2 with (⟨%names, %hn, Hnames, Hfd⟩ | ⟨%he2, Herr2, %r0, %rs, Hfd⟩)
    · obtain ⟨rfl, hnok, hnex, hncnt⟩ := hn
      wp_auto
      ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
      · iPkgInit
      ihave #Hfp : isPkgInit (PROP := IProp GF) pkg_id.path.filepath $$ []
      · iPkgInit
      wp_apply wp_Strings nsl names $$ [Hnames] as %srt ⟨Hsrt, %hperm, %hsorted⟩
      · iframe
      (try wp_auto)
      icases typedPointsto_split _ _ _ $$ Hop with Hop
      simp only [TypedPointsto.typedPointstoDef]
      icases Hop with ⟨ext, -⟩
      (try wp_auto)
      wp_if_destruct
      · wp_apply os.File.Close.wp_dirS f fd d j _ $$ [Hf Hfd] as %ec -
        · iframe; iexact Hinv
        (try wp_auto)
        iapply HΦ
        iframe
        ileft
        iexists names, srt
        iframe
        ipureintro
        refine ⟨rfl, hnok, hnex, hncnt, srt, hperm, hsorted, ?_⟩
        have he : fileutil.optsExt es = "" := by
          rw [Hif]; simp [stringToGoString]
        rw [he, if_pos rfl]
      · have hext := Hif
        ihave %Hsrtl := ownSlice_len _ _ _ $$ Hsrt
        wp_apply (wp_slice_make2 (V := GoString) (W64 0)) as %t0 ⟨Ht0, Htc0⟩
        · ipureintro; decide
        (try wp_auto)
        ihave IH2 : iprop(∃ (k : w64) (vv : GoString) (tsl : GoSlice),
            "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "tss" ∷ tss_ptr ↦ tsl ∗
            "Ht" ∷ tsl ↦* fileutil.extFilt (fileutil.optsExt es) (srt.take (sint.nat k)) ∗
            "Htc" ∷ ownSliceCap GoString tsl (DFrac.own 1) ∗ "Hsrt" ∷ nsl ↦* srt ∗
            "ext" ∷ structFieldRef go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp go!"ext" «$r0_ptr» ↦
              fileutil.optsExt es ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ srt.length⌝) $$ [i v tss Ht0 Htc0 Hsrt ext]
        · iexists W64 0, _, t0
          simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, fileutil.extFilt, List.filter_nil]
          iframe
          ipureintro
          exact ⟨by decide, by simp⟩
        wp_for IH2
        obtain ⟨Hk0, Hkl⟩ := Hk
        wp_if_destruct
        · have hkl : sint.nat k < srt.length := by
            have : sint.Z k < sint.Z nsl.len := Hif
            word
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by word⟩)]
          obtain ⟨x, hx⟩ : ∃ x, srt[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hkl⟩
          wp_apply wp_load_slice_index nsl (sint.Z k) srt (DFrac.own 1) x Hk0 $$ [Hsrt] as Hsrt
          · iframe; ipureintro; exact hx
          try wp_auto
          wp_apply wp_Ext x as %r %hr
          subst hr
          (try wp_auto)
          have htk : srt.take (sint.nat k + 1) = srt.take (sint.nat k) ++ [x] := by
            rw [List.take_succ_eq_append_getElem hkl]
            rw [List.getElem?_eq_getElem hkl] at hx; cases hx; rfl
          have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          wp_if_destruct
          · wp_apply wp_slice_literal (V := GoString) [x]
            isplitr
            · ipureintro; rfl
            iintro %s1 ⟨Hs1, -⟩
            wp_apply wp_slice_append $$ [$Ht $Htc $Hs1] as %tsl' ⟨Ht, Htc, -⟩
            (try wp_auto)
            wp_for_post
            iframe
            iexists k + W64 1, x, tsl'
            simp only [named]
            simp only [hk1, htk, fileutil.extFilt, List.filter_append]
            have hf : [x].filter (fun v => decide (filepath.extModel v = fileutil.optsExt es)) = [x] := by
              simp [Hif]
            rw [hf]
            iframe
            ipureintro
            exact ⟨by word, by omega⟩
          · (try wp_auto)
            wp_for_post
            iframe
            iexists k + W64 1, x, tsl
            simp only [named]
            simp only [hk1, htk, fileutil.extFilt, List.filter_append]
            have hf : [x].filter (fun v => decide (filepath.extModel v = fileutil.optsExt es)) = [] := by
              simp [Hif]
            rw [hf, List.append_nil]
            iframe
            ipureintro
            exact ⟨by word, by omega⟩
        · have hkn : sint.nat k = srt.length := by
            have : ¬ sint.Z k < sint.Z nsl.len := by
              intro h; apply Hif; first | exact h | rw [decide_eq_true h]
            word
          rw [hkn, List.take_length]
          (try wp_auto)
          wp_apply os.File.Close.wp_dirS f fd d j _ $$ [Hf Hfd] as %ec -
          · iframe; iexact Hinv
          (try wp_auto)
          iapply HΦ
          iframe
          ileft
          iexists names, _
          iframe
          ipureintro
          refine ⟨rfl, hnok, hnex, hncnt, srt, hperm, hsorted, ?_⟩
          have he : fileutil.optsExt es ≠ "" := by
            intro h; apply hext; rw [h]; simp [stringToGoString]
          rw [if_neg he]; rfl
    · obtain ⟨e2, rfl⟩ : ∃ e2, err2 = GoInterface.ok e2 := by
        cases err2 with
        | ok e => exact ⟨e, rfl⟩
        | nil => exact (he2 rfl).elim
      (try wp_auto)
      (try wp_auto)
      wp_apply os.File.Close.wp_dirS f fd d j _ $$ [Hf Hfd] as %ec -
      · iframe; iexact Hinv
      (try wp_auto)
      iapply HΦ
      iframe
      iright
      iframe
      ipureintro; exact he2
  · obtain ⟨he, rfl⟩ := he
    obtain ⟨e1, rfl⟩ : ∃ e1, err = GoInterface.ok e1 := by
      cases err with
      | ok e => exact ⟨e, rfl⟩
      | nil => exact (he rfl).elim
    (try wp_auto)
    (try wp_auto)
    iapply HΦ
    iframe
    iright
    iframe
    ipureintro; exact he

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.wp_proofAbsentS
    [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj] :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.specAbsentS (GF := GF) (hG := hG) := by
  intro d b sl gs es dqs R j dq qc N dqn h hlen hb hN hi
  wp_start as ⟨#Hinv, #Hsi, #Hpkg, Hp, Hperm, Hn, Hsl, #Hgs⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  wp_apply fileutil.wp_applyOpts «$r0_ptr» sl gs es dqs hlen $$ [Hsl «$r0»] as ⟨Hsl, Hop⟩
  · iframe; iexact Hgs
  (try wp_auto)
  wp_apply os.Open.wp_absentS d b R j N dq dqn h qc hb hN hi $$ [Hp Hn Hperm]
    as %f %err ⟨Hp, Hn, Hperm, %he, Herr⟩
  · iframe; isplitl [] <;> iassumption
  obtain ⟨he, rfl⟩ := he
  obtain ⟨e1, rfl⟩ : ∃ e1, err = GoInterface.ok e1 := by
    cases err with
    | ok e => exact ⟨e, rfl⟩
    | nil => exact (he rfl).elim
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; exact he

end proof

end EtcdGrove
end Perennial
