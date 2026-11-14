/-
`fileutil.ReadDir`'s body once (read_dir.go): the options loop (`applyOpts` over the option
closures), `os.Open`, the deferred `Close`, `Readdirnames(-1)`, `sort.Strings` and the extension
filter, over abstract triples of the three `os` calls (`ReadDir.wp_core`). `ReadDir.wp_proof`,
`ReadDir.wp_specAbsentIs` and `ReadDir.wp_specChildIs` instantiate it with the shared-mode `os`
specs (`NsS`, `NsChildS`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import LinuxFs.Spec.path.filepath.Ext
public import Perennial.Spec.sort.Strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- The extension the options leave, one option more. -/
theorem fileutil.optsExt_snoc (es : List GoString) (e : GoString) :
    fileutil.optsExt (es ++ [e]) = e := by
  simp [fileutil.optsExt, List.foldl_append]

/-- The extension filter, one name more. -/
theorem fileutil.filter_take_succ (p : GoString → Bool) (srt : List GoString) (i : Nat)
    (v : GoString) (hv : srt[i]? = some v) :
    (srt.take (i + 1)).filter p = (srt.take i).filter p ++ (if p v then [v] else []) := by
  rw [List.take_add_one, hv]
  simp only [Option.toList_some, List.filter_append, List.filter_cons, List.filter_nil]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `ReadDir(d, opts...)` over abstract triples of `os.Open(d)` (from `A`: an fd `fd` of `d`
with `Fd fd` and `B`, or an error `ErrO` with `C`), `Readdirnames(n)`, `n ≤ 0` (from the fd and
`B`: names `OkN`, at most `2^62` of them, or an error `ErrR`; `Fd' fd` and `C` back) and `Close`
(of the fd with `Fd'`). -/
theorem fileutil.ReadDir.wp_core
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG))
    (d : GoString) (sl : GoSlice) (gs : List GoFunc) (es : List GoString) (dqs : DFrac)
    (A B C : IProp GF) (Fd Fd' : w64 → IProp GF) (OkN : List GoString → Prop)
    (ErrO ErrR : GoInterface → IProp GF)
    (hlen : es.length = gs.length)
    (hOk : ∀ names, OkN names → names.length ≤ 2 ^ 62)
    (wpOpen : ∀ Φ : val → IProp GF, A -∗ (∀ (f : Loc) (err : GoInterface),
        ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd d (DFrac.own 1) ∗ Fd fd ∗ B) ∨
         (⌜err ≠ interface.nil⌝ ∗ ErrO err ∗ C)) -∗ Φ (PairV #f #err)) -∗
      WP (App (Val (@! os.Open)) (Val #d)) {{ Φ }})
    (wpRead : ∀ (f : Loc) (fd n : w64) (Φ : val → IProp GF), ⌜sint.Z n ≤ 0⌝ -∗
      os.ownFile f fd d (DFrac.own 1) -∗ Fd fd -∗ B -∗
      (∀ (r : GoSlice) (err : GoInterface), os.ownFile f fd d (DFrac.own 1) -∗ Fd' fd -∗ C -∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ OkN names⌝ ∗ r ↦* names) ∨
         (⌜err ≠ interface.nil⌝ ∗ ErrR err)) -∗ Φ (PairV #r #err)) -∗
      WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n)) {{ Φ }})
    (wpClose : ∀ (f : Loc) (fd : w64) (Φ : val → IProp GF),
      os.ownFile f fd d (DFrac.own 1) -∗ Fd' fd -∗ (∀ err : GoInterface, Φ #err) -∗
      WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #())) {{ Φ }}) :
    {{ A ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
        sl ↦*{dqs} gs ∗ [∗list] i ↦ g ∈ gs, fileutil.withExtFn (GF := GF) g (es.getD i "") }}
      (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir)) (Val #d)) (Val #sl))
    {{ (r : GoSlice) (err : GoInterface), RET (PairV #r #err); sl ↦*{dqs} gs ∗ C ∗
        ((∃ names rs : List GoString, ⌜err = interface.nil ∧ OkN names ∧
              fileutil.ReadDirOut names (fileutil.optsExt es) rs⌝ ∗ r ↦* rs) ∨
         (⌜err ≠ interface.nil⌝ ∗ (ErrO err ∨ ErrR err))) }} := by
  wp_start as ⟨HA, #Hpkg, Hsl, #Hgs⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_method_call
  wp_auto
  ihave %Hgl := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (j : w64) (gv : GoFunc),
      "i" ∷ i_ptr ↦ j ∗ "opt" ∷ opt_ptr ↦ gv ∗
      "Hop" ∷ «$r0_ptr» ↦ go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.mk
        (fileutil.optsExt (es.take (sint.nat j))) ∗
      "Hsl" ∷ sl ↦*{dqs} gs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ gs.length⌝) $$ [i opt «$r0» Hsl]
  · have h0 : (zero_val go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp) =
        go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirOp.mk
          (fileutil.optsExt (es.take (sint.nat (W64 0)))) := by
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, fileutil.optsExt, List.foldl_nil]
      rw [show stringToGoString "" = ([] : GoString) by simp [stringToGoString]]; rfl
    rw [h0]
    iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; simp
  wp_for IH
  obtain ⟨Hj0, Hjl⟩ := Hj
  wp_if_destruct
  · have hjl : sint.nat j < gs.length := by
      have : sint.Z j < sint.Z sl.len := Hif
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, by word⟩)]
    obtain ⟨g, hg⟩ : ∃ g, gs[sint.nat j]? = some g := ⟨_, List.getElem?_eq_getElem hjl⟩
    obtain ⟨e, he⟩ : ∃ e, es[sint.nat j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hjl)⟩
    wp_apply wp_load_slice_index sl (sint.Z j) gs dqs g Hj0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hg
    try wp_auto
    ihave #Hg := BigSepL.bigSepL_lookup hg $$ Hgs
    have hge : es.getD (sint.nat j) (stringToGoString "") = e := by
      simp [List.getD, he]
    rw [hge]
    unfold fileutil.withExtFn
    wp_bind (App (Val #g) (Val #«$r0_ptr»))
    iapply Hg $$ Hop
    iintro !> Hop
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, g
    simp only [named]
    iframe
    have htake : es.take (sint.nat (j + W64 1)) = es.take (sint.nat j) ++ [e] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, he]; rfl
    rw [htake, fileutil.optsExt_snoc]
    iframe
    ipureintro; constructor <;> word
  · have hj : sint.nat j = gs.length := by
      have : ¬ sint.Z j < sint.Z sl.len := Hif
      word
    rw [hj, ← hlen, List.take_length]
    try wp_auto
    wp_bind (App (Val (@! os.Open)) (Val #d))
    iapply (wpOpen _) $$ HA
    iintro %f %err Hr
    icases Hr with (⟨%fd, %herr, Hf, Hfd, HB⟩ | ⟨%herr, HE, HC⟩)
    · subst herr
      wp_auto
      wp_bind (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames"))
        (Val #(W64 (-1))))
      iapply (wpRead f fd (W64 (-1)) _) $$ [] Hf Hfd HB
      · ipureintro; decide
      iintro %r %err Hf Hfd HC Hr
      icases Hr with (⟨%names, %hr, Hr⟩ | ⟨%herr, HE⟩)
      · obtain ⟨rfl, hok⟩ := hr
        wp_auto
        ihave #Hsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
        · iPkgInit
        ihave #Hfp : isPkgInit (PROP := IProp GF) pkg_id.path.filepath $$ []
        · iPkgInit
        wp_apply wp_Strings r names $$ [Hr] as %srt ⟨Hr, %hperm, %hsorted⟩
        · iframe
          ipureintro; exact hOk names hok
        have hE : stringToGoString "" = ([] : GoString) := by simp [stringToGoString]
        by_cases hx : fileutil.optsExt es = []
        · rw [decide_eq_true hx]
          wp_auto
          wp_bind (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
          iapply (wpClose f fd _) $$ Hf Hfd
          iintro %cerr
          wp_auto
          iapply HΦ
          iframe
          ileft
          iexists names, srt
          iframe
          ipureintro
          refine ⟨rfl, hok, srt, hperm, hsorted, ?_⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hx, hE]))]
        · rw [decide_eq_false hx]
          wp_auto
          wp_apply (wp_slice_make2 (V := GoString) (W64 0)) as %t0 ⟨Ht0, Hc0⟩
          · ipureintro; decide
          (try wp_auto)
          ihave %Hrl := ownSlice_len _ _ _ $$ Hr
          ihave IH : iprop(∃ (j : w64) (vv : GoString) (tsl : GoSlice),
              "i" ∷ i_ptr ↦ j ∗ "v" ∷ v_ptr ↦ vv ∗ "tss" ∷ tss_ptr ↦ tsl ∗
              "Ht" ∷ tsl ↦* ((srt.take (sint.nat j)).filter
                (fun v => decide (filepath.extModel v = fileutil.optsExt es))) ∗
              "Htc" ∷ ownSliceCap GoString tsl (DFrac.own 1) ∗
              "Hr" ∷ r ↦* srt ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ srt.length⌝) $$ [i v tss Ht0 Hc0 Hr]
          · iexists W64 0, _, t0
            simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
              List.replicate_zero]
            iframe
            ipureintro; simp
          wp_for IH
          obtain ⟨Hj0, Hjl⟩ := Hj
          wp_if_destruct
          · have hjl : sint.nat j < srt.length := by
              have : sint.Z j < sint.Z r.len := Hif
              word
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, by word⟩)]
            obtain ⟨v, hv⟩ : ∃ v, srt[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hjl⟩
            have htake := fileutil.filter_take_succ
              (fun v => decide (filepath.extModel v = fileutil.optsExt es)) srt (sint.nat j) v hv
            rw [show sint.nat j + 1 = sint.nat (j + W64 1) by word] at htake
            wp_apply wp_load_slice_index r (sint.Z j) srt (DFrac.own 1) v Hj0 $$ [Hr] as Hr
            · iframe; ipureintro; exact hv
            try wp_auto
            wp_apply wp_Ext v as %ev %hev
            subst hev
            try wp_auto
            by_cases hm : filepath.extModel v = fileutil.optsExt es
            · rw [decide_eq_true hm]
              wp_auto
              wp_apply wp_slice_literal [v]
              isplitr
              · ipureintro; rfl
              iintro %sl1 ⟨Hsl1, -⟩
              wp_apply wp_slice_append $$ [$Ht $Htc $Hsl1] as %tsl' ⟨Ht, Htc, -⟩
              try wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, v, tsl'
              simp only [named]
              rw [htake]
              simp only [hm, decide_true, ↓reduceIte]
              iframe
              ipureintro; constructor <;> word
            · rw [decide_eq_false hm]
              wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, v, tsl
              simp only [named]
              rw [htake]
              simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
              iframe
              ipureintro; constructor <;> word
          · have hj : sint.nat j = srt.length := by
              have : ¬ sint.Z j < sint.Z r.len := Hif
              word
            rw [hj, List.take_length]
            try wp_auto
            wp_bind (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
            iapply (wpClose f fd _) $$ Hf Hfd
            iintro %cerr
            wp_auto
            iapply HΦ
            iframe
            ileft
            iexists names, _
            iframe
            ipureintro
            refine ⟨rfl, hok, srt, hperm, hsorted, ?_⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hE]; exact hx))]
      · cases err with
        | nil => exact absurd rfl herr
        | ok ie =>
        wp_auto
        wp_bind (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
        iapply (wpClose f fd _) $$ Hf Hfd
        iintro %cerr
        wp_auto
        iapply HΦ
        iframe
        iright
        isplitr
        · ipureintro; exact herr
        iright; iexact HE
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact herr
      ileft; iexact HE

end proof

end EtcdGrove
end Perennial
