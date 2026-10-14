/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__InsertStep.lean`. Lean-first (no Rocq
counterpart); unit P4 (2026-10-14; an axiom since unit P1b). The body shifts the steps with an
overlapping `append(t.steps[:at+1], t.steps[at:]...)`: `wp_slice_append_shift`
(`SliceShift.lean`, derived from Perennial's slice library), then overwrites the duplicated step
at `at`; an `at` past the end appends.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__InsertStep
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.SliceShift

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.InsertStep.wp_proof :
    traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG) := by
  intro t e at' st msg fields
  wp_start as ⟨Ht, Hf, %Hat⟩
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hss
  ihave %Hswf := ownSlice_wf _ _ _ $$ Hss
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left ⟨by decide, by word, by word⟩]
    wp_auto
    rw [ite_eq_left ⟨Hat, by word, Hswf.2⟩]
    try wp_auto
    wp_apply (wp_slice_append_shift (V := traceutil.step) v.steps' ss at' ⟨Hat, Hif⟩)
      $$ [$Hss $Hcap] as %s' ⟨Hss, Hcap⟩
    try wp_auto
    ihave %Hsl' := ownSlice_len _ _ _ $$ Hss
    have hi : sint.nat at' < ss.length := by rw [Hsl.1]; word
    have hlen' : (ss.take (sint.nat at' + 1) ++ ss.drop (sint.nat at')).length = ss.length + 1 := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    rw [ite_eq_left ⟨Hat, by rw [hlen'] at Hsl'; word⟩]
    wp_apply (wp_store_slice_index (V := traceutil.step) s' (sint.Z at') _ _) $$ [$Hss] as Hss
    · ipureintro; rw [hlen']; constructor <;> word
    try wp_auto
    have hset : (ss.take (sint.nat at' + 1) ++ ss.drop (sint.nat at')).set (sint.Z at').toNat
        ({ time' := st, msg' := msg, fields' := fields, isSubTraceStart' := false,
           isSubTraceEnd' := false } : traceutil.step) =
        ss.take (sint.nat at') ++
          ({ time' := st, msg' := msg, fields' := fields, isSubTraceStart' := false,
             isSubTraceEnd' := false } : traceutil.step) :: ss.drop (sint.nat at') := by
      have h1 : (sint.Z at').toNat = sint.nat at' := rfl
      rw [h1, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
        List.append_assoc, List.singleton_append,
        List.set_append_right _ _ (by rw [List.length_take]; omega)]
      rw [List.length_take, Nat.min_eq_left (by omega), Nat.sub_self, List.set_cons_zero]
    rw [hset]
    iapply HΦ
    iunfold traceutil.ownTrace
    iexists _, _
    (try simp only)
    iframe Ht Hfs Hss Hcap
    isplitl [Hsf Hf]
    · ihave Hsf := (BigSepL.bigSepL_append (l₁ := ss.take (sint.nat at'))
        (l₂ := ss.drop (sint.nat at'))).1 $$ [Hsf]
      · rw [List.take_append_drop]; iexact Hsf
      icases Hsf with ⟨H1, H2⟩
      iapply BigSepL.bigSepL_append.2
      iframe H1
      iapply BigSepL.bigSepL_cons.2
      iframe
    ipureintro; exact He
  · wp_apply wp_slice_literal (V := traceutil.step)
      [({ time' := st, msg' := msg, fields' := fields, isSubTraceStart' := false, isSubTraceEnd' := false } : traceutil.step)]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append (V := traceutil.step) _ _ _ _ _ $$ [$Hss $Hcap $Hsl2]
      as %sl3 ⟨Hss, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iunfold traceutil.ownTrace
    iexists _, _
    (try simp only)
    iframe Ht Hfs Hss Hcap
    isplitl [Hsf Hf]
    · iapply BigSepL.bigSepL_snoc.2
      iframe
    ipureintro; exact He

end proof

end EtcdGrove
end Perennial
