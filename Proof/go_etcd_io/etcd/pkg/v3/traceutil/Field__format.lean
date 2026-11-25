/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Field__format.lean`, over Perennial's `fmt.Sprintf` (the real `Sprintf`, real `fmt` stage 1):
`%s` of the key (a string), `%v` of the value (`fieldsWf`: `nil` or of a predeclared basic type, so
`fmt.ArgsWf` of both). Lean-first (no Rocq counterpart); traceutil-log (2026-11-23).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Field__format
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode _root_.Perennial.go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Field.format.wp_proof : traceutil.Field.format.spec (GF := GF) (hG := hG) := by
  intro l f
  wp_start as ⟨Hl, %Hwf⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #f.Key', f.Value']
  isplitr
  · ipureintro; rfl
  iintro %al ⟨Hal, -⟩
  (try wp_auto)
  unfold traceutil.fieldsWf at Hwf
  simp only [List.map_cons, List.map_nil] at Hwf
  obtain ⟨args, Hargs⟩ := fmt.PureArgsWf.toPureArgs Hwf
  have Hall := fmt.PureArgs.str f.Key' _ _ Hargs
  obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
    have hl := Hargs.length_eq
    match args, hl with
    | [a], _ => exact ⟨a, rfl⟩
  have Ha := fmt.PureArgs.dirOk_v Hargs a (List.mem_singleton_self _)
  wp_apply fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s:%v; "
    [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_v, .lit go!"; "] _ _ _ (DFrac.own 1)
    (by fmt_encode)
    (.dir _ _ _ _ _ (by simp [_root_.Perennial.fmt.DirOk]) (.lit _ _ _ (by decide)
      (.dir _ _ _ _ _ Ha (.lit _ _ _ (by decide) .nil)))) Hall $$ [$Hfmt $Hal] as %s ⟨-, -⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
