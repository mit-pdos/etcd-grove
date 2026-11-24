/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Field__format.lean`, over Perennial's `fmt.Sprintf`:
`%s` of the key (a string), `%v` of the value (`fieldsWf`: `nil` or of a predeclared basic type, so
`fmt.ArgsWf` of both). Lean-first (no Rocq counterpart); traceutil-log (2026-11-23).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Field__format
public import Perennial.Proof.fmt.Link

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
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1) $$ [$Hfmt $Hal] as %s ⟨-, -⟩
  · iapply _root_.Perennial.fmt.argsOk_of_argsWf
    unfold traceutil.fieldsWf at Hwf
    exact _root_.Perennial.fmt.ArgsWf.cons_string _ _ Hwf
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
