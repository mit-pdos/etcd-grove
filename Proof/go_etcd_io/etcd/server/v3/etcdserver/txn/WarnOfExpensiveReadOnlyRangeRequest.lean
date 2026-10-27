/-
Proof of the spec of the same name (`util.go`, translated; unit P4, 2026-10-14: it was a
trust-boundary axiom). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyRangeRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.isNil
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.warnOfExpensiveGenericRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.WarnOfExpensiveReadOnlyRangeRequest.wp_proof
    (hNil : txn.isNil.spec (GF := GF) (hG := hG))
    (hGen : txn.warnOfExpensiveGenericRequest.spec (GF := GF) (hG := hG)) :
    txn.WarnOfExpensiveReadOnlyRangeRequest.spec (GF := GF) (hG := hG) := by
  intro lg d now req resp err P
  wp_start as ⟨%Hlg, #Hs, HP, Hresp⟩
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply time.wp_Since as %el -
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iexact HP
  (try wp_auto)
  wp_apply hNil
  wp_join iprop(∃ rs : GoString, resp_ptr ↦ rs ∗ rangeResponse_ptr ↦ resp ∗ P)
    with [resp rangeResponse HP Hresp] as ⟨%rs, resp, rangeResponse, HP⟩
  · (try wp_auto)
    icases Hresp with (%Hn | ⟨⟨%sl, #Hk⟩, #Hsz⟩)
    · exact absurd Hn Hif
    (try wp_auto)
    iunfold txn.sizeOk at Hsz
    wp_apply Hsz $$ [$HP $Hpp] as %n HP
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hasl] as %s ⟨-, -⟩
    case wf =>
      repeat' first
        | exact _root_.Perennial.fmt.ArgsWf.nil
        | refine _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.int _) ?_
    (try wp_auto)
    isplitr; · ipureintro; rfl
    iexists _; iframe resp rangeResponse HP
  (try wp_auto)
  wp_apply hGen
  · iframe Hs; ipureintro; exact Hlg
  iapply HΦ
  iexact HP

end proof

end EtcdGrove
end Perennial
