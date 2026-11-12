/-
Proof of the spec of the same name (`util.go`, translated; unit P4, 2026-10-14: it was a
trust-boundary axiom). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyTxnRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.isNil
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.warnOfExpensiveGenericRequest
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewLoggableTxnRequest
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse__GetKvs

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

theorem txn.WarnOfExpensiveReadOnlyTxnRequest.wp_proof
    (hLog : NewLoggableTxnRequest.spec (GF := GF) (hG := hG))
    (hNil : txn.isNil.spec (GF := GF) (hG := hG))
    (hGRR : ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hKvs : RangeResponse.GetKvs.spec (GF := GF) (hG := hG))
    (hGen : txn.warnOfExpensiveGenericRequest.spec (GF := GF) (hG := hG)) :
    txn.WarnOfExpensiveReadOnlyTxnRequest.spec (GF := GF) (hG := hG) := by
  intro lg d now r t resp err P
  wp_start as ⟨%Hlg, #Hr, HP, Hresp⟩
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply time.wp_Since as %el -
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iexact HP
  (try wp_auto)
  wp_apply (hLog r t) $$ [] as %rs #Hrs
  · iframe #
  (try wp_auto)
  wp_apply hNil
  wp_join iprop(∃ rs : GoString, resp_ptr ↦ rs ∗ txnResponse_ptr ↦ resp ∗ P)
    with [resp txnResponse HP Hresp] as ⟨%rs, resp, txnResponse, HP⟩
  · (try wp_auto)
    icases Hresp with (%Hn | ⟨#Hsh, #Hsz⟩)
    · exact absurd Hn Hif
    iunfold txn.txnRespShow at Hsh
    icases Hsh with ⟨%sl, %ps, #Hrsp, #Hsl, #Hops⟩
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    (try wp_auto)
    ihave IH : iprop(∃ (n : w64) (rv : Loc) (rsl : GoSlice) (ss : List GoString),
        "i" ∷ i_ptr ↦ n ∗ "rv" ∷ r_ptr ↦ rv ∗ "resps" ∷ resps_ptr ↦ rsl ∗
        "Hss" ∷ rsl ↦* ss ∗ "Hcap" ∷ ownSliceCap GoString rsl (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i r resps]
    · iexists W64 0, _, slice.nil, []
      iframe
      isplitl []; · iapply ownSlice_nil
      isplitl []; · iapply ownSliceCap_nil
      ipureintro; decide
    wp_for IH
    wp_if_destruct
    · have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, by simpa using Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      have Hlt : sint.nat n < ps.length := by have := Hsll.1; word
      obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
      wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard p Hn $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact Hp
      ihave #Hop := BigSepL.bigSepL_lookup (Φ := fun _ p => txn.respOpShow (GF := GF) p) Hp $$ Hops
      iunfold txn.respOpShow at Hop
      icases Hop with ⟨%Hpn, %u, #Hu, (⟨%w, %rr, %Hueq, #Hw, #Hrr⟩ | %Hnot)⟩
      · subst Hueq
        (try wp_auto)
        wp_apply (hGRR p w rr) $$ []
        · iframe #; ipureintro; exact Hpn
        by_cases hrr : rr = null
        · subst hrr
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          (try wp_auto)
          wp_apply wp_slice_append (V := GoString) _ _ _ _ _ $$ [$Hss $Hcap $Hsl2]
            as %rsl' ⟨Hss, Hcap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, p, rsl', _
          iframe
          ipureintro; word
        · icases Hrr with (%Hn0 | ⟨%sl', #Hk⟩)
          · exact absurd Hn0 hrr
          rw [decide_eq_false hrr]
          (try wp_auto)
          wp_apply (hKvs rr sl') $$ []
          · iframe #; ipureintro; exact hrr
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hasl] as %s0 ⟨-, -⟩
          case wf =>
            repeat' first
              | exact _root_.Perennial.fmt.ArgsWf.nil
              | refine _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.int _) ?_
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          (try wp_auto)
          wp_apply wp_slice_append (V := GoString) _ _ _ _ _ $$ [$Hss $Hcap $Hsl2]
            as %rsl' ⟨Hss, Hcap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, p, rsl', _
          iframe
          ipureintro; word
      · rcases u with ii | _
        rotate_left
        · (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, p, rsl, ss
          iframe
          ipureintro; word
        have hty := Hnot ii rfl
        (try wp_auto)
        simp only [hty, ↓reduceIte]
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, p, rsl, ss
        iframe
        ipureintro; word
    · (try wp_auto)
      wp_apply _root_.Perennial.strings.wp_Join _ _ _ _ $$ [$Hss] as Hss
      (try wp_auto)
      iunfold txn.sizeOk at Hsz
      wp_apply Hsz $$ [$HP $Hpp] as %sz HP
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hasl] as %s0 ⟨-, -⟩
      case wf =>
        repeat' first
          | exact _root_.Perennial.fmt.ArgsWf.nil
          | refine _root_.Perennial.fmt.ArgsWf.cons_string _ _ ?_
          | refine _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.int _) ?_
      (try wp_auto)
      isplitr; · ipureintro; rfl
      iexists _; iframe resp txnResponse HP
  (try wp_auto)
  wp_apply hGen
  · iframe Hrs; ipureintro; exact Hlg
  iapply HΦ
  iexact HP

end proof

end EtcdGrove
end Perennial
