/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/firstOpType.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstOpType
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequest

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `i`-th `*pb.RequestOp` of `requestOpsIs ps ops` denotes some operation. -/
theorem firstOpType_ops_get : ∀ (ps : List Loc) (ops : List TxnOp) (i : Nat) (p : Loc), ps[i]? = some p →
    txn.requestOpsIs (GF := GF) ps ops ⊢ ∃ op, txn.requestOpIs p op
  | [], _, _, _, h => by simp at h
  | q :: qs, [], _, _, _ => by iintro H; iunfold txn.requestOpsIs at H; iexfalso; iexact H
  | q :: qs, op :: ops, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    iintro H; iunfold txn.requestOpsIs at H
    icases H with ⟨H, -⟩
    iexists op; iexact H
  | q :: qs, op :: ops, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    iintro H; iunfold txn.requestOpsIs at H
    icases H with ⟨-, H⟩
    iapply firstOpType_ops_get qs ops i p h $$ H

/-- A `*pb.RequestOp` of `requestOpIs`: not nil, its `Request` oneof read-only, one of the four
wrappers, holding a non-nil request. -/
theorem firstOpType_ops_req (p : Loc) (op : TxnOp) :
    txn.requestOpIs (GF := GF) p op ⊢ ⌜p ≠ null⌝ ∗ ∃ (u : GoInterface) (w : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□ u ∗
      ((⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w⌝ ∗
          ∃ (r : Loc) (o : OpFull),
          structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
          txn.rangeRequestIs r o) ∨
       (⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w⌝ ∗
          ∃ (r : Loc) (o : OpFull),
          structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
          txn.putRequestIs r o) ∨
       (⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w⌝ ∗
          ∃ (r : Loc) (o : OpFull),
          structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
          txn.deleteRangeRequestIs r o) ∨
       ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w⌝) := by
  cases op
  case txn cs ts es =>
    unfold txn.requestOpIs
    iintro #H
    icases H with ⟨%Hp, %w, %r, #Hu, -⟩
    isplitr; · ipureintro; exact Hp
    iexists _, w
    iframe Hu
    iright; iright; iright; ipureintro; rfl
  all_goals
    unfold txn.requestOpIs
    iintro #H
    icases H with ⟨%Hp, %u, %w, %r, %o, #Hu, H⟩
    isplitr; · ipureintro; exact Hp
    iexists u, w
    iframe Hu
    icases H with (⟨⟨%Hu', -⟩, #Hw, #Hr⟩ | ⟨⟨%Hu', -⟩, #Hw, #Hr⟩ | ⟨⟨%Hu', -⟩, #Hw, #Hr⟩)
    · ileft; isplitr; · ipureintro; exact Hu'
      iexists r, o; iframe #
    · iright; ileft; isplitr; · ipureintro; exact Hu'
      iexists r, o; iframe #
    · iright; iright; ileft; isplitr; · ipureintro; exact Hu'
      iexists r, o; iframe #

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem firstOpType.wp_proof (hGR : RequestOp.GetRequest.spec (GF := GF) (hG := hG)) :
    firstOpType.spec (GF := GF) (hG := hG) := by
  intro sl ps ops
  wp_start as ⟨#Hsl, #Hops⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (v : Loc), "i" ∷ i_ptr ↦ n ∗ "operation" ∷ operation_ptr ↦ v ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i operation]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    ihave ⟨%op, #Hop⟩ := firstOpType_ops_get ps ops (sint.nat n) p Hp $$ Hops
    icases firstOpType_ops_req p op $$ Hop with ⟨%Hpn, %u, %w, #Hu, Hcase⟩
    wp_apply wp_load_slice_index sl (sint.Z n) _ DFrac.discard p Hn $$ [] as -
    · iframe #; ipureintro; exact Hp
    try wp_auto
    wp_apply hGR p u $$ []
    · iframe #; ipureintro; exact Hpn
    icases Hcase with (⟨%H, -⟩ | ⟨%H, -⟩ | ⟨%H, -⟩ | %H) <;> subst H <;> wp_auto <;>
      wp_for_post <;> iapply HΦ <;> itrivial
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
