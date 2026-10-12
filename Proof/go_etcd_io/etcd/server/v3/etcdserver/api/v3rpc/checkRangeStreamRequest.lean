/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeStreamRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsDefaultOrdering
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.HasRevisionFilters
public import Spec.google_golang_org.grpc.status.Errorf

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

omit [FfiSyntax] in
/-- An `int32` enumeration value widened as `rangeOpOf` does is `c` iff the value is `c`. -/
theorem v3rpc.w64_of_w32_eq (x : w32) (c : Int) (hc0 : 0 ≤ c) (hc : c < 2 ^ 31) :
    (W64 (sint.Z x) : w64) = W64 c ↔ x = W32 c := by
  constructor
  · intro h
    have h1 : sint.Z (W64 (sint.Z x) : w64) = sint.Z (W64 c : w64) := by rw [h]
    have h2 : sint.Z (W64 (sint.Z x) : w64) = sint.Z x := by word
    have h3 : sint.Z (W64 c : w64) = c := by word
    rw [h2, h3] at h1
    word
  · intro h; subst h; word

theorem v3rpc.checkRangeStreamRequest.wp_proof
    (hRange : v3rpc.checkRangeRequest.spec (GF := GF) (hG := hG))
    (hDef : txn.IsDefaultOrdering.spec (GF := GF) (hG := hG))
    (hRev : txn.HasRevisionFilters.spec (GF := GF) (hG := hG))
    (hErrf : status.Errorf.spec (GF := GF) (hG := hG)) :
    v3rpc.checkRangeStreamRequest.spec (GF := GF) (hG := hG) := by
  intro r o
  wp_start as #Hr
  ihave #Ptxn : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  wp_apply (hRange r o) $$ [$Hr] as %err Herr
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co,
    %minM, %maxM, %minC, %maxC, -, -, -, -, -, -, #Ho, #Ht, -, -, -, -, -, -, -, %Hop⟩
  cases hc : v3rpc.rangeCheck o with
  | some ce =>
    simp only [v3rpc.checkRes]
    icases Herr with #Herr
    ihave He := Herr
    iunfold txn.errVarIs at He
    icases He with ⟨%ee, -, %Hee⟩
    subst Hee
    wp_auto
    iapply HΦ
    iexact Herr
  | none =>
    simp only [v3rpc.checkRes]
    icases Herr with %Hee
    subst Hee
    wp_auto
    wp_apply (hDef target order)
    have hord : (o.sortOrder = W64 0 ∨ (o.sortTarget = W64 0 ∧ o.sortOrder = W64 1)) ↔
        (order = W32 0 ∨ (target = W32 0 ∧ order = W32 1)) := by
      subst Hop
      simp only [txn.rangeOpOf]
      rw [v3rpc.w64_of_w32_eq order 0 (by decide) (by decide), v3rpc.w64_of_w32_eq target 0 (by decide) (by decide),
        v3rpc.w64_of_w32_eq order 1 (by decide) (by decide)]
    wp_if_destruct
    rotate_left
    · wp_apply (hErrf (W32 12)) as %e2 %He2
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact fun h => absurd (go.intoVal_inj h) (by decide)
      iapply HΦ
      ipureintro
      constructor
      · intro h; exact absurd h He2
      · intro h; exact absurd (hord.1 h.1) (by simpa using Hif)
    have hdef : order = W32 0 ∨ (target = W32 0 ∧ order = W32 1) := by simpa using Hif
    wp_apply (hRev r o) $$ [$Hr]
    cases hrf : txn.hasRevFilters o
    rotate_left
    · wp_auto
      wp_apply (hErrf (W32 12)) as %e2 %He2
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact fun h => absurd (go.intoVal_inj h) (by decide)
      iapply HΦ
      ipureintro
      constructor
      · intro h; exact absurd h He2
      · intro h; rw [h.2] at hrf; exact absurd hrf (by decide)
    · wp_auto
      iapply HΦ
      ipureintro
      constructor
      · intro _; exact ⟨hord.2 hdef, hrf⟩
      · intro _; rfl

end proof

end EtcdGrove
end Perennial
