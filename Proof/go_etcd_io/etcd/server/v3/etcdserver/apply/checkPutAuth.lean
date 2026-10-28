/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
theorem apply.checkPutAuth.wp_proof
    (hLP : apply.checkLeasePuts.spec (GF := GF) (hG := hG)) :
    apply.checkPutAuth.spec (GF := GF) (hG := hG) := by
  intro st le γ P f RD on RW ai info dq r o
  wp_start as ⟨#Hst, #Hle, Hai, Hrd, #Hr⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, #HPut, #HRange, -⟩
  iunfold apply.permCheck2 at HPut
  iunfold apply.permCheck3 at HRange
  iunfold txn.putRequestIs at Hr
  icases Hr with ⟨%Hrn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #HK, #Hk, -, -, #HL, #HPK, -, -, -, %Ho, %Hkb⟩
  subst Ho
  wp_auto
  rw [Hsti]
  wp_apply HPut $$ [$Hai $Hk $Hrd] as %err ⟨Hai, -, Hrd, #HeI1, %Hoff1, #Hv1⟩
  · ipureintro; exact Hkb
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hai Hrd; isplitl []; (first | iexact HeI1 | iexact HeI2 | iexact HeI3 | iexact HeI4 | iapply applyErrIs_nil); isplitl []; (ipureintro; first | (intro _; rfl) | (intro h; exact Hoff3 h) | (intro h; exact Hoff2 h) | (intro h; exact Hoff1 h)); (iintro %h; cases h)
  | nil =>
  wp_auto
  rw [← Hsti]
  wp_apply (hLP st le γ P f RD on RW ai info dq lease) $$ [$Hst $Hle $Hai $Hrd] as %err ⟨Hai, Hrd, #HeI2, %Hoff2⟩
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hai Hrd; isplitl []; (first | iexact HeI1 | iexact HeI2 | iexact HeI3 | iexact HeI4 | iapply applyErrIs_nil); isplitl []; (ipureintro; first | (intro _; rfl) | (intro h; exact Hoff3 h) | (intro h; exact Hoff2 h) | (intro h; exact Hoff1 h)); (iintro %h; cases h)
  | nil =>
  wp_auto
  cases pk
  · wp_auto
    iapply HΦ; iframe Hai Hrd; isplitl []; (first | iexact HeI1 | iexact HeI2 | iexact HeI3 | iexact HeI4 | iapply applyErrIs_nil); isplitl []; (ipureintro; first | (intro _; rfl) | (intro h; exact Hoff3 h) | (intro h; exact Hoff2 h) | (intro h; exact Hoff1 h))
    iintro %_
    simp only [apply.putClass, apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, Bool.false_eq_true, ↓reduceIte]
    iapply (apply.classRes_of_permVerdict on info k [] .write) $$ Hv1
  wp_auto
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  rw [Hsti]
  wp_apply HRange $$ %ai %info %dq %ksl %slice.nil %k %([] : List w8) %DFrac.discard %(DFrac.own 1) [Hai Hnil Hrd] as %err ⟨Hai, -, -, Hrd, #HeI3, %Hoff3, #Hv3⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hai Hrd; isplitl []; (first | iexact HeI1 | iexact HeI2 | iexact HeI3 | iexact HeI4 | iapply applyErrIs_nil); isplitl []; (ipureintro; first | (intro _; rfl) | (intro h; exact Hoff3 h) | (intro h; exact Hoff2 h) | (intro h; exact Hoff1 h)); (iintro %h; cases h)
  | nil =>
    wp_auto
    iapply HΦ; iframe Hai Hrd; isplitl []; (first | iexact HeI1 | iexact HeI2 | iexact HeI3 | iexact HeI4 | iapply applyErrIs_nil); isplitl []; (ipureintro; first | (intro _; rfl) | (intro h; exact Hoff3 h) | (intro h; exact Hoff2 h) | (intro h; exact Hoff1 h))
    iintro %_
    simp only [apply.putClass, apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
    iapply apply.classRes_cons
    isplitl []
    · iapply (apply.classRes_of_permVerdict on info k [] .write) $$ Hv1
    · iapply (apply.classRes_of_permVerdict on info k [] .read) $$ Hv3

end proof

end EtcdGrove
end Perennial
