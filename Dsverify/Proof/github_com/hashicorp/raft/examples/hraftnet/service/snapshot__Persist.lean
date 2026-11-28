/-
The proof of `service.snapshot.Persist` (adapted from dsverify-lab's hr3 `snapshot__Persist.lean`, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.snapshot__Persist
public import Perennial.Spec.strconv.Itoa
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.encodeState

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

theorem github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Persist.wp_proof
    (wp_Itoa : strconv.Itoa.spec (GF := GF) (hG := hG))
    (wp_encodeState : github_com.hashicorp.raft.examples.hraftnet.service.encodeState.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.snapshot.Persist.spec (GF := GF) (hG := hG) := by
  intro γ fc sn x k id own Q R
  wp_start as ⟨#Hsn, #Hsink, #HQ, Hown⟩
  unfold snapVal
  icases Hsn with ⟨%es, #Hsn, #Hsp, %Hes⟩
  iStructNamed Hsn
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Itoa $$ [$Hstr]
  wp_apply wp_encodeState $$ [$Hpkg]
  have hb : _root_.Perennial.internal.strconv.fmtInt (W64 (es.length : Int)) (W64 10) ++ go!"|" ++
      (if (regOf es).isSome = true then go!"1" ++ (regOf es).getD [] else go!"0") = snapBytes es := by
    have h2 : (if (regOf es).isSome = true then go!"1" ++ (regOf es).getD [] else go!"0") =
        encodeReg (regOf es) := by
      cases regOf es <;> rfl
    rw [h2]; rfl
  rw [hb]
  wp_apply (wp_string_to_bytes (snapBytes es)) as %bsl ⟨Hb, -⟩
  unfold isSink
  icases Hsink with ⟨%Hrf, #HWrite, #HClose, -, -, -⟩
  wp_bind (App (Val #(methods k.ty _ k.v)) _)
  iapply HWrite $$ Hown Hb
  iintro Hown Hb
  wp_auto
  wp_bind (App (Val #(methods k.ty _ k.v)) _)
  iapply HClose $$ Hown [HQ]
  · iapply HQ
    rw [List.nil_append]
    iexact Hsp
  iintro Hown -
  wp_auto
  iapply HΦ $$ Hown

end proof

end Perennial
