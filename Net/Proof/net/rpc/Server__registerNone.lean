/-
The proof of `Server.register.spec_none` (`Net/Spec/net/rpc/Server__register.lean`): `register`'s
proof (`Server__register.lean`) up to its methods, for a receiver with none (`rcvrNone`): the
service's method map stays empty (the loop runs no iteration), so `register` logs its message
(`log.Println`) and returns `errors.New` of it, without touching the server.
-/
module

public import Net.Spec.net.rpc.Server__register
public import Net.Spec.net.rpc.getCodec
public import Net.Spec.go.token.IsExported
public import Net.Spec.log.Println
public import Net.Proof.net.rpc.Errs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [errors.Assumptions] [go.token.Assumptions] [log.Assumptions]

theorem Server.register.wp_proof_none (wp_getCodec : getCodec.spec (GF := GF) (hG := hG))
    (wp_IsExported : go.token.IsExported.spec (GF := GF) (hG := hG))
    (wp_Println : log.Println.spec (GF := GF) (hG := hG)) :
    Server.register.spec_none (GF := GF) (hG := hG) := by
  intro s γ C rcvr nm name useName hname
  wp_start as ⟨#Hs, #Hset, Hrcv, #Hlog⟩
  wp_auto
  wp_apply wp_getCodec C $$ Hset as %cd #Hcd
  unfold codecIs
  icases Hcd with ⟨%v, #Hv, -, -, #Hrcvok⟩
  iStructNamed Hv
  wp_auto
  unfold rcvOk
  wp_bind (App (Val #v.Receiver') _)
  iapply Hrcvok $$ Hrcv
  inext
  iintro %rp #Hrp
  unfold rcvrNone
  icases Hrp with ⟨%rv, #Hrv, %Hrf, #HM⟩
  obtain ⟨Hnm, Hnp⟩ := Hrf
  iStructNamed Hrv
  wp_auto
  cases useName
  case' false =>
    simp only [regNameOk, Bool.false_eq_true, ite_false] at hname
    obtain ⟨-, c, rest, hnm, hc⟩ := hname
    wp_auto
    rw [Hnp]
    wp_auto
    rw [Hnm, hnm]
    wp_auto
    wp_apply wp_IsExported c rest hc
    (try wp_auto)
    simp only [Bool.false_eq_true, ite_false]
    generalize c :: rest = sn
  case' true =>
    simp only [regNameOk, ite_true] at hname
    wp_auto
    rw [decide_eq_false hname]
    wp_auto
    simp only [ite_true]
    generalize name = sn

  all_goals
    wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %mp2 Hmp2
    (try wp_auto)
    wp_apply (wp_map_for_range (V := Loc) (fun _keys (_i : Int) => iprop(
        mp2 ↦$ (∅ : GMap GoString Loc) ∗
        s_ptr ↦ «$r0_ptr» ∗ «$r0_ptr» ↦ ({ name' := sn, rcvr' := rcvr, method' := mp2 } : net.rpc.service) ∗
        (∃ x : Loc, m_ptr ↦ x) ∗ (∃ y : GoString, mname_ptr ↦ y)))
      _ go.string (go.GoType.PointerType net.rpc.Method.ty) rv.Methods' ∅ DFrac.discard) $$ HM
    iintro %keys -
    isplitl [Hmp2 s «$r0» m mname]
    · iframe
    isplitr
    · imodintro
      iintro %i %key %mm ⟨%Hik, %Hmm⟩ -
      simp [GMap.lookup_empty] at Hmm
    iintro ⟨HM2, Hsp, Hr0, -, -⟩ -
    wp_auto
    wp_apply (wp_map_len_lt (K := GoString) (V := Loc) mp2 ∅ (DFrac.own 1)) $$ HM2 as ⟨HM2, -⟩
    have hsz : W64 (GMap.size (∅ : GMap GoString Loc)) = W64 0 := by
      rw [GMap.map_size_empty]; try rfl
    rw [decide_eq_true hsz]
    wp_auto
    -- no method: `str` set by the receiver's `PtrHasMethods`, logged, and returned as an error
    cases rv.PtrHasMethods'
    all_goals
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Println _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [$Hlog $Hsl] as -
      (try wp_auto)
      wp_apply wp_errors_New' as %x #-
      (try wp_auto)
      iapply HΦ
      ipureintro; simp [interface.mkOk]

end proof

end net.rpc
end Perennial
