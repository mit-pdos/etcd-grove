/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/checkTxnReads.lean`: each
response's range, if any, is checked by `checkKVs`. `GetResponseRange` of a response of another
kind is run from its code (its spec, `ResponseOp__GetResponseRange.lean`, is of a range's only), so
every call is. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkTxnReads
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkKVs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `opRespsMsg` element by element. -/
theorem opRespsMsg_getElem' (ps : List Loc) (ms : List OpRespM) :
    opRespsMsg (GF := GF) ps ms ⊢
      ⌜ps.length = ms.length⌝ ∗ □ ∀ (k : Nat) (p : Loc) (m : OpRespM), ⌜ps[k]? = some p⌝ -∗
        ⌜ms[k]? = some m⌝ -∗ opRespMsg p m := by
  induction ps generalizing ms with
  | nil =>
    cases ms with
    | nil =>
      iintro -
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %k %p %m %Hp
      simp at Hp
    | cons m ms =>
      unfold opRespsMsg
      iintro %H
      exact H.elim
  | cons p ps ih =>
    cases ms with
    | nil =>
      unfold opRespsMsg
      iintro %H
      exact H.elim
    | cons m ms =>
      show opRespMsg p m ∗ opRespsMsg ps ms ⊢ _
      iintro ⟨#Hp, Hr⟩
      ihave ⟨%Hl, #Hall⟩ := ih ms $$ Hr
      isplitr
      · ipureintro; simp [Hl]
      imodintro
      iintro %k %p' %m' %Hp' %Hm'
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp' Hm'
        subst Hp' Hm'
        iexact Hp
      | succ k =>
        simp only [List.getElem?_cons_succ] at Hp' Hm'
        iapply Hall $$ %k %p' %m' %Hp' %Hm'

theorem checkTxnReads.wp_proof (wp_checkKVs : checkKVs.spec (GF := GF) (hG := hG)) :
    checkTxnReads.spec (GF := GF) (hG := hG) := by
  intro who sl ps ms Hok
  wp_start as ⟨#Hps, #Hms⟩
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave %Hsl := ownSlice_len $$ Hps
  ihave ⟨%Hml, #Hm⟩ := opRespsMsg_getElem' ps ms $$ Hms
  wp_auto
  ihave HI : (∃ (j : w64) (p0 : Loc),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ p0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i op]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z sl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ps (sint.nat j) as p
    obtain ⟨m, Hmj⟩ : ∃ m, ms[sint.nat j]? = some m :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hml]; word)⟩
    wp_apply wp_load_slice_index sl (sint.Z j) ps DFrac.discard p Hj.1 $$ [Hps] as -
    · iframe #; ipureintro; exact Hp_lookup
    ihave #Hp := Hm $$ %(sint.nat j) %p %m %Hp_lookup %Hmj
    (try wp_auto)
    have hnext : ∀ m', ms[sint.nat j]? = some m' → respReadsOk who m' :=
      fun m' h => Hok m' (List.mem_of_getElem? h)
    cases m with
    | range rev kvs more count =>
      iunfold opRespMsg at Hp
      icases Hp with ⟨%Hpn, %w, %r, #Hresp, #Hrr, #Hr⟩
      iunfold txn.rangeResponseIs at Hr
      icases Hr with ⟨%Hrn, %h, %ksl, %kps, -, -, -, #Hk, #Hks, #Hkvs, -⟩
      wp_method_call
      wp_call
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hpn
      (try wp_auto)
      wp_if_destruct
      · exact absurd rfl Hrn
      (try wp_auto)
      wp_apply wp_checkKVs who ksl kps kvs (hnext _ Hmj)
      · iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, p
      iframe
      ipureintro; constructor <;> word
    | put rev prev =>
      iunfold opRespMsg at Hp
      icases Hp with ⟨%Hpn, %w, %r, #Hresp, -⟩
      wp_method_call
      wp_call
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hpn
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, p
      iframe
      ipureintro; constructor <;> word
    | delete rev n prevs =>
      iunfold opRespMsg at Hp
      icases Hp with ⟨%Hpn, %w, %r, #Hresp, -⟩
      wp_method_call
      wp_call
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hpn
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, p
      iframe
      ipureintro; constructor <;> word
    | txn rev ok resps =>
      iunfold opRespMsg at Hp
      icases Hp with ⟨%Hpn, %w, %r, %h, %tsl, %tps, #Hresp, -⟩
      wp_method_call
      wp_call
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hpn
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, p
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end authkv
end EtcdGrove
end Perennial
