/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/EncodeContinue.lean`. Lean-first (no Rocq counterpart):
`strings.TrimPrefix`; equal to the key (no non-empty prefix) is `fmt.Errorf`'s error; else the token
struct, `json.Marshal` (no error), `RawURLEncoding.EncodeToString` (`rawUrlEncInit`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.EncodeContinue
public import Spec.encoding.json.Marshal
public import Perennial.Proof.strings.Link
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode k8s_etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.EncodeContinue.wp_proof
    (wp_Marshal : encoding.json.Marshal.spec (GF := GF) (hG := hG)) :
    storage.EncodeContinue.spec (GF := GF) (hG := hG) := by
  intro key kp rv
  wp_start
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Pj : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  ihave #Pb : isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply strings.wp_TrimPrefix
  (try wp_auto)
  by_cases hok : encOkL key kp = true
  · have htp : strings.trimPrefix key kp = key.drop kp.length := by
      unfold encOkL at hok; simp only [decide_eq_true_eq] at hok
      simp [strings.trimPrefix, hok.2]
    have hne : ¬ strings.trimPrefix key kp = key := by
      rw [htp]; intro h
      unfold encOkL at hok; simp only [decide_eq_true_eq] at hok
      have := congrArg List.length h
      have hl : kp.length ≠ 0 := fun h0 => hok.1 (List.eq_nil_of_length_eq_zero h0)
      have hle := hok.2.length_le
      simp at this; omega
    rw [decide_eq_false hne]
    (try wp_auto)
    wp_alloc l as Hl
    (try wp_auto)
    wp_apply (wp_Marshal l (DFrac.own 1) _ rfl) $$ [$Hl] as %sl ⟨Hl, Hsl⟩
    (try wp_auto)
    ihave ⟨%e, #He, #Henc⟩ := encoding.base64.rawUrlEncInit_access $$ Pb
    (try wp_auto)
    wp_bind
    iapply Henc $$ Hsl
    inext
    iintro Hsl
    (try wp_auto)
    iapply HΦ
    ipureintro
    simp only [hok, ite_true, and_true]
    rw [encL, ← htp]
  · have heq : strings.trimPrefix key kp = key := by
      unfold strings.trimPrefix
      by_cases h : kp <+: key
      · have : kp = [] := Classical.byContradiction fun hn => hok (by unfold encOkL; simp [hn, h])
        subst this; simp
      · simp [h]
    rw [decide_eq_true heq]
    (try wp_auto)
    ihave Hnil : (slice.nil ↦* ([] : List GoAny) : IProp GF) $$ []
    · iapply ownSlice_nil
    wp_apply (_root_.Perennial.fmt.wp_Errorf _ _ _ _root_.Perennial.fmt.ArgsWf.nil) $$ [$Hnil] as %err -
    (try wp_auto)
    iapply HΦ
    ipureintro
    simp [hok]

end proof

end EtcdGrove
end Perennial
