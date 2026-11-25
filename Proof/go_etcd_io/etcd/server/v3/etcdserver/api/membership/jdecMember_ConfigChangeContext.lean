/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/jdecMember_ConfigChangeContext.lean`
(jsongen's generated code, membership's `json_model_gen.go`), over `models.lab/jsoncodec`'s decoding
helpers and `jdec_S_string`: the six exact field names, in the generated order.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jdecMember_ConfigChangeContext
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jdec_S_string
public import Net.Spec.models_lab.jsoncodec.Uint
public import Net.Spec.models_lab.jsoncodec.String
public import Net.Spec.models_lab.jsoncodec.Bool
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

set_option goose.wp.extras true

open go_etcd_io.etcd.server.v3.etcdserver.api in
theorem membership.jdecMember_ConfigChangeContext.wp_proof
    (wp_Uint : models_lab.jsoncodec.Uint.spec (GF := GF) (hG := hG))
    (wp_String : models_lab.jsoncodec.String.spec (GF := GF) (hG := hG))
    (wp_Bool : models_lab.jsoncodec.Bool.spec (GF := GF) (hG := hG))
    (wp_jdec_S_string : membership.jdec_S_string.spec (GF := GF) (hG := hG)) :
    membership.jdecMember_ConfigChangeContext.spec (GF := GF) (hG := hG) := by
  intro b dq bs i key p e r r' seen v c rest hseen hset hb hc
  wp_start as ⟨Hb, Hown⟩
  iunfold membership.ccOwn at Hown
  icases Hown with ⟨%sp, %sc, Hid, Hpu, Hlrn, Hnm, Hcu, Hprom, Hps, Hcs, %Hnil⟩
  have hcE : JsonScan.numEnd c := by
    rcases hc with rfl | rfl
    · exact JsonScan.numEnd_comma
    · exact JsonScan.numEnd_rb
  have Hnil' : ∀ k, (go!"peerURLs" ∉ k :: seen → sp = slice.nil) ∧
      (go!"clientURLs" ∉ k :: seen → sc = slice.nil) := fun k =>
    ⟨fun h => Hnil.1 (fun h' => h (List.mem_cons_of_mem _ h')),
     fun h => Hnil.2 (fun h' => h (List.mem_cons_of_mem _ h'))⟩
  unfold membership.ccSet at hset
  wp_auto
  by_cases hk1 : key = go!"id"
  · rw [if_pos hk1] at hset
    subst hk1
    cases v with
    | num n =>
      dsimp only at hset
      by_cases hn : n < 2 ^ 64
      case neg => rw [if_neg hn] at hset; cases hset
      rw [if_pos hn] at hset
      cases hset
      wp_if_destruct
      all_goals try (exact absurd rfl Hif)
      wp_apply (wp_Uint b dq bs i (W64 18446744073709551615) n c rest hcE
        (by simpa [membership.JVal.json] using hb) (by word)) $$ Hb as Hb
      try wp_auto
      simp only [membership.JVal.json]
      iapply HΦ
      iframe
      iunfold membership.ccOwn
      iexists sp, sc
      iframe
      ipureintro; exact Hnil' _
    | _ => cases hset
  rw [if_neg hk1] at hset
  wp_if_destruct
  all_goals try (exact absurd rfl hk1)
  by_cases hk2 : key = go!"peerURLs"
  · rw [if_pos hk2] at hset
    subst hk2
    cases hs : membership.strsOf v with
    | none => rw [hs] at hset; cases hset
    | some xs =>
      rw [hs] at hset
      cases hset
      have hsp := Hnil.1 hseen
      subst hsp
      wp_if_destruct
      all_goals try (exact absurd rfl Hif)
      wp_apply (wp_jdec_S_string b dq bs i _ e v xs (c :: rest) hs hb) $$ [$Hb $Hpu] as ⟨Hb, %s', Hpu, Hs'⟩
      try wp_auto
      iapply HΦ
      iframe
      iunfold membership.ccOwn
      iexists s', sc
      iframe
      ipureintro
      exact ⟨fun h => absurd (List.mem_cons_self) h, (Hnil' _).2⟩
  rw [if_neg hk2] at hset
  wp_if_destruct
  all_goals try (exact absurd rfl hk2)
  by_cases hk3 : key = go!"isLearner"
  · rw [if_pos hk3] at hset
    subst hk3
    cases v with
    | bool x =>
      dsimp only at hset
      cases hset
      wp_if_destruct
      all_goals try (exact absurd rfl Hif)
      have hjb : (membership.JVal.bool x).json = boolLit x := by cases x <;> rfl
      wp_apply (wp_Bool b dq bs i x (c :: rest) (by rw [hb, hjb])) $$ Hb as Hb
      try wp_auto
      rw [← hjb]
      iapply HΦ
      iframe
      iunfold membership.ccOwn
      iexists sp, sc
      iframe
      ipureintro; exact Hnil' _
    | _ => cases hset
  rw [if_neg hk3] at hset
  wp_if_destruct
  all_goals try (exact absurd rfl hk3)
  by_cases hk4 : key = go!"name"
  · rw [if_pos hk4] at hset
    subst hk4
    cases v with
    | str sv =>
      dsimp only at hset
      by_cases hpl : membership.plainStr sv
      case neg => rw [if_neg hpl] at hset; cases hset
      rw [if_pos hpl] at hset
      cases hset
      wp_if_destruct
      all_goals try (exact absurd rfl Hif)
      wp_apply (wp_String b dq bs i sv (c :: rest) hpl
        (by rw [hb]; simp [membership.JVal.json, membership.jquoted])) $$ Hb as Hb
      try wp_auto
      rw [show W64 ((uint.nat i + 1 + sv.length + 1 : Nat) : Int) =
          W64 ((uint.nat i + (membership.JVal.str sv).json.length : Nat) : Int) by
        simp [membership.JVal.json, membership.jquoted]; congr 1; omega]
      iapply HΦ
      iframe
      iunfold membership.ccOwn
      iexists sp, sc
      iframe
      ipureintro; exact Hnil' _
    | _ => cases hset
  rw [if_neg hk4] at hset
  wp_if_destruct
  all_goals try (exact absurd rfl hk4)
  by_cases hk5 : key = go!"clientURLs"
  · rw [if_pos hk5] at hset
    subst hk5
    cases hs : membership.strsOf v with
    | none => rw [hs] at hset; cases hset
    | some xs =>
      rw [hs] at hset
      cases hset
      have hsc := Hnil.2 hseen
      subst hsc
      wp_if_destruct
      all_goals try (exact absurd rfl Hif)
      wp_apply (wp_jdec_S_string b dq bs i _ e v xs (c :: rest) hs hb) $$ [$Hb $Hcu] as ⟨Hb, %s', Hcu, Hs'⟩
      try wp_auto
      iapply HΦ
      iframe
      iunfold membership.ccOwn
      iexists sp, s'
      iframe
      ipureintro
      exact ⟨(Hnil' _).1, fun h => absurd (List.mem_cons_self) h⟩
  rw [if_neg hk5] at hset
  wp_if_destruct
  all_goals try (exact absurd rfl hk5)
  by_cases hk6 : key = go!"isPromote"
  · rw [if_pos hk6] at hset
    subst hk6
    cases v with
    | bool x =>
      dsimp only at hset
      cases hset
      wp_if_destruct
      all_goals try (exact absurd rfl Hif)
      have hjb : (membership.JVal.bool x).json = boolLit x := by cases x <;> rfl
      wp_apply (wp_Bool b dq bs i x (c :: rest) (by rw [hb, hjb])) $$ Hb as Hb
      try wp_auto
      rw [← hjb]
      iapply HΦ
      iframe
      iunfold membership.ccOwn
      iexists sp, sc
      iframe
      ipureintro; exact Hnil' _
    | _ => cases hset
  rw [if_neg hk6] at hset
  wp_if_destruct
  all_goals try (exact absurd rfl hk6)
  cases hset

end proof

end EtcdGrove
end Perennial
