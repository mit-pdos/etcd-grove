/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/ConfigChangeContext__JSONModelUnmarshal.lean`
(jsongen's generated code): `jsoncodec.Valid`, then `jdec_ConfigChangeContext` on the struct split
field by field (`membership.ccOwn`), reassembled after.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext__JSONModelUnmarshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jdec_ConfigChangeContext
public import Net.Spec.models_lab.jsoncodec.Valid

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
theorem membership.ConfigChangeContext.JSONModelUnmarshal.wp_proof
    (wp_Valid : models_lab.jsoncodec.Valid.spec (GF := GF) (hG := hG))
    (wp_jdec : membership.jdec_ConfigChangeContext.spec (GF := GF) (hG := hG)) :
    membership.ConfigChangeContext.JSONModelUnmarshal.spec (GF := GF) (hG := hG) := by
  intro jr data dq bs p v r hdec hid hpu hlrn hnm hcu hprom
  obtain ⟨hscan, ms, ⟨hnd, hsome⟩, hobj, hfold⟩ := membership.ccDecode_some hdec
  obtain ⟨⟨vid, ⟨vpu, vlrn⟩, ⟨vnm, vcu⟩⟩, vprom⟩ := v
  simp only at hid hpu hlrn hnm hcu hprom
  subst hid hpu hlrn hnm hcu hprom
  wp_start as ⟨Hd, Hp⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_Valid data dq bs hscan) $$ Hd as Hd
  try wp_auto
  iStructNamed Hp
  ihave %HnnM := typedPointsto_not_null _ _ _ $$ Member
  iStructNamed Member
  ihave %HnnR := typedPointsto_not_null _ _ _ $$ RaftAttributes
  ihave %HnnA := typedPointsto_not_null _ _ _ $$ Attributes
  iStructNamed RaftAttributes
  iStructNamed Attributes
  wp_if_destruct
  · exact absurd rfl Hnn
  try wp_auto
  wp_apply (wp_jdec data dq bs (W64 0) p _ ms membership.ccZero r [] [] hnd
      (fun _ _ h => List.not_mem_nil h) hfold (by simp [hobj]))
    $$ [$Hd ID PeerURLs IsLearner Name ClientURLs IsPromote] as ⟨Hd, %seen', Hown⟩
  · iunfold membership.ccOwn
    iexists slice.nil, slice.nil
    simp only [membership.ccZero]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSlice_nil
    ipureintro; exact ⟨fun _ => trivial, fun _ => trivial⟩
  iunfold membership.ccOwn at Hown
  icases Hown with ⟨%sp, %sc, HID, HPU, HLRN, HNM, HCU, HPROM, Hps, Hcs, -⟩
  try wp_auto
  iapply HΦ
  iframe Hd
  iexists ⟨⟨r.m.id, ⟨sp, r.m.isLearner⟩, ⟨r.m.name, sc⟩⟩, r.promote⟩
  iframe Hps Hcs
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe HPROM
    iapply typedPointsto_combine _ _ _ HnnM
    simp only [TypedPointsto.typedPointstoDef]
    iframe HID
    isplitl [HPU HLRN]
    · iapply typedPointsto_combine _ _ _ HnnR
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · isplitl
      · iapply typedPointsto_combine _ _ _ HnnA
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      · itrivial
  ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
