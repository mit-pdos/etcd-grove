/-
`json.Marshal` of a `membership.ConfigChangeContext` (`Spec/encoding/json/MarshalConfigChangeContext.lean`), proved (#24 J2; a
trust-boundary axiom until 2026-11-23): the encoding/json model's `Marshal` (proved,
`Codec/Marshal`) dispatches a `ConfigChangeContext` to its `JSONModelMarshal` (`marshalVia`: a `ConfigChangeContext` has that
method and not `JSONModelMarshalPtr`), whose proof gives the bytes `membership.ccJson`.
-/
module

public import Spec.encoding.json.MarshalConfigChangeContext
public import Spec.encoding.json.Codec.Marshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext__JSONModelMarshal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [json_sem : encoding.json.Assumptions]
variable [mem_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

open go_etcd_io.etcd.server.v3.etcdserver.api in
/-- The codec contract of one `json.Marshal(c)` call: the embedded member's URL slices, given back with
the bytes `ccJson c ps cs`. -/
def membership.ccEncJ (m : membership.ConfigChangeContext) (dp dc : DFrac) (ps cs : List GoString) :
    models_lab.jsoncodec.JsonCodec GF :=
  { enc := fun _ Ψ => iprop(m.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Member'.Attributes'.ClientURLs' ↦*{dc} cs ∗
      (m.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps -∗ m.Member'.Attributes'.ClientURLs' ↦*{dc} cs -∗
        Ψ (some (membership.ccJson m ps cs))))
    dec := fun _ _ _ => iprop(False) }

open go_etcd_io.etcd.server.v3.etcdserver.api in
theorem encoding.json.MarshalConfigChangeContext.wp_proof
    (wp_Marshal : _root_.Perennial.encoding.json.Marshal.spec (GF := GF) (hG := hG))
    (wp_method : membership.ConfigChangeContext.JSONModelMarshal.spec (GF := GF) (hG := hG)) :
    encoding.json.MarshalConfigChangeContext.spec (GF := GF) (hG := hG) := by
  intro m dp dc ps cs
  wp_start_folded as ⟨Hp, Hc⟩
  have h1 : go.typeSetContains membership.ConfigChangeContext.ty
      _root_.Perennial.encoding.json.modelMarshalerPtr.ty = false := by go_type_set
  have h2 : go.typeSetContains membership.ConfigChangeContext.ty
      _root_.Perennial.encoding.json.modelMarshaler.ty = true := by go_type_set
  wp_apply (wp_Marshal (membership.ccEncJ m dp dc ps cs) (fun _ _ => (W64 0, W64 0)) _
    (fun r => iprop(⌜r = some (membership.ccJson m ps cs)⌝ ∗
      m.Member'.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Member'.Attributes'.ClientURLs' ↦*{dc} cs))) $$ [Hp Hc] as %s %err Hret
  · iframe
    isplitr
    · simp only [_root_.Perennial.encoding.json.marshalVia, h1, h2, Bool.false_eq_true,
        ↓reduceIte, _root_.Perennial.encoding.json.marshalAt]
      unfold membership.ccEncJ; dsimp only
      iintro %Ψ' %Φ' ⟨Hp, Hc, Hk⟩ Hpost
      wp_apply (wp_method m m dp dc ps cs) $$ [$Hp $Hc] as %s' ⟨Hs, Hcap, Hp, Hc⟩
      icases Hpost with ⟨Hok, -⟩
      iapply Hok $$ Hs Hcap
      iapply Hk $$ Hp Hc
    · unfold membership.ccEncJ; dsimp only
      iframe
      iintro Hp Hc
      iframe
      ipureintro; rfl
  unfold _root_.Perennial.encoding.json.marshalRet
  icases Hret with (⟨%Herr, %bs, Hs, Hcap, %Hbs, Hp, Hc⟩ | ⟨%Herr, %Hbs, -, -⟩)
  · subst Herr
    cases Hbs
    iapply HΦ
    iframe
  · cases Hbs

end proof

end EtcdGrove
end Perennial
