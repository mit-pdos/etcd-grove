/-
`json.Marshal` of a `*membership.Member` (`Spec/encoding/json/MarshalMemberPtr.lean`; claim #34 stage 4,
2026-11-25): the encoding/json model's `Marshal` dispatches a `*Member` to its `JSONModelMarshalPtr`
(`marshalVia`: `*Member` has that method), whose proof gives the bytes `membership.memberJson`.
-/
module

public import Spec.encoding.json.MarshalMemberPtr
public import Spec.encoding.json.Codec.Marshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member__JSONModelMarshalPtr

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
/-- The codec contract of one `json.Marshal(&m)` call: the record and its URL slices, given back with
the bytes `memberJson m ps cs`. -/
def membership.memberPtrEncJ (l : Loc) (q : DFrac) (m : membership.Member) (dp dc : DFrac)
    (ps cs : List GoString) : models_lab.jsoncodec.JsonCodec GF :=
  { enc := fun _ Ψ => iprop(l ↦{q} m ∗ m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗
      m.Attributes'.ClientURLs' ↦*{dc} cs ∗
      (l ↦{q} m -∗ m.RaftAttributes'.PeerURLs' ↦*{dp} ps -∗ m.Attributes'.ClientURLs' ↦*{dc} cs -∗
        Ψ (some (membership.memberJson m ps cs))))
    dec := fun _ _ _ => iprop(False) }

open go_etcd_io.etcd.server.v3.etcdserver.api in
theorem encoding.json.MarshalMemberPtr.wp_proof
    (wp_Marshal : _root_.Perennial.encoding.json.Marshal.spec (GF := GF) (hG := hG))
    (wp_method : membership.Member.JSONModelMarshalPtr.spec (GF := GF) (hG := hG)) :
    encoding.json.MarshalMemberPtr.spec (GF := GF) (hG := hG) := by
  intro l q m dp dc ps cs
  wp_start_folded as ⟨Hl, Hp, Hc⟩
  have h1 : go.typeSetContains (go.GoType.PointerType membership.Member.ty)
      _root_.Perennial.encoding.json.modelMarshalerPtr.ty = true := by go_type_set
  wp_apply (wp_Marshal (membership.memberPtrEncJ l q m dp dc ps cs) (fun _ _ => (W64 0, W64 0)) _
    (fun r => iprop(⌜r = some (membership.memberJson m ps cs)⌝ ∗ l ↦{q} m ∗
      m.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ m.Attributes'.ClientURLs' ↦*{dc} cs)))
    $$ [Hl Hp Hc] as %s %err Hret
  · iframe
    isplitr
    · simp only [_root_.Perennial.encoding.json.marshalVia, h1, ↓reduceIte,
        _root_.Perennial.encoding.json.marshalAt]
      unfold membership.memberPtrEncJ; dsimp only
      iintro %Ψ' %Φ' ⟨Hl, Hp, Hc, Hk⟩ Hpost
      wp_apply (wp_method l l q m dp dc ps cs) $$ [$Hl $Hp $Hc] as %s' ⟨Hs, Hcap, Hl, Hp, Hc⟩
      icases Hpost with ⟨Hok, -⟩
      iapply Hok $$ Hs Hcap
      iapply Hk $$ Hl Hp Hc
    · unfold membership.memberPtrEncJ; dsimp only
      iframe
      iintro Hl Hp Hc
      iframe
      ipureintro; rfl
  unfold _root_.Perennial.encoding.json.marshalRet
  icases Hret with (⟨%Herr, %bs, Hs, Hcap, %Hbs, Hl, Hp, Hc⟩ | ⟨%Herr, %Hbs, -, -⟩)
  · subst Herr
    cases Hbs
    iapply HΦ
    iframe
  · cases Hbs

end proof

end EtcdGrove
end Perennial
