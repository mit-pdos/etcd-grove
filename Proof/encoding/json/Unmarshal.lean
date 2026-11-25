/-
`json.Unmarshal` into a `*membership.ConfigChangeContext` (`Spec/encoding/json/Unmarshal.lean`),
proved (#24 J2 batch 2b; a trust-boundary axiom, D43 M4, until 2026-11-24): the encoding/json model's
`Unmarshal` (proved, `Codec/Unmarshal`) dispatches a `*ConfigChangeContext` to its generated
`JSONModelUnmarshal` (`unmarshalVia`: the pointer type has that method), whose proof decodes the
bytes as `membership.ccDecode` says, with the scanner's contract `scanOk JsonScan.scanF` (linked:
`jsoncodec.scanOk_scanF`).
-/
module

public import Spec.encoding.json.Unmarshal
public import Spec.encoding.json.Codec.Unmarshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext__JSONModelUnmarshal
public import Net.Proof.models_lab.jsoncodec.Scan.Def

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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [json_sem : encoding.json.Assumptions]
variable [mem_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

open go_etcd_io.etcd.server.v3.etcdserver.api in
/-- What one `json.Unmarshal(data, p)` call decodes into `*p` (zero, `v`) when the bytes decode to
`r`: the struct with `r`'s fields and URL lists. -/
def membership.ccDecPost (p : Loc) (r : membership.CcM) : IProp GF :=
  iprop(∃ v' : membership.ConfigChangeContext, p ↦ v' ∗
    v'.Member'.RaftAttributes'.PeerURLs' ↦* r.m.peerURLs ∗
    v'.Member'.Attributes'.ClientURLs' ↦* r.m.clientURLs ∗
    ⌜v'.Member'.ID' = r.m.id ∧ v'.Member'.RaftAttributes'.IsLearner' = r.m.isLearner ∧
      v'.Member'.Attributes'.Name' = r.m.name ∧ v'.IsPromote' = r.promote⌝)

open go_etcd_io.etcd.server.v3.etcdserver.api in
/-- The codec contract of one `json.Unmarshal(data, p)` call into the zero `ConfigChangeContext`
`v`: bytes that decode to `r`, and `*p`. -/
def membership.ccDecJ (p : Loc) (v : membership.ConfigChangeContext) (r : membership.CcM) :
    models_lab.jsoncodec.JsonCodec GF :=
  { enc := fun _ _ => iprop(False)
    dec := fun bs _ Ψ => iprop(⌜membership.ccDecode bs = some r⌝ ∗ p ↦ v ∗
      (membership.ccDecPost p r -∗ Ψ true)) }

/-- Bytes the scanner takes whole are valid to the codec's `jsonValid`. -/
theorem membership.jsonValid_of_scanL (bs : List w8) (h : JsonScan.scanL bs true = (0, bs.length))
    (hl : bs.length < 2 ^ 63) : models_lab.jsoncodec.jsonValid JsonScan.scanF bs := by
  unfold models_lab.jsoncodec.jsonValid JsonScan.scanF
  rw [h]
  have hu : uint.nat (W64 (bs.length : Int)) = bs.length := by word
  refine ⟨rfl, by rw [hu]; exact Nat.le_refl _, ?_⟩
  rw [hu, List.drop_length]; intro c hc; cases hc

open go_etcd_io.etcd.server.v3.etcdserver.api in
theorem encoding.json.Unmarshal.wp_proof
    (wp_Unmarshal : _root_.Perennial.encoding.json.Unmarshal.spec (GF := GF) (hG := hG))
    (wp_method : membership.ConfigChangeContext.JSONModelUnmarshal.spec (GF := GF) (hG := hG))
    (hscan : ⊢ models_lab.jsoncodec.scanOk (GF := GF) JsonScan.scanF models_lab.jsoncodec.scanFn) :
    encoding.json.Unmarshal.spec (GF := GF) (hG := hG) := by
  intro sl bs dq p v id prom hctx
  obtain ⟨r, hdec, hid, hprom, hmem⟩ := membership.ccContextOf_some hctx
  wp_start_folded as ⟨Hsl, Hp, %Hz⟩
  have hz1 := Hz.1; have hz2 := Hz.2.1; have hz3 := Hz.2.2.1; have hz4 := Hz.2.2.2.1
  have hz5 := Hz.2.2.2.2.1; have hz6 := Hz.2.2.2.2.2
  have h1 : go.typeSetContains (go.GoType.PointerType membership.ConfigChangeContext.ty)
      _root_.Perennial.encoding.json.modelUnmarshaler.ty = true := by go_type_set
  ihave %Hlen := ownSlice_len $$ Hsl
  have hscanL := (membership.ccDecode_some hdec).1
  have hl63 : bs.length < 2 ^ 63 := by
    have := Hlen.1; have := Hlen.2
    have : sint.nat sl.len < 2 ^ 63 := by word
    omega
  have hvalid := membership.jsonValid_of_scanL bs hscanL hl63
  wp_apply (wp_Unmarshal (membership.ccDecJ p v r) JsonScan.scanF sl dq bs
    (interface.mkOk (go.GoType.PointerType membership.ConfigChangeContext.ty) #p)
    (fun ok => iprop(⌜ok = true⌝ ∗ membership.ccDecPost p r))) $$ [Hsl Hp]
    as %err ⟨Hsl, Hret⟩
  · iframe
    isplitr [Hp]
    · simp only [_root_.Perennial.encoding.json.unmarshalVia, interface.mkOk, h1, ↓reduceIte]
      isplitr
      · iapply hscan
      unfold _root_.Perennial.encoding.json.unmarshalAt
      iintro %data %dq' %bs' %Ψ %Φ' Hd Hdec Hk
      unfold membership.ccDecJ; dsimp only
      icases Hdec with ⟨%hdec', Hp, Hpost⟩
      have hscan' := (membership.ccDecode_some hdec').1
      ihave %Hlen' := ownSlice_len $$ Hd
      have hl63' : bs'.length < 2 ^ 63 := by
        have := Hlen'.1; have := Hlen'.2
        have : sint.nat data.len < 2 ^ 63 := by word
        omega
      wp_apply (wp_method p data dq' bs' p v r hdec' hz1 hz2 hz3 hz4 hz5 hz6) $$ [$Hd $Hp]
        as ⟨Hd, Hres⟩
      iapply Hk $$ Hd
      ileft
      isplitr
      · ipureintro; exact membership.jsonValid_of_scanL bs' hscan' hl63'
      iexists true
      isplitr
      · ipureintro; simp
      iapply Hpost
      iunfold membership.ccDecPost
      iexact Hres
    · unfold membership.ccDecJ; dsimp only
      iframe
      isplitr
      · ipureintro; exact hdec
      iintro Hpost
      iframe
      ipureintro; rfl
  unfold _root_.Perennial.encoding.json.unmarshalRet
  icases Hret with (⟨-, %ok, %Hok, %Hok', Hpost⟩ | ⟨%Hbad, -⟩)
  · subst Hok'
    have herr : err = GoInterface.nil := Hok.2 rfl
    subst herr
    iunfold membership.ccDecPost at Hpost
    icases Hpost with ⟨%v', Hp, Hpus, Hcus, %Hv'⟩
    iapply HΦ
    rw [hmem]
    iframe
    isplitr
    · ipureintro; rfl
    ipureintro
    obtain ⟨e1, e2, e3, e4⟩ := Hv'
    exact ⟨by rw [e1, hid], by rw [e4, hprom], rfl, e2, e3⟩
  · exact absurd hvalid Hbad.1

end proof

end EtcdGrove
end Perennial
