/-
The proof of `LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean`: from
`proto.UnmarshalPb.spec` at the registered `walpb.Record` (`pbRecordC`, `pbRecordC_reg`): a success
is D1 (the bytes decode to the record, `recDecode`), the decoded object owned whole (`recOwnC`) is
an `ownRec`; a failure means by D2 that the bytes are no record's encoding (the encoder's records
have no unknown fields, so their contents are valid).
-/
module

public import LinuxFs.Spec.google_golang_org.protobuf.proto.UnmarshalWalRecord
public import LinuxFs.Spec.google_golang_org.protobuf.proto.UnmarshalPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem recCell_optPtsTo {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (o : Option V) : recCell (GF := GF) p o ⊢ optPtsTo p (o.getD (zero_val V)) := by
  cases o <;> simp only [recCell, optPtsTo, Option.getD]
  · iintro %h; ileft; ipureintro; exact ⟨h, trivial⟩
  · iintro #H; iright; iexact H

theorem recBytesOwn_own (ds : GoSlice) (o : Option (List w8)) :
    recBytesOwn (GF := GF) ds o ⊢ ds ↦* (o.getD []) := by
  cases o <;> simp only [recBytesOwn, Option.getD]
  · iintro %h; subst h; iapply ownSlice_nil
  · iintro ⟨-, H⟩; iexact H

/-- The decoded record, owned whole, is an `ownRec` of its model. -/
theorem recOwnC_ownRec (l : Loc) (c : RecC) : recOwnC (GF := GF) l c ⊢ ownRec l c.model := by
  unfold recOwnC ownRec
  iintro ⟨%v, Hl, Ht, Hc, Hd, -, -⟩
  iexists v
  iframe Hl
  have e1 : c.model.typ = c.typ.getD (zero_val w64) := rfl
  have e2 : c.model.crc = c.crc.getD (zero_val w32) := rfl
  have e3 : c.model.data = c.data.getD [] := rfl
  rw [e1, e2, e3]
  isplitl [Ht]
  · iapply recCell_optPtsTo v.Type' c.typ; iexact Ht
  isplitl [Hc]
  · iapply recCell_optPtsTo v.Crc' c.crc; iexact Hc
  iapply recBytesOwn_own v.Data' c.data; iexact Hd

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem decC_ownRec (l : Loc) (c : (pbRecordC (GF := GF)).data.C) :
    (pbRecordC (GF := GF)).data.decC l c ⊢ ownRec l ((pbRecordC (GF := GF)).data.modelOf c) :=
  recOwnC_ownRec (hG := hG) l c

theorem proto.UnmarshalWalRecord.wp_proof (HPb : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    proto.UnmarshalWalRecord.spec (GF := GF) (hG := hG) := by
  intro b bs dq l
  have H := HPb pbRecordC pbRecordC_reg b bs dq l
  simp only [pbRecordC_ty] at H
  iintro %Φ ⟨#Hinit, Hb, Hl⟩ HΦ
  iapply H $$ [Hb Hl]
  · iframe; iframe Hinit
  iintro !> %err ⟨Hb, %Hok, Hdec⟩
  by_cases he : err = GoInterface.nil
  · subst he
    ihave ⟨%c, Hm, %Hc⟩ := Hdec $$ %rfl
    obtain ⟨hw, -, -, -⟩ := Hc
    iapply HΦ
    iframe Hb
    ileft
    iexists (pbRecordC (GF := GF)).data.modelOf c
    isplitr
    · ipureintro; exact ⟨rfl, hw⟩
    iapply decC_ownRec l c
    iexact Hm
  · iapply HΦ
    iframe Hb
    iright
    ipureintro
    refine ⟨he, fun r hr => he (Hok ⟨recOf r, trivial, ?_, ?_⟩)⟩
    · exact (pbRecordC_ufValid _).2 (by rw [recOf_uf]; exact ufWire.nil)
    · rw [pbEncC_pbRecordC]; exact hr

end proof

end EtcdGrove
end Perennial
