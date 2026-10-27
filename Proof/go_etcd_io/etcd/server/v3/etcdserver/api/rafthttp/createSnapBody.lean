/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/createSnapBody.lean` (rafthttp stage
7d). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createSnapBody
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageEncoder__encode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__fields
public import Spec.bytes.Buffer__Write
public import Spec.io.MultiReader

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- A `bytes.Buffer` is a writer that never fails (`bytes.Buffer.Write.spec`), of any permission. -/
theorem buffer_writerAtF (hW : bytes.Buffer.Write.spec (GF := GF) (hG := hG)) (b : Loc)
    (A : List w8 → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.bytes ⊢
      writerAtF true ⟨go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty, #b⟩
        (bufferM.ownBuffer b) A := by
  iintro #Hpkg
  unfold writerAtF
  iintro !> %p %dq %chunk %bs %Ψ !> ⟨Hp, Hb, -⟩ HΨ
  ihave %Hlen := ownSlice_len p dq chunk $$ Hp
  wp_apply hW b bs p dq chunk $$ [$Hb $Hp] as ⟨Hb, Hp⟩
  iapply HΨ
  iexists chunk.length
  rw [List.take_length]
  iframe
  isplitr
  · ipureintro; refine ⟨?_, Nat.le_refl _, fun _ => rfl⟩
    have : chunk.length < 2 ^ 63 := by have := Hlen.1; word
    word
  isplitr
  · iapply http.errStrOk_nil
  ipureintro; intro _; rfl

theorem rafthttp.createSnapBody.wp_proof
    (hFields : snap.Message.fields.spec (GF := GF) (hG := hG))
    (hEnc : rafthttp.messageEncoder.encode.spec (GF := GF) (hG := hG))
    (hWrite : bytes.Buffer.Write.spec (GF := GF) (hG := hG))
    (hMulti : io.MultiReader.spec (GF := GF) (hG := hG)) :
    rafthttp.createSnapBody.spec (GF := GF) (hG := hG) := by
  intro lg m ml rc st Φ Hlg Hms
  wp_start as ⟨#Hmsg, #Hml, Hrs⟩
  ihave ⟨#HfM, ⟨%tsz, #HfT, -⟩, %rd, %ri, #HfR, %Hrd, #Hwrap, #Hclose⟩ := hFields m ml rc $$ Hmsg
  wp_auto
  rename_i Φs bp
  irename: (bp ↦ (zero_val _root_.Perennial.bytes.Buffer)) => Hb0
  ihave Hbuf := bufferM.ownBuffer_new bp $$ Hb0
  iStructNamed «$r0»
  ipersist w
  ihave #Hbpk : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave #Hwr := buffer_writerAtF hWrite bp (fun _ => iprop(True)) $$ Hbpk
  wp_apply hEnc «$r0_ptr» ⟨go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty, #bp⟩ ml st
      (bufferM.ownBuffer bp) (fun _ => iprop(True)) [] true Hms $$ [$Hbuf]
    as %err ⟨#Herr, %Hnf, %h', Hbuf, Hok⟩
  · iframe #
    iintro !> %bs %_
    isplit <;> itrivial
  have Hen : err = GoInterface.nil := Hnf rfl
  subst Hen
  ihave %Hok := Hok $$ %rfl
  obtain ⟨bs, Hwire, Hbl, Hh⟩ := Hok
  simp only [List.nil_append] at Hh
  subst Hh
  wp_auto
  ihave Hrs' := Hwrap $$ %Φs Hrs
  wp_apply (wp_slice_literal (V := GoInterface)
    [interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #bp, rd])
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, -⟩
  wp_apply hMulti _ _ bp (msgFrame bs) rd Φs $$ [$Hsl $Hbuf $Hrs'] as %mr Hmr
  (try wp_auto)
  wp_alloc rac as Hrac
  iStructNamed Hrac
  ipersist Reader; ipersist Closer
  wp_auto
  iapply HΦ
  iexists bs, ⟨go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.pkg.v3.ioutil.ReaderAndCloser.ty,
    #rac⟩
  isplitr
  · ipureintro; exact ⟨rfl, Hwire, Hbl⟩
  isplitl [Hmr]
  · unfold snapPre snapPhi
    iunfold http.streamHas at Hmr
    icases Hmr with ⟨%Src, %e, #He, #Hsr, HSrc, %Hpc⟩
    iunfold http.streamHas
    iexists Src, e
    iframe #; iframe HSrc
    isplitl
    · iunfold http.streamReaderOk at Hsr
      icases Hsr with ⟨%mri, %Hmri, #HR⟩
      subst Hmri
      iunfold http.streamReaderOk
      iexists _
      isplitr
      · ipureintro; rfl
      iintro !> %r %p %xs %Ψ !> Hpre HΨ
      rw [go_etcd_io.etcd.pkg.v3.ioutil.ReaderAndCloser.TypeAssumptions.ptr_Read_unfold.method_unfold]
      wp_auto
      wp_apply HR $$ [$Hpre]
      iexact HΨ
    ipureintro; exact Hpc
  iunfold rdCloseOk
  iintro !> %Ψ !> - HΨ
  subst Hrd
  rw [go_etcd_io.etcd.pkg.v3.ioutil.ReaderAndCloser.TypeAssumptions.ptr_Close_unfold.method_unfold]
  wp_auto
  wp_apply Hclose
  iexact HΨ

end proof

end EtcdGrove
end Perennial
