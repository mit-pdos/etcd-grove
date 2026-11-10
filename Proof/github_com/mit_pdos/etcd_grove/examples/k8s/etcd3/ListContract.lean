/-
Lean-first (no Rocq counterpart).

# The driver meets the store's list contract (stage 7e-2, `notes/k8s-7e-2-draft.md` §6)

`driver_listContractOk`: for a store configuration of the driver (`driverSpec`, `decoderI`,
`versionerI`, as `Main` passes them to `etcd3.New`), the reflect calls on `[]Obj` (the trusted
`reflect` specs at the driver's `Obj` and `meta.GetItemsPtr` at `ObjList`), the decoder's
`DecodeListItem` and the versioner's `UpdateList` meet `listContractOk` on `driverListSpec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListSpecD
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder__DecodeListItem
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__UpdateList
public import Spec.k8s_io.apimachinery.pkg.api.meta.GetItemsPtr
public import Spec.reflect.MakeSlice
public import Spec.reflect.Copy
public import Spec.reflect.Append

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s reflectM

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem forall₂_append_one {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β} {a : α} {b : β}, List.Forall₂ R l1 l2 → R a b →
      List.Forall₂ R (l1 ++ [a]) (l2 ++ [b])
  | [], [], _, _, .nil, h => List.Forall₂.cons h List.Forall₂.nil
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => List.Forall₂.cons h1 (forall₂_append_one h2 h)

theorem driver_listContractOk' (wp_GetItemsPtr : apimeta.GetItemsPtr.spec (GF := GF) (hG := hG))
    (wp_MakeSlice : reflect.MakeSlice.spec (GF := GF) (hG := hG))
    (wp_Copy : reflect.Copy.spec (GF := GF) (hG := hG))
    (wp_Append : reflect.Append.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ⊢
    listContractOk' (driverSpec (GF := GF)) driverListSpec := by
  iintro ⟨#Prf, #Pmeta⟩
  unfold listContractOk'
  isplitr
  · iintro !> %pl %Φ %Hpl HΦ
    wp_apply (wp_GetItemsPtr pl) $$ []
    · iframe #
      ipureintro; exact Hpl
    simp only [driverListSpec, driverSpec, objTyD]
    iexact HΦ
  isplitr
  · iintro !> %rt %m %Φ %Hh HΦ
    wp_apply (wp_MakeSlice rt (W64 0) m) $$ [] as %w ⟨%s, %Hs, Hsl, Hcap⟩
    · iframe #
      ipureintro; exact ⟨Hh.1, by decide, Hh.2.1, Hh.2.2⟩
    iapply HΦ $$ %w %s %Hs.1
    simp only [driverListSpec, itemsAtD]
    iexists []
    iframe
    ipureintro; exact List.Forall₂.nil
  isplitr
  · iintro !> %rt %n %m %os %Φ %Hh HΦ
    obtain ⟨hrt, hn, hn0, hnm, hm⟩ := Hh
    wp_apply (wp_MakeSlice rt n m) $$ [] as %w ⟨%s', %Hs, Hsl, Hcap⟩
    · iframe #
      ipureintro; exact ⟨hrt, hn0, hnm, hm⟩
    iapply HΦ $$ %w %s' %Hs.1
    iintro %v %p %dq %s %Ψ %Hv Hp Hits HΨ
    simp only [driverListSpec, itemsAtD]
    icases Hits with ⟨%vs, Hvs, -, %Hf⟩
    wp_apply (wp_Copy w s' _ v p dq (DFrac.own 1) s vs) $$ [Hsl Hp Hvs] as ⟨Hp, -, Hsl⟩
    · iframe #
      iframe
      ipureintro; exact ⟨Hs.1, Hv⟩
    iapply HΨ $$ Hp
    iexists vs
    have hl : vs.length = sint.nat n := by rw [← Hf.length_eq, hn]
    rw [List.length_replicate, ← hl, List.take_length, List.drop_eq_nil_of_le (by simp),
      List.append_nil]
    iframe
    ipureintro; exact Hf
  · iintro !> %v %p %dq %s %os %e %esl %dqe %q %o %rv %Φ %Hh Hp Hits Hesl Ho HΦ
    simp only [driverListSpec, itemsAtD, driverSpec]
    icases Hits with ⟨%vs, Hvs, Hcap, %Hf⟩
    iunfold objAtD at Ho
    icases Ho with ⟨%q', %n, %Hq, Hq⟩
    obtain ⟨Hqq, hq, hrv⟩ := Hq
    have hqq : q' = q := by
      have h := ((interface_mkOk_inj _ _ _ _).1 Hqq).2
      exact (go.intoVal_inj h).symm
    subst hqq
    wp_apply (wp_Append v p dq s vs e esl dqe q' (DFrac.own 1) (o.toObj n)) $$ [Hesl Hp Hvs Hcap Hq]
      as %w ⟨%s', %Hw, Hesl, Hvs, Hcap, Hp, Hq⟩
    · iframe #
      iframe
      ipureintro; exact Hh
    iapply HΦ $$ %w %s' %Hw Hp [Hvs Hcap] Hesl
    · iexists vs ++ [o.toObj n]
      iframe
      ipureintro
      exact forall₂_append_one Hf ⟨n, rfl, hrv⟩
    iunfold objAtD
    iexists q', n
    iframe
    ipureintro; exact ⟨Hqq, hq, hrv⟩

theorem driver_listContractOk (wp_GetItemsPtr : apimeta.GetItemsPtr.spec (GF := GF) (hG := hG))
    (wp_MakeSlice : reflect.MakeSlice.spec (GF := GF) (hG := hG))
    (wp_Copy : reflect.Copy.spec (GF := GF) (hG := hG))
    (wp_Append : reflect.Append.spec (GF := GF) (hG := hG))
    (wp_DecodeListItem : decoder.DecodeListItem.spec (GF := GF) (hG := hG))
    (wp_UpdateList : versioner.UpdateList.spec (GF := GF) (hG := hG))
    [go_etcd_io.etcd.client.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (c : StoreCfg GF DObj) (hS : c.S = driverSpec) (hdi : c.di = decoderI) (hvi : c.vi = versionerI) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ⊢
    listContractOk c driverListSpec := by
  iintro ⟨#Hpkg, #Prf, #Pmeta⟩
  unfold listContractOk
  rw [hS, hdi, hvi]
  isplitr
  · iapply driver_listContractOk' wp_GetItemsPtr wp_MakeSlice wp_Copy wp_Append
    iframe #
  isplitr
  · iintro !> %ctx %dsl %d %rev %nf %Φ #Hd #Hnf HΦ
    simp only [decoderI]
    wp_apply (wp_DecodeListItem ctx dsl d rev nf) $$ [] as %x %err Hr
    · iframe #
    iapply HΦ
    simp only [driverSpec, driverCodec]
    cases decodeObjD d <;> simp only <;> iexact Hr
  isplitr
  · iintro !> %pl %os %rv %rv' %cont %cont' %rem %remV %rem0 %Φ Hl Hrem HΦ
    simp only [versionerI]
    wp_apply (wp_UpdateList pl os rv rv' cont cont' rem remV rem0) $$ [$Hl $Hrem] as Hl
    iapply HΦ
    iframe
    ipureintro; rfl
  ipureintro
  simp only [driverListSpec]
  intro h
  have h' : (go.GoType.Named go!"github.com/mit-pdos/etcd-grove/examples/k8s/etcd3.ObjList" [] :
      go.GoType) = go.GoType.Named go!"k8s.io/apimachinery/pkg/apis/meta/v1/unstructured.UnstructuredList" [] := by
    have e1 : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty =
        go.GoType.Named go!"github.com/mit-pdos/etcd-grove/examples/k8s/etcd3.ObjList" [] := by
      with_unfolding_all rfl
    have e2 : k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.UnstructuredList.ty =
        go.GoType.Named go!"k8s.io/apimachinery/pkg/apis/meta/v1/unstructured.UnstructuredList" [] := by
      with_unfolding_all rfl
    rw [← e1, ← e2]; exact h
  simp at h'

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
