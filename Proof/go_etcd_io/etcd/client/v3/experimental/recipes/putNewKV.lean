/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/putNewKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.putNewKV
public import Spec.go_etcd_io.etcd.client.v3.Version
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

private theorem B_conv {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

theorem putNewKV.wp_proof (hVer : EtcdGrove.Version.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hWL : EtcdGrove.WithLease.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    putNewKV.spec (GF := GF) (hG := hG) := by
  intro kv pfx key val lease lo
  wp_start as ⟨#Hkv, #Hlo, %Hk⟩
  iunfold isRecipesKV at Hkv
  icases Hkv with ⟨-, #HTxn, -, -⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply hVer key $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num (W64 0)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  wp_apply hWL lease $$ [$Hcv] as %f0 #Hf0
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f0])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  (try wp_auto)
  ihave #Hopts : optsAt (GF := GF) _ [withLeaseM lease] $$ []
  · unfold optsAt
    iexists [f0]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
    · simp at Hf
  wp_apply hPut key val _ [withLeaseM lease] $$ [$Hcv $Hopts] as %opPut #HopPut
  · ipureintro; exact putLeaseOp_not_panics key val lease
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opPut])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  (try wp_auto)
  wp_apply hTODO
  (try wp_auto)
  iunfold isEtcdTxnKVTodo at HTxn
  wp_apply HTxn as %t ⟨%B, HB, #HBs, #HCommit⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, -, -, -⟩
  iunfold txnCommitErrTodo at HCommit
  wp_apply_raw HIf $$ %TxnBuild.empty %_ %([compareM (cmpKeyM .version key) .eq (.num (W64 0))] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opPutModel key val [withLeaseM lease]] : List OpFull) %([.put key val lease] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opPut]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopPut
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      simp only [List.map_cons, List.map_nil, putLeaseOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv B _ ({ model := newKeyTxn key val lease, cif := true, cthen := true, celse := false } : TxnBuild) (by rfl) $$ HB
  wp_apply HCommit $$ %({ model := newKeyTxn key val lease, cif := true, cthen := true, celse := false } : TxnBuild) %lo [$HB $Hlo] as %resp %err ⟨Hres, #Hce⟩
  · ipureintro; exact newKeyTxn_under pfx key val lease Hk
  iunfold txnCommitResultTok at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts, Htok⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    icases Hce with (%Hn | #Hce)
    · exact absurd Hn Hne
    (try wp_auto)
    iapply HΦ
    iright; iright
    iframe Hce
    ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  have hm : ({ model := newKeyTxn key val lease, cif := true, cthen := true, celse := false } :
      TxnBuild).model = newKeyTxn key val lease := rfl
  rw [hm]
  obtain ⟨Hlo_r0, Hr0, Hrmax, Hwf0⟩ := Hrr
  have Hlo_r := Hlo_r0 rfl
  iunfold txnRespAt at Hresp
  icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, -, -, -, -⟩
  (try wp_auto)
  cases hok : (runTxn r s0 (newKeyTxn key val lease)).1
  · -- the key existed
    obtain ⟨hpres, h1, h2⟩ := newKeyTxn_else key val lease r s0 hok
    ihave #Hs0 := txnStates_noWrite pfx r s0 _ _ h2 $$ Hts
    have hok' : (newKeyTxn key val lease).cmps.all (cmpHolds s0) = false := hok
    simp only [newKeyTxn] at hok'
    rw [hok']
    (try wp_auto)
    ihave Hri : (recipesInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hri with ⟨⟨%eK, #HeK, -⟩, -, -, -⟩
    (try wp_auto)
    iapply HΦ
    iright; ileft
    isplitr
    · unfold concurrency.isPkgErr
      iframe HeK
      ipureintro; simp
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr
    isplitr
    · unfold etcdPresent
      iexists s0
      iframe Hs0
      ipureintro; exact hpres
    ipureintro; exact Hlo_r
  · -- the key was created at `r`
    ihave %Hrevs := txnStates_pos' pfx r s0 _ _ $$ Hts
    obtain ⟨habs, h1, h2, hwf', hv⟩ := newKeyTxn_then pfx key val lease r s0 Hwf0 Hk Hrevs hok
    ihave ⟨#Hs0, #Hs1⟩ := txnStates_wrote pfx r s0 _ _ _ h2 h1 $$ Hts
    ihave Htok := tokIf_true h2 _ $$ Htok
    have hok' : (newKeyTxn key val lease).cmps.all (cmpHolds s0) = true := hok
    simp only [newKeyTxn] at hok'
    rw [hok']
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iframe Hr
    isplitr
    · unfold keyCreatedAt etcdAbsent
      isplitr
      · iexists s0
        iframe Hs0
        ipureintro; exact habs
      iexists putKv r key val lease s0
      iframe Hs1
      ipureintro; exact ⟨Hr0, hwf', hv⟩
    iframe Htok
    ipureintro; exact ⟨Hlo_r, Hrmax⟩

end proof

end recipes
end EtcdGrove
end Perennial
