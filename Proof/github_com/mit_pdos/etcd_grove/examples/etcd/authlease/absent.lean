/-
`absent(root, k, why)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): **proved**, over
its callees' specs (as `barrier`'s read, `client_Get_on`): the reply's key-values are none (the caller's
fact), so `len(g.Kvs) != 0` is false and the panic is not reached. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.absent
public import Spec.context.ErrAny
public import Spec.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.ClientOn
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

theorem absent.wp_proof
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    absent.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS root k why addr s E γr cid mid c n F P Q hsz hAs
  wp_start as ⟨Hlt, #Htk, #Hrange, #Hc, #HF, #Hn, #HQ, #Hnone⟩
  ihave #Htk0 := Htk
  iunfold clientTokAt at Htk0
  icases Htk0 with ⟨%api, %conn, #Hkvf, #Hobj, -, -, -⟩
  (try wp_auto)
  -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg wp_WithTimeout wp_ErrAny hAs _)
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -, #HeO⟩
  iunfold metadata.outgoingCtxOkC at HeO
  icases HeO with ⟨%eom, #Heom⟩
  (try wp_auto)
  -- `g, err := root.Get(ctx, k)`
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave Hres := optsAt_res slice.nil [] iprop(True) $$ Hnil
  wp_apply (client_Get_on root api conn addr s E γr cid mid c n ectx eom ecd k slice.nil []
      iprop(True) Q F hsz) $$ [$Hlt Hres] as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    isplitl []
    · itrivial
    rw [show (opGetModel k []).base.sortSet = false from rfl]
    isplitl []
    · unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    isplitl []
    · ipureintro; exact ⟨by simp [opGetPanics, opFold, OpFull.newOp, OpModel.zero], rfl⟩
    iintro !>
    icases HQ with (%hq | #hq)
    · ileft; ipureintro; exact hq
    · iright
      isplitl []
      · ipureintro; rfl
      iexact hq
  icases Hout with ⟨-, (⟨%Herr, %m, #Hm, #Hok, -⟩ | ⟨%Herr, -⟩)⟩
  rotate_left
  · (try wp_auto)
    wp_apply Hecancel
    cases err with
    | nil => exact absurd rfl Herr.1
    | ok e =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; try itrivial
  subst Herr
  (try wp_auto)
  wp_apply Hecancel
  (try wp_auto)
  ihave %Hkv := Hnone $$ %m Hok
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %kvps, #Hh, #Hhf, #Hkvf', #Hsl, #Hkvs, #Hmore, #Hcount⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen', -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hz : sl.len = W64 0 := by
    have hl := Hsll.1
    rw [Hlen', Hkv] at hl
    simp at hl
    word
  (try wp_auto)
  simp only [Hz]
  (try wp_auto)
  iapply HΦ; iframe Hlt; try itrivial

end proof

end etcd_authlease
end EtcdGrove
end Perennial
