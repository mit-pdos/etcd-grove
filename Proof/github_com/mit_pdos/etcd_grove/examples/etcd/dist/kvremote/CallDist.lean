/-
Lean-first (no Rocq counterpart).

The proof of `Call_dist.spec` (txnlin's `Call` across machines, P9): copies of txnlin's `callGet`,
`callList`, `callPut`, `callDel`, `callTxn`, `call` and `Call` proofs (`Proof/.../txnlin/`), each with the
in-process servers' facts (`isNewClient ∗ clientWriteOnce ∗ [∗list] kvRegsAt`, one update per member,
the members' `srvStart`) replaced by the view's client facts `kvClientAt cl api eps V Γ` and one
update at `Γ.kv`, over the cross-machine laws of `ClientCallDistLaws.lean` (`client_*_dist.law`,
`txn_Commit_dist.law`) in place of `client_*_st.law`/`txn_Commit_st.law`. The rest of each proof
(the output from the reply) is txnlin's, unchanged. Not a generalization of txnlin's proofs: those keep
their statements (a generalization would be a spec change to txnlin).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.CallDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.ClientCallDistLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.vrOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.kvsFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.withKVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpsFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.opsOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.thenOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.elseOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.txnRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.withRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callPut
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callDel
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callList
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callTxn
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.txn__If
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.TxnPlainSpec

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin go_etcd_io.etcd.server.v3.etcdserver
open EtcdGrove.etcd_dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `callGet` across machines (txnlin's `callGet.spec` at the view). -/
theorem callGet_dist (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_vrOf : vrOf.spec (GF := GF) (hG := hG))
    (h_Get : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Get_dist.law (GF := GF) (hG := hG)) :
    ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∀ (key : GoString) (Q : KVState → IProp GF), key.length ≤ inMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu Γ.kv Q)) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callGet)) (Val #cl))
        (Val #key))
    {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
        ∃ σ : KVState, □ Q σ ∗
          ⌜y = getOut (W64 (σ.rev : Int)) (σ.kvs.filter fun v => decide (v.key = key)) ∧
            kvRevFits σ.rev⌝) }} := by
  intro _ π cl api eps V Γ hAs key Q hkl
  wp_start as ⟨Hlt, #Hkc, #Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  ihave #Hnil := optsAt_nil (GF := GF)
  (try wp_auto)
  wp_apply (h_Get cl api eps V Γ cctx ccd key slice.nil Q
      (opSizeOk_opGetModel (K := inMax) (E := 0) (V := 0) (optsKeep_nil _ _ _) hkl (by decide))) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hkvs, hrev, hb⟩ := Hσ
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_if_destruct
    · obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
        have : 0 < ps.length := by have := Hsll.1; word
        exact ⟨ps[0], List.getElem?_eq_getElem this⟩
      obtain ⟨kv0, Hkv0⟩ : ∃ kv0, m.kvs[0]? = some kv0 := by
        have : 0 < m.kvs.length := by
          rw [← Hlen]; exact List.length_pos_of_mem (List.mem_of_getElem? Hp0)
        exact ⟨m.kvs[0], List.getElem?_eq_getElem this⟩
      ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
      iunfold txn.kvIs at Hkv
      icases Hkv with ⟨%kSl, %vSl, -, -, -, #HmF, #HvF, #HvalF, #HvS, -⟩
      have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
        have := Hsll.1
        constructor <;> word
      simp only [Hbnd0, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact Hp0
      (try wp_auto)
      wp_apply wp_vrOf vSl kv0.value DFrac.discard kv0.modRev kv0.version $$ [HvS] as -
      · iframe #
      (try wp_auto)
      iapply HΦ
      iframe Hlt
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [← hkvs, hrev]
      cases hk : m.kvs with
      | nil => simp [hk] at Hkv0
      | cons a l =>
        simp only [hk, List.getElem?_cons_zero, Option.some.injEq] at Hkv0
        subst Hkv0
        rfl
    · iapply HΦ
      iframe Hlt
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [← hkvs, hrev]
      have : m.kvs = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← Hlen]; have := Hsll.1; word
      rw [this]
      rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; rfl

/-- `callList` across machines (txnlin's `callList.spec` at the view). -/
theorem callList_dist (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_kvsFrom : kvsFrom.spec (GF := GF) (hG := hG))
    (wp_withKVs : withKVs.spec (GF := GF) (hG := hG))
    (wp_WithRange : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (h_List : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_List_dist.law (GF := GF) (hG := hG)) :
    ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∀ (Q : KVState → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu Γ.kv Q)) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callList)) (Val #cl))
    {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
        ∃ σ : KVState, □ Q σ ∗
          ⌜y = listOut (W64 (σ.rev : Int))
              (σ.kvs.filter fun v => inRange listFrom listTo v.key) ∧ kvRevFits σ.rev⌝) }} := by
  intro _ π cl api eps V Γ hAs Q
  wp_start as ⟨Hlt, #Hkc, #Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  (try wp_auto)
  wp_apply wp_WithRange listTo as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts : optsAt (GF := GF) _ [withRangeM listTo] $$ []
  · unfold optsAt
    iexists [f]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg; subst Hf' Hg; iexact Hf
    · simp at Hf'
  (try wp_auto)
  wp_apply (h_List cl api eps V Γ cctx ccd _ Q
      (opSizeOk_opGetModel (K := inMax) (E := inMax) (V := 0)
        (optsKeep_cons (withRangeM_keep (by decide)) (optsKeep_nil _ _ _)) (by decide) (by decide))) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hkvs, hrev, hb⟩ := Hσ
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    wp_apply wp_kvsFrom sl ps m.kvs as %ko ⟨Hko, -⟩
    · iframe #
    (try wp_auto)
    wp_apply wp_withKVs _ ko _ (DFrac.own 1) $$ [Hko] as %o' ⟨-, %Ho'⟩
    · iframe
    iapply HΦ
    iframe Hlt
    iright
    iexists σ
    iframe HQ
    ipureintro
    refine ⟨?_, hb⟩
    rw [Ho', ← hkvs, hrev]
    rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; rfl

/-- `callPut` across machines (txnlin's `callPut.spec` at the view), auth off. -/
theorem callPut_dist (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (h_Put : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Put_dist.law (GF := GF) (hG := hG)) :
    ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
    Γ.auth = false →
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∀ (key val : GoString) (Q : KVState → IProp GF), key.length ≤ inMax → val.length ≤ inMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ kvOpAu1 Γ.kv (.put (linkv.putOp key val)) Q) }}
      (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callPut))
        (Val #cl)) (Val #key)) (Val #val))
    {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
        ∃ σ : KVState, Q σ ∗
          ⌜y = { zOut with Rev' := W64 ((σ.rev + 1 : Nat) : Int) } ∧ kvRevFits (σ.rev + 1)⌝) }} := by
  intro _ π cl api eps V Γ hauth hAs key val Q hkl hvl
  wp_start as ⟨Hlt, #Hkc, Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  ihave #Hnil := optsAt_nil (GF := GF)
  (try wp_auto)
  wp_apply (h_Put cl api eps V Γ cctx ccd key val slice.nil Q
      (opSizeOk_opPutModel (K := inMax) (E := 0) (V := inMax) (optsKeep_nil _ _ _) hkl hvl (by decide))
      hauth) $$ [$Hlt Hau]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    iexact Hau
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hrev, hb⟩ := Hσ
    iunfold putRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %pk, #Hh, #Hhf, -⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    iapply HΦ
    iframe Hlt
    iright
    iexists σ
    iframe HQ
    ipureintro
    refine ⟨?_, hb⟩
    rw [← hrev]
    rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; rfl

/-- `callDel` across machines (txnlin's `callDel.spec` at the view), auth off. -/
theorem callDel_dist (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (h_Delete : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Delete_dist.law (GF := GF) (hG := hG)) :
    ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
    Γ.auth = false →
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∀ (key : GoString) (Q : KVState → IProp GF), key.length ≤ inMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ kvOpAu1 Γ.kv (.deleteRange (linkv.delOp key)) Q) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callDel)) (Val #cl))
        (Val #key))
    {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
        ∃ σ : KVState, Q σ ∗
          ⌜y = delOut (W64 ((kvOpStep (.deleteRange (linkv.delOp key)) σ).rev : Int))
              (W64 ((rangeIn σ.kvs (linkv.delOp key)).length : Int)) ∧
            kvRevFits (σ.rev + 1)⌝) }} := by
  intro _ π cl api eps V Γ hauth hAs key Q hkl
  wp_start as ⟨Hlt, #Hkc, Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  ihave #Hnil := optsAt_nil (GF := GF)
  (try wp_auto)
  wp_apply (h_Delete cl api eps V Γ cctx ccd key slice.nil Q
      (opSizeOk_opDeleteModel (K := inMax) (E := 0) (V := 0) (optsKeep_nil _ _ _) hkl (by decide))
      hauth) $$ [$Hlt Hau]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    iexact Hau
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hdel, hrev, hb⟩ := Hσ
    iunfold delRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hdelf, -⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    iapply HΦ
    iframe Hlt
    iright
    iexists σ
    iframe HQ
    ipureintro
    refine ⟨?_, hb⟩
    rw [← hrev, ← hdel]
    rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; rfl

/-- `callTxn` across machines (txnlin's `callTxn.spec` at the view), auth off. -/
theorem callTxn_dist (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_cmpsFor : cmpsFor.spec (GF := GF) (hG := hG))
    (wp_opsOf : opsOf.spec (GF := GF) (hG := hG)) (wp_thenOf : thenOf.spec (GF := GF) (hG := hG))
    (wp_elseOf : elseOf.spec (GF := GF) (hG := hG)) (wp_txnRes : txnRes.spec (GF := GF) (hG := hG))
    (wp_withRes : withRes.spec (GF := GF) (hG := hG))
    (h_Txn : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Txn_dist.law (GF := GF) (hG := hG))
    (wp_If : EtcdGrove.txn.If.spec (GF := GF) (hG := hG))
    (wp_Then : EtcdGrove.txn.Then.spec (GF := GF) (hG := hG))
    (wp_Else : EtcdGrove.txn.Else.spec (GF := GF) (hG := hG))
    (h_Commit : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], txn_Commit_dist.law (GF := GF) (hG := hG)) :
    ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
    Γ.auth = false →
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∀ (x : Input) (cs : List (linkv.MCmp GoString GoString)) (t e : List (linkv.MOp GoString GoString))
      (Q : KVState → IProp GF), decIn x = some (.txn cs t e) → t ++ e ≠ [] →
      minBytesLe inMax (.txn cs t e) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ callUpd Γ.kv (.txn cs t e) Q) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callTxn)) (Val #cl))
        (Val #x))
    {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
        ∃ σ : KVState, callRes (.txn cs t e) Q σ ∗
          ⌜y = withResL
              (txnBase (if (linkv.MIn.txn cs t e).isWrite then
                  (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev)
                (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).1)
              (((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
                (linkv.txnOf cs t e)).2.2.map linkv.resOf).map encRes) ∧
            kvRevFits σ.rev⌝) }} := by
  intro _ π cl api eps V Γ hauth hAs x cs t e Q hx hne hb
  obtain ⟨hn, hcs, ht, he⟩ := decIn_txn x cs t e hx
  wp_start as ⟨Hlt, #Hkc, Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`, first
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  (try wp_auto)
  wp_apply wp_elseOf x as %esl ⟨Hesl, -⟩
  wp_apply wp_opsOf esl (elseOfL x) (DFrac.own 1) e he $$ [$Hesl] as %eos ⟨-, #Heos⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_thenOf x as %tsl ⟨Htsl, -⟩
  wp_apply wp_opsOf tsl (thenOfL x) (DFrac.own 1) t ht $$ [$Htsl] as %tos ⟨-, #Htos⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_cmpsFor x cs hcs hn $$ [] as %csl #Hcsl
  · iframe #
  (try wp_auto)
  wp_apply (h_Txn cl api eps V Γ cctx ccd) $$ [$Hlt] as %tv ⟨Hlt, %tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (wp_If tp eps cctx ccd TxnBuild.empty csl (cs.map linkv.cmpOf)) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; simp [TxnBuild.empty]
  (try wp_auto)
  wp_apply ((EtcdGrove.txn.Then.spec_plain wp_Then) tp eps cctx ccd _ tos (t.map clientOp)
      (t.map clientTOp)) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨txnOpOf_clientOps t, rfl, rfl⟩
  (try wp_auto)
  wp_apply ((EtcdGrove.txn.Else.spec_plain wp_Else) tp eps cctx ccd _ eos (e.map clientOp)
      (e.map clientTOp)) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨txnOpOf_clientOps e, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp eps cctx ccd
      ⟨clientTxn cs t e, true, true, true⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, clientTxn]
  (try wp_auto)
  wp_apply (h_Commit cl api tp eps V Γ cctx ccd
      ⟨clientTxn cs t e, true, true, true⟩ Q cs t e rfl hne
      (by
        show txnSizeOk (txnWireOf (clientTxn cs t e))
        rw [txnWireOf_clientTxn]
        exact txnSizeOk_txnOf cs t e (decIn_txn_length x cs t e hx) hb) hauth) $$ [$Hlt Hobj Hau]
    as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    iframe
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hok, hrel, hrev, hb⟩ := Hσ
    iunfold txnRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hsucc, #Hrs, #Hsl, #Hms⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    wp_apply wp_elseOf x as %esl2 ⟨Hesl2, -⟩
    (try wp_auto)
    have hrel' := hrel
    rw [txnOf_branch'] at hrel'
    cases hs : m.succeeded
    · -- the else-branch
      rw [hs] at hrel'
      simp only [Bool.false_eq_true, ↓reduceIte] at hrel'
      have hdec := he
      wp_pures
      ipersist Hesl2
      (try wp_auto)
      wp_apply wp_txnRes esl2 _ _ sl ps _ m.resps hdec hrel' $$ [] as %rsl ⟨Hrsl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_withRes _ rsl _ (DFrac.own 1) $$ [Hrsl] as %o' ⟨-, %Ho'⟩
      · iframe
      iapply HΦ
      iframe Hlt
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [Ho', hrev]
      unfold txnBase
      congr 2
      rw [← hs, hok]
      rfl
    · -- the then-branch
      rw [hs] at hrel'
      simp only [↓reduceIte] at hrel'
      have hdec := ht
      wp_pures
      (try wp_auto)
      wp_apply wp_thenOf x as %osl ⟨Hosl, -⟩
      (try wp_auto)
      ipersist Hosl
      (try wp_auto)
      wp_apply wp_txnRes osl _ _ sl ps _ m.resps hdec hrel' $$ [] as %rsl ⟨Hrsl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_withRes _ rsl _ (DFrac.own 1) $$ [Hrsl] as %o' ⟨-, %Ho'⟩
      · iframe
      iapply HΦ
      iframe Hlt
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [Ho', hrev]
      unfold txnBase
      congr 2
      rw [← hs, hok]
      rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro; rfl

/-- `call` across machines (txnlin's `call.spec` at the view), auth off. -/
theorem call_dist (wp_callGet : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
      ∀ (key : GoString) (Q : KVState → IProp GF), key.length ≤ inMax →
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
          (kvClientAt cl api eps V Γ ∗ □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu Γ.kv Q)) }}
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callGet)) (Val #cl))
          (Val #key))
      {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
          ∃ σ : KVState, □ Q σ ∗
            ⌜y = getOut (W64 (σ.rev : Int)) (σ.kvs.filter fun v => decide (v.key = key)) ∧
              kvRevFits σ.rev⌝) }})
    (wp_callList : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
      ∀ (Q : KVState → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
          (kvClientAt cl api eps V Γ ∗ □ (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu Γ.kv Q)) }}
        (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callList)) (Val #cl))
      {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
          ∃ σ : KVState, □ Q σ ∗
            ⌜y = listOut (W64 (σ.rev : Int))
                (σ.kvs.filter fun v => inRange listFrom listTo v.key) ∧ kvRevFits σ.rev⌝) }})
    (wp_callPut : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
      Γ.auth = false →
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
      ∀ (key val : GoString) (Q : KVState → IProp GF), key.length ≤ inMax → val.length ≤ inMax →
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
          (kvClientAt cl api eps V Γ ∗ kvOpAu1 Γ.kv (.put (linkv.putOp key val)) Q) }}
        (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callPut))
          (Val #cl)) (Val #key)) (Val #val))
      {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
          ∃ σ : KVState, Q σ ∗
            ⌜y = { zOut with Rev' := W64 ((σ.rev + 1 : Nat) : Int) } ∧
              kvRevFits (σ.rev + 1)⌝) }})
    (wp_callDel : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
      Γ.auth = false →
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
      ∀ (key : GoString) (Q : KVState → IProp GF), key.length ≤ inMax →
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
          (kvClientAt cl api eps V Γ ∗ kvOpAu1 Γ.kv (.deleteRange (linkv.delOp key)) Q) }}
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callDel)) (Val #cl))
          (Val #key))
      {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
          ∃ σ : KVState, Q σ ∗
            ⌜y = delOut (W64 ((kvOpStep (.deleteRange (linkv.delOp key)) σ).rev : Int))
                (W64 ((rangeIn σ.kvs (linkv.delOp key)).length : Int)) ∧
              kvRevFits (σ.rev + 1)⌝) }})
    (wp_callTxn : ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
      Γ.auth = false →
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
      ∀ (x : Input) (cs : List (linkv.MCmp GoString GoString))
        (t e : List (linkv.MOp GoString GoString))
        (Q : KVState → IProp GF), decIn x = some (.txn cs t e) → t ++ e ≠ [] →
        minBytesLe inMax (.txn cs t e) →
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
          isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
          (kvClientAt cl api eps V Γ ∗ callUpd Γ.kv (.txn cs t e) Q) }}
        (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.callTxn)) (Val #cl))
          (Val #x))
      {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
          ∃ σ : KVState, callRes (.txn cs t e) Q σ ∗
            ⌜y = withResL
                (txnBase (if (linkv.MIn.txn cs t e).isWrite then
                    (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev)
                  (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).1)
                (((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
                  (linkv.txnOf cs t e)).2.2.map linkv.resOf).map encRes) ∧
              kvRevFits σ.rev⌝) }}) :
    ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
      (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
    Γ.auth = false →
    errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∀ (x : Input) (i : MI) (Q : KVState → IProp GF), decIn x = some i → GenIn x →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
        (kvClientAt cl api eps V Γ ∗ callUpd Γ.kv i Q) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.call)) (Val #cl))
        (Val #x))
    {{ (y : Output), RET #y; levelTok 0 ∗ (⌜y = errOut⌝ ∨
        ∃ σ : KVState, callRes i Q σ ∗
          ⌜y.Err' = false ∧ kvRevFits σ.rev ∧ (GoodKV σ → y = outAt i σ)⌝) }} := by
  intro _ π cl api eps V Γ hauth hAs x i Q hx hgen
  wp_start as ⟨Hlt, #Hkc, Hau⟩
  wp_auto
  unfold callUpd callRes
  rcases decIn_cases x i hx with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨hk, cs, t, e, rfl, hcs, ht, he⟩
  · -- a get
    simp only [linkv.MIn.isWrite, Bool.false_eq_true, ↓reduceIte]
    wp_if_destruct
    · icases Hau with #Hau
      wp_apply wp_callGet cl api eps V Γ hAs x.Key' Q (hgen.2.2 _ hx) $$ [$Hlt] as %y ⟨Hlt, Hy⟩
      · iframe #
      iapply HΦ
      iframe Hlt
      icases Hy with (%Hy | ⟨%σ, #HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, by assumption, fun hg => ?_⟩
        · rw [Hy]; unfold getOut; split <;> rfl
        · rw [Hy]; exact getOut_eq σ hg.1 x.Key'
    · exact absurd hk Hif
  · -- a list
    simp only [linkv.MIn.isWrite, Bool.false_eq_true, ↓reduceIte]
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · icases Hau with #Hau
      wp_apply wp_callList cl api eps V Γ hAs Q $$ [$Hlt] as %y ⟨Hlt, Hy⟩
      · iframe #
      iapply HΦ
      iframe Hlt
      icases Hy with (%Hy | ⟨%σ, #HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, by assumption, fun hg => ?_⟩
        · rw [Hy]; rfl
        · rw [Hy]; exact listOut_eq σ hg
    · exact absurd hk Hif
  · -- a put
    simp only [linkv.MIn.isWrite, ↓reduceIte]
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · wp_apply wp_callPut cl api eps V Γ hauth hAs x.Key' x.Val' Q (hgen.2.2 _ hx).1
          (hgen.2.2 _ hx).2 $$ [$Hlt Hau] as %y ⟨Hlt, Hy⟩
      · iframe #
        iExactEq Hau; rfl
      iapply HΦ
      iframe Hlt
      icases Hy with (%Hy | ⟨%σ, HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, Hb.mono (by omega), fun _ => ?_⟩
        · rw [Hy]; rfl
        · rw [Hy]; exact putOut_eq σ x.Key' x.Val'
    · exact absurd hk Hif
  · -- a delete
    simp only [linkv.MIn.isWrite, ↓reduceIte]
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · wp_apply wp_callDel cl api eps V Γ hauth hAs x.Key' Q (hgen.2.2 _ hx) $$ [$Hlt Hau]
        as %y ⟨Hlt, Hy⟩
      · iframe #
        iExactEq Hau; rfl
      iapply HΦ
      iframe Hlt
      icases Hy with (%Hy | ⟨%σ, HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, Hb.mono (by omega), fun hg => ?_⟩
        · rw [Hy]; rfl
        · rw [Hy]; exact delOut_eq σ hg x.Key'
    · exact absurd hk Hif
  · -- a transaction
    have hne := hgen.2.1 cs t e hx
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_apply wp_callTxn cl api eps V Γ hauth hAs x cs t e Q hx hne (hgen.2.2 _ hx) $$ [$Hlt Hau]
      as %y ⟨Hlt, Hy⟩
    · iframe #
      unfold callUpd
      iexact Hau
    iapply HΦ
    iframe Hlt
    icases Hy with (%Hy | ⟨%σ, HQ, %Hy, %Hb⟩)
    · ileft; ipureintro; exact Hy
    · iright
      iexists σ
      unfold callRes
      iframe HQ
      ipureintro
      refine ⟨?_, Hb, fun hg => ?_⟩
      · rw [Hy]; rfl
      · rw [Hy, ← txnResOut_eq σ hg cs t e]
        split
        · rfl
        · rename_i hw
          rw [kvOpStep_read_rev σ hg _ (by simpa using hw)]
          rfl

/-- **`Call_dist.spec`**: `Call`'s type assertion, then `call_dist` over the copies above. -/
theorem Call_dist.wp_proof (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_vrOf : vrOf.spec (GF := GF) (hG := hG))
    (wp_kvsFrom : kvsFrom.spec (GF := GF) (hG := hG))
    (wp_withKVs : withKVs.spec (GF := GF) (hG := hG))
    (wp_WithRange : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (wp_cmpsFor : cmpsFor.spec (GF := GF) (hG := hG))
    (wp_opsOf : opsOf.spec (GF := GF) (hG := hG)) (wp_thenOf : thenOf.spec (GF := GF) (hG := hG))
    (wp_elseOf : elseOf.spec (GF := GF) (hG := hG)) (wp_txnRes : txnRes.spec (GF := GF) (hG := hG))
    (wp_withRes : withRes.spec (GF := GF) (hG := hG))
    (wp_If : EtcdGrove.txn.If.spec (GF := GF) (hG := hG))
    (wp_Then : EtcdGrove.txn.Then.spec (GF := GF) (hG := hG))
    (wp_Else : EtcdGrove.txn.Else.spec (GF := GF) (hG := hG))
    (h_Get : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Get_dist.law (GF := GF) (hG := hG))
    (h_List : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_List_dist.law (GF := GF) (hG := hG))
    (h_Put : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Put_dist.law (GF := GF) (hG := hG))
    (h_Delete : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Delete_dist.law (GF := GF) (hG := hG))
    (h_Txn : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], client_Txn_dist.law (GF := GF) (hG := hG))
    (h_Commit : ∀ [go_etcd_io.etcd.cache.v3.Assumptions], txn_Commit_dist.law (GF := GF) (hG := hG)) :
    Call_dist.spec (GF := GF) (hG := hG) := by
  intro _ π cl api eps V Γ hauth hAs x i Q hx hgen
  have wp_call := call_dist
    (callGet_dist hWT wp_ErrAny wp_vrOf h_Get)
    (callList_dist hWT wp_ErrAny wp_kvsFrom wp_withKVs wp_WithRange h_List)
    (callPut_dist hWT wp_ErrAny h_Put)
    (callDel_dist hWT wp_ErrAny h_Delete)
    (callTxn_dist hWT wp_ErrAny wp_cmpsFor wp_opsOf wp_thenOf wp_elseOf wp_txnRes wp_withRes
      h_Txn wp_If wp_Then wp_Else h_Commit)
  wp_start as ⟨Hlt, #Hkc, Hau⟩
  wp_auto
  wp_apply wp_call cl api eps V Γ hauth hAs x i Q hx hgen $$ [$Hlt Hau] as %y ⟨Hlt, Hy⟩
  · iframe Hau; iframe #
  iapply HΦ
  iframe Hlt
  icases Hy with (%Hy | ⟨%σ, HQ, %Hy⟩)
  · ileft; ipureintro; subst Hy; rfl
  · iright
    iexists y, σ
    iframe HQ
    ipureintro
    exact ⟨rfl, Hy⟩

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
