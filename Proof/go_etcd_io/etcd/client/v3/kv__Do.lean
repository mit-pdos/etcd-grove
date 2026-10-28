/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Do.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.Op__IsSortOptionValid
public import Spec.go_etcd_io.etcd.client.v3.Op__toRangeRequest
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Range
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Put
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__DeleteRange
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Proof.go_etcd_io.etcd.client.v3.KVMembers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Do` for any specs registered at the connection (`doRunGen`): `doOut`. -/
theorem kv.Do.wp_generic
    (wp_IsSortOptionValid : Op.IsSortOptionValid.spec (GF := GF) (hG := hG))
    (wp_toRangeRequest : Op.toRangeRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Range : retryKVClient.Range.spec (GF := GF) (hG := hG))
    (wp_retry_Put : retryKVClient.Put.spec (GF := GF) (hG := hG))
    (wp_retry_DeleteRange : retryKVClient.DeleteRange.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Do.specG (GF := GF) (hG := hG) := by
  intro api conn addr ci cd opv o Sp Qp Sr Qr Sd Qd
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hat, Hrun⟩
  iunfold kvObjAtC at Hkv
  icases Hkv with ⟨%rkv, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, %Hsc⟩
  ihave Hat' := Hat
  iunfold opFullAt at Hat'
  icases Hat' with ⟨-, -, %Hf2, -, -⟩
  obtain ⟨ht, -⟩ := Hf2
  wp_auto
  rw [ht]
  iunfold doRunGen at Hrun
  icases Hrun with (⟨%Ht, #Hsn, #Hrpc, #Hrun⟩ | ⟨%Hp, #Hrpc, Hrun⟩ | ⟨%Hd, #Hrpc, Hrun⟩)
  · -- a range
    rw [Ht]
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_IsSortOptionValid opv o $$ []
    · iframe #
    cases hsv : sortValid o
    · -- an invalid sort option: `rpctypes.ErrInvalidSortOption`
      have hss : o.base.sortSet = true := by
        cases h : o.base.sortSet
        · simp [sortValid, h] at hsv
        · rfl
      simp only [sortNamesIf, hss, ↓reduceIte]
      ihave #Hsn' := Hsn
      iunfold sortNamesOk at Hsn'
      icases Hsn' with ⟨⟨%e, #He, %Hev, #Hse, #Hcl⟩, -, -⟩
      wp_auto
      wp_apply wp_ContextError ci cd e $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
      · iframe #; ipureintro; exact fun _ => Hev.2
      ihave #Hcl' := Hclw $$ Hcl
      iapply HΦ
      unfold doOut
      simp only [Ht, ↓reduceIte]
      unfold rangeCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hev.1).1, (Herr'.2 Hev.1).2, rfl⟩
    wp_auto
    try wp_method_call
    try wp_call
    wp_auto
    wp_apply wp_toRangeRequest opv o $$ [] as %r ⟨%req, Hr, #Hk, #He, %Hreq⟩
    · iframe #; ipureintro; exact Ht
    ihave #Hrun' : □ ▷ attemptPre conn (GoInterface.ok ci) Sr (rangeReqOp req o.key o.base.rangeEnd) Qr $$ []
    · rw [Hreq]; iexact Hrun
    wp_apply wp_retry_Range rkv conn addr Sr Qr ci cd r req o.key o.base.rangeEnd sl vs $$ [Hr]
      as %resp %err ⟨-, Hres⟩
    · iframe #
      iframe
      ipureintro; exact Hcap
    iunfold rangeCallOut at Hres
    icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      simp only [Ht, ↓reduceIte]
      unfold rangeCallOut
      ileft
      iframe Hm
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        unfold doOut
        simp only [Ht, ↓reduceIte]
        unfold rangeCallOut
        iright
        iframe #
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩
  · -- a put
    rw [Hp]
    wp_auto
    ihave Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨Hat0, #Hkey, %Hf2, #Hval, -⟩
    iunfold opAt at Hat0
    icases Hat0 with ⟨%Hf, -⟩
    unfold OpFields at Hf
    obtain ⟨-, hpk, -⟩ := Hf
    obtain ⟨-, -, -, -, hlease, hiv, hil, -⟩ := Hf2
    ihave Hrun' : reqPre conn go!"/etcdserverpb.KV/Put" addr vs (attemptPre conn (GoInterface.ok ci) Sp (putReqOp
        { state' := zeroValDef, Key' := opv.key', Value' := opv.val', Lease' := opv.leaseID',
          PrevKv' := opv.prevKV', IgnoreValue' := opv.ignoreValue',
          IgnoreLease' := opv.ignoreLease', unknownFields' := slice.nil, sizeCache' := 0 }
        o.key o.val) Qp) $$ [Hrun]
    · simp only [putReqOp, putWireOf, hlease, hpk, hiv, hil]
      iapply kvReqPre_conn api rkv conn go!"/etcdserverpb.KV/Put" ⟨go!"Put", rfl⟩ addr vs _ Hsc $$ [Hrun]
      iframe Hremote Hrkv Hrun
    wp_apply wp_retry_Put rkv conn addr Sp Qp ci cd _ _ o.key o.val sl vs $$ [«$r0» Hrun']
      as %resp %err ⟨-, Hres⟩
    · iframe #
      iframe
      try (simp only []; iframe #)
    iunfold putCallOut at Hres
    icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      rw [Hp]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
      unfold putCallOut
      ileft
      iframe Hm
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        unfold doOut
        rw [Hp]; simp only [show (W64 2 = W64 1) = False by decide, ↓reduceIte]
        unfold putCallOut
        iright
        iframe #
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

  · -- a delete
    rw [Hd]
    wp_auto
    ihave Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨Hat0, #Hkey, -, -, -⟩
    iunfold opAt at Hat0
    icases Hat0 with ⟨%Hf, #Hend⟩
    unfold OpFields at Hf
    obtain ⟨-, hpk, -⟩ := Hf
    ihave Hrun' : reqPre conn go!"/etcdserverpb.KV/DeleteRange" addr vs (attemptPre conn (GoInterface.ok ci) Sd (deleteReqOp
        { state' := zeroValDef, Key' := opv.key', RangeEnd' := opv.end', PrevKv' := opv.prevKV',
          unknownFields' := slice.nil, sizeCache' := 0 }
        o.key o.base.rangeEnd) Qd) $$ [Hrun]
    · simp only [deleteReqOp, deleteWireOf, hpk]
      iapply kvReqPre_conn api rkv conn go!"/etcdserverpb.KV/DeleteRange" ⟨go!"DeleteRange", rfl⟩ addr vs _ Hsc $$ [Hrun]
      iframe Hremote Hrkv Hrun
    wp_apply wp_retry_DeleteRange rkv conn addr Sd Qd ci cd _ _ o.key o.base.rangeEnd sl vs
      $$ [«$r0» Hrun'] as %resp %err ⟨-, Hres⟩
    · iframe #
      iframe
      try (simp only []; iframe #)
    iunfold deleteCallOut at Hres
    icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
    · subst Herr
      wp_auto
      iapply HΦ
      unfold doOut
      rw [Hd]; simp only [show (W64 3 = W64 1) = False by decide,
        show (W64 3 = W64 2) = False by decide, ↓reduceIte]
      unfold deleteCallOut
      ileft
      iframe Hm
      ipureintro; rfl
    · obtain ⟨Hne, Hce', Hnull⟩ := Herr
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        wp_auto
        wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        unfold doOut
        rw [Hd]; simp only [show (W64 3 = W64 1) = False by decide,
          show (W64 3 = W64 2) = False by decide, ↓reduceIte]
        unfold deleteCallOut
        iright
        iframe #
        ipureintro
        exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

/-- `kv.Do` on a `*kv` of the members (D44): `kv.Do.wp_generic` at the members' specs, registered
by `isKV`'s registrations (`kvRegs_rpcRange`, ...) and met by the caller's side (`rangeSpec_of`,
...). -/
theorem kv.Do.wp_members
    (wp_IsSortOptionValid : Op.IsSortOptionValid.spec (GF := GF) (hG := hG))
    (wp_toRangeRequest : Op.toRangeRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Range : retryKVClient.Range.spec (GF := GF) (hG := hG))
    (wp_retry_Put : retryKVClient.Put.spec (GF := GF) (hG := hG))
    (wp_retry_DeleteRange : retryKVClient.DeleteRange.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Do.specM (GF := GF) (hG := hG) := by
  intro api ms ci cd opv o c F Q
  iintro %Φ ⟨#Pc, #Hkv, #Hctx, #Hce, Hat, Hrun⟩ HΦ
  iunfold isKV at Hkv
  icases Hkv with ⟨#Hobj, #Hregs⟩
  icases (kvObjAt_conn api (ms.map SrvAt.addr)).1 $$ Hobj with ⟨%conn, #Hobj⟩
  -- the plain specs at every metadata (`GrpcSpec.md`)
  iapply (kv.Do.wp_generic wp_IsSortOptionValid wp_toRangeRequest wp_retry_Range wp_retry_Put
    wp_retry_DeleteRange wp_ContextError api conn (ms.map SrvAt.addr) ci cd opv o
    (GrpcSpec.md (kvPutSpec ms)) (putAns ms F (putWireOf o) Q)
    (GrpcSpec.md (kvRangeSpec ms)) (rangeAns ms c F (rangeWireOf o) Q)
    (GrpcSpec.md (kvDeleteSpec ms)) (delAns ms F (deleteWireOf o) Q)) $$ [Hat Hrun] HΦ
  iframe #
  iframe Hat
  iunfold doRunM at Hrun
  unfold doRunGen
  icases Hrun with (⟨%Ht, #Hsn, #Hk, #Hu⟩ | ⟨%Hp, #HF, Hu⟩ | ⟨%Hd, #HF, Hu⟩)
  · ileft
    isplitl []
    · ipureintro; exact Ht
    iframe Hsn
    isplitl []
    · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcRange ms) $$ Hregs
    imodintro
    inext
    iapply (attemptPre_md conn (GoInterface.ok ci) (kvRangeSpec ms) (rangeWireOf o)
      (rangeAns ms c F (rangeWireOf o) Q))
    iapply (rangeSpec_of ms c F (rangeWireOf o) Q)
    iframe Hk Hu
  · iright
    ileft
    isplitl []
    · ipureintro; exact Hp.1
    isplitl []
    · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcPut ms) $$ Hregs
    iapply (kvReqPre_wand api (ms.map SrvAt.addr) (floorsAt ms F) _ _
      ((putSpec_of ms F (putWireOf o) Q Hp.2).trans
        (attemptPre_md conn (GoInterface.ok ci) (kvPutSpec ms) _ _)))
    iframe HF Hu
  · iright
    iright
    isplitl []
    · ipureintro; exact Hd.1
    isplitl []
    · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcDelete ms) $$ Hregs
    iapply (kvReqPre_wand api (ms.map SrvAt.addr) (floorsAt ms F) _ _
      ((deleteSpec_of ms F (deleteWireOf o) Q Hd.2).trans
        (attemptPre_md conn (GoInterface.ok ci) (kvDeleteSpec ms) _ _)))
    iframe HF Hu

/-- What `kv.Do`'s precondition says of the operation's kind. -/
theorem doRunOk_kind (γ : KVNames) (dup : Bool) (o : OpFull) (Q : KVState → IProp GF) :
    doRunOk (GF := GF) γ dup o Q ⊢ ⌜o.t = W64 1 ∨
      o.t = W64 2 ∨ (o.t = W64 3 ∧ (deleteWireOf o).base.rangeEnd ≠ [W8 0])⌝ ∗
      doRunOk γ dup o Q := by
  unfold doRunOk
  iintro (⟨%H, Hs, #Hu⟩ | ⟨%H, Hu⟩ | ⟨%H, Hu⟩)
  · isplitr
    · ipureintro; exact Or.inl H
    ileft; iframe Hs Hu; ipureintro; exact H
  · isplitr
    · ipureintro; exact Or.inr (Or.inl H.1)
    iright; ileft; iframe Hu; ipureintro; exact H
  · isplitr
    · ipureintro; exact Or.inr (Or.inr H)
    iright; iright; iframe Hu; ipureintro; exact H

/-- `kv.Do` on a `*kv` of etcd's KV `γ` (D44): `kv.Do.wp_members` at its hidden members, from the
floor `[]` and the committed index `0` (`isKv`'s `srvStart`) and the caller's update at each member's
names (`rangeUpd_of`, `putUpd_of`, `delUpd_of`); the reply's fields as the state's
(`rangeAns_st`, `putAns_st`, `delAns_st`). -/
theorem kv.Do.wp_proof
    (wp_IsSortOptionValid : Op.IsSortOptionValid.spec (GF := GF) (hG := hG))
    (wp_toRangeRequest : Op.toRangeRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Range : retryKVClient.Range.spec (GF := GF) (hG := hG))
    (wp_retry_Put : retryKVClient.Put.spec (GF := GF) (hG := hG))
    (wp_retry_DeleteRange : retryKVClient.DeleteRange.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Do.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd opv o Q
  iintro %Φ ⟨#Pc, #Hkv, #Hctx, #Hce, Hat, Hrun⟩ HΦ
  ihave ⟨%Hk, Hrun⟩ := doRunOk_kind γ dup o Q $$ Hrun
  have hdz : o.t ≠ W64 1 → o.t ≠ W64 2 → (deleteWireOf o).base.rangeEnd ≠ [W8 0] :=
    fun h1 h2 => by
      rcases Hk with h | h | ⟨_, h⟩
      · exact absurd h h1
      · exact absurd h h2
      · exact h
  iunfold isKv at Hkv
  icases Hkv with ⟨%ms, #Hkv⟩
  iunfold isKvOf at Hkv
  icases Hkv with ⟨#Hobj, #Hregs, #Hst, %Hm⟩
  obtain ⟨Hn, Hr, Hrb⟩ := Hm
  ihave #HK := srvStart_both ms $$ Hst
  ihave #HF := srvStart_idx ms $$ Hst
  iapply (kv.Do.wp_members wp_IsSortOptionValid wp_toRangeRequest wp_retry_Range wp_retry_Put
    wp_retry_DeleteRange wp_ContextError api ms ci cd opv o (W64 0) [] Q) $$ [Hat Hrun]
  · iframe #
    iframe Hat
    isplitl []
    · iunfold isKV; iframe #
    iunfold doRunOk at Hrun
    unfold doRunM
    icases Hrun with (⟨%Ht, #Hsn, #Hu⟩ | ⟨%Hp, Hu⟩ | ⟨%Hd, Hu⟩)
    · ileft
      isplitl []
      · ipureintro; exact Ht
      iframe Hsn
      isplitl []
      · iunfold knownAt; iexact HK
      ihave #Hu := readAu_upd γ (rangeWireOf o) Q $$ Hu
      iapply (rangeUpd_of ms γ Hn (rangeWireOf o) Q) $$ Hu
    · iright
      ileft
      isplitl []
      · ipureintro; exact Hp
      isplitl []
      · iunfold floorsAt; iexact HF
      ihave Hu := writeAu_upd dup γ _ Q $$ Hu
      iapply (kvReqPre_of_upd api ms (!dup) (noRefusal_of_dup ms dup Hr) _ _
        (putUpd_of ms γ Hn (putWireOf o) Q)) $$ Hu
    · iright
      iright
      isplitl []
      · ipureintro; exact Hd
      isplitl []
      · iunfold floorsAt; iexact HF
      ihave Hu := writeAu_upd dup γ _ Q $$ Hu
      iapply (kvReqPre_of_upd api ms (!dup) (noRefusal_of_dup ms dup Hr) _ _
        (delUpd_of ms γ Hn (deleteWireOf o) Q)) $$ Hu
  inext
  iintro %r %err Hout
  iapply HΦ
  iapply (doOut_mono o _ _ _ _ _ _ r err
    (fun _ m => rangeAns_st Hrb ms (W64 0) [] (rangeWireOf o) Q m)
    (fun _ m => putAns_st Hrb ms [] (putWireOf o) Q m)
    (fun h1 h2 m => delAns_st Hrb ms [] (deleteWireOf o) Q m (hdz h1 h2))) $$ Hout

end proof

end EtcdGrove
end Perennial
