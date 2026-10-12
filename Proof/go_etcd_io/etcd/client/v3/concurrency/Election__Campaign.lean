/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Campaign.lean`. Lean-first (no Rocq
counterpart).

The transaction (`campaignTxn`) is `tryAcquire`'s without the owner get: it creates the key with
the value at `r`, or finds it (`Responses[0]`), its create revision becoming `leaderRev`, and its
value either the proposal's or replaced by `Proclaim` (whose `ProclaimStep` gives the value,
`proclaimStep_guard`). `waitDeletes(leaderRev - 1)` then gives a state at `R` with no key created
before `leaderRev`: the key is there with that create revision (`leaderAt`) or not
(`campaignLost`); `Campaign` does not look.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Campaign
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Proclaim
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Resign
public import Spec.go_etcd_io.etcd.client.v3.concurrency.waitDeletes
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange
public import Spec.fmt.SprintfNamed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

private theorem B_conv' {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The state before a transaction has positive create revisions. -/
theorem campaign_txnStates_pos (pfx : GoString) (r : w64) (s s' : List EtcdKv) (wrote : Bool) :
    txnStates (GF := GF) pfx r s s' wrote ⊢ ⌜∀ v ∈ s, 0 < sint.Z v.createRev⌝ := by
  unfold txnStates
  split
  · iintro ⟨#H1, -⟩
    ihave %H := etcdState_revs _ _ _ $$ H1
    ipureintro; intro v hv; exact (H v hv).1
  · iintro #H1
    ihave %H := etcdState_revs _ _ _ $$ H1
    ipureintro; intro v hv; exact (H v hv).1

theorem campaign_txnStates_true (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' true ⊢ □ etcdState r pfx s' := by
  unfold txnStates
  simp only [↓reduceIte]
  iintro ⟨-, #H⟩
  iexact H

theorem campaign_txnStates_false (pfx : GoString) (r : w64) (s s' : List EtcdKv) :
    txnStates (GF := GF) pfx r s s' false ⊢ □ etcdState r pfx s := by
  unfold txnStates
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro #H
  iexact H

end lemmas

theorem campaign_len_eq_sint (n : Nat) (x : w64) (h : n = sint.nat x ∧ 0 ≤ sint.Z x) :
    (n : Int) = sint.Z x := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  simp only [sint.nat, sint.Z] at *
  omega

theorem campaign_putOp_txnOpOf (key val : GoString) (id : w64) :
    txnOpOf (opPutModel key val [withLeaseM id]) = some (.put key val id) := by
  simp [opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem campaign_putOp_not_panics (key val : GoString) (id : w64) :
    ¬ (opPutModel key val [withLeaseM id]).putPanics := by
  simp [opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero,
    OpFull.putPanics]

theorem campaignTxn_under (pfx key val : GoString) (lease : w64) (hk : pfx <+: key) :
    (campaignTxn key val lease).Under pfx := by
  obtain ⟨hkk, hke, -⟩ := keyOp_fields key
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [campaignTxn, List.mem_singleton] at hc
    subst hc
    exact keyRangeUnder_key pfx key hk
  · intro op hop
    simp only [campaignTxn, List.mem_singleton] at hop
    subst hop; exact hk
  · intro op hop
    simp only [campaignTxn, List.mem_singleton] at hop
    subst hop
    show KeyRangeUnder pfx (keyOp key).key (keyOp key).base.rangeEnd
    rw [hkk, hke]; exact keyRangeUnder_key pfx key hk

/-- The comparison held: the key was absent, the transaction put it (a write, at `r`). -/
theorem campaignTxn_then (key val : GoString) (lease r : w64) (s : List EtcdKv)
    (hpos : ∀ v ∈ s, 0 < sint.Z v.createRev)
    (h : (runTxn r s (campaignTxn key val lease)).1 = true) :
    (runTxn r s (campaignTxn key val lease)).2.1 = putKv r key val lease s ∧
    txnWrote (runTxn r s (campaignTxn key val lease)).2.2 = true ∧
    (runTxn r s (campaignTxn key val lease)).2.2 = [.put] ∧
    HasKeyValAt key r val (putKv r key val lease s) := by
  have habs : ∀ v ∈ s, v.key ≠ key := by
    intro v hv hvk
    have := acquire_cmp_present key s hpos ⟨v, hv, hvk⟩
    have h' : (campaignTxn key val lease).cmps.all (cmpHolds s) = true := h
    simp only [campaignTxn, createGuard, List.all_cons, List.all_nil, Bool.and_true] at h'
    rw [this] at h'; cases h'
  have hok : (campaignTxn key val lease).cmps.all (cmpHolds s) = true := by
    simp only [campaignTxn, createGuard, List.all_cons, List.all_nil, Bool.and_true]
    exact acquire_cmp_absent key s habs
  have e : runTxn r s (campaignTxn key val lease) = (true, putKv r key val lease s, [.put]) := by
    simp only [runTxn, hok, TxnModel.branch, ite_true]
    simp [campaignTxn, runOps, applyTxnOp]
  rw [e]
  have hfind : s.find? (fun v => decide (v.key = key)) = none := by
    rw [List.find?_eq_none]; intro v hv; simpa using habs v hv
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold putKv; rw [hfind]
  exact ⟨_, btInsert_self_mem _ _, rfl, rfl, rfl⟩

/-- The comparison failed: the key was present, nothing written, the key got. -/
theorem campaignTxn_else (key val : GoString) (lease r : w64) (s : List EtcdKv)
    (h : (runTxn r s (campaignTxn key val lease)).1 = false) :
    (∃ v ∈ s, v.key = key) ∧ (runTxn r s (campaignTxn key val lease)).2.1 = s ∧
    txnWrote (runTxn r s (campaignTxn key val lease)).2.2 = false ∧
    (runTxn r s (campaignTxn key val lease)).2.2 =
      [.range (rangeSel s (keyOp key)) (rangeIn s (keyOp key)).length] := by
  have hpres : ∃ v ∈ s, v.key = key := by
    refine Classical.byContradiction fun hn => ?_
    have habs : ∀ v ∈ s, v.key ≠ key := fun v hv hvk => hn ⟨v, hv, hvk⟩
    have := acquire_cmp_absent key s habs
    have h' : (campaignTxn key val lease).cmps.all (cmpHolds s) = false := h
    simp only [campaignTxn, createGuard, List.all_cons, List.all_nil, Bool.and_true] at h'
    rw [this] at h'; cases h'
  have hok : (campaignTxn key val lease).cmps.all (cmpHolds s) = false := h
  have e : runTxn r s (campaignTxn key val lease) = (false, s,
      [.range (rangeSel s (keyOp key)) (rangeIn s (keyOp key)).length]) := by
    simp only [runTxn, hok, TxnModel.branch]
    simp [campaignTxn, runOps, applyTxnOp]
  rw [e]
  exact ⟨hpres, rfl, rfl, rfl⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Election.Campaign.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG))
    (hLe : Session.Lease.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hWL : EtcdGrove.WithLease.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hProclaim : Election.Proclaim.spec (GF := GF) (hG := hG))
    (hResign : Election.Resign.spec (GF := GF) (hG := hG))
    (hWD : waitDeletes.spec (GF := GF) (hG := hG))
    (hCtx : Client.Ctx.spec (GF := GF) (hG := hG))
    (hSp : EtcdGrove.fmt.SprintfNamed.spec (GF := GF) (hG := hG)) :
    Election.Campaign.spec (GF := GF) (hG := hG) := by
  intro e s γ client id pfx st ctx cs pv lo
  wp_start as ⟨#He, Hst, #Hctx, #Hcc, #Hlo⟩
  ihave #He' := He
  iunfold isElection at He'
  icases He' with ⟨#Hes, #Hepfx, %Hpfx, #Hsess, #Hcl⟩
  iunfold electionState at Hst
  icases Hst with ⟨Hk, Hrv, Hls, Hh, %Hsess0⟩
  wp_auto
  wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply hLe s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply hSp $$ [$Hfmt $Hargs] as %key ⟨Hargs, %Hkey⟩
  · ipureintro
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    refine ⟨Or.inl ((_root_.Perennial.fmt.ArgsWf.cons_string pfx []
      _root_.Perennial.fmt.ArgsWf.nil) _ (List.mem_singleton_self _)), Or.inr ⟨⟨go!"go.etcd.io/etcd/client/v3.LeaseID", ?_, ?_⟩, ?_⟩⟩
    · simp [go_etcd_io.etcd.client.v3.LeaseID.ty]
    · simp [EtcdGrove.fmt.methodlessNamedTypes]
    · show _root_.Perennial.fmt.IsBasicType (underlying go_etcd_io.etcd.client.v3.LeaseID.ty)
      rw [show underlying go_etcd_io.etcd.client.v3.LeaseID.ty = go.int64
        from go.IsUnderlying.is_underlying]
      simp [_root_.Perennial.fmt.IsBasicType, _root_.Perennial.fmt.IsIntType]
  rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at Hkey
  simp only [List.set_cons_succ, List.set_cons_zero] at Hkey
  have Hpk : pfx <+: key := _root_.Perennial.fmt.SprintfOut.str_x_prefix pfx _ _ Hkey
  (try wp_auto)
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hCR key $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"=" .eq _ (.num (W64 0)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #HKV, -, #Hctxf, #Hcctx, -, #HTxn, -, -⟩
  (try wp_auto)
  iunfold isEtcdTxnKV at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, #HElse, #HCommit, -⟩
  wp_apply_raw HIf $$ %TxnBuild.empty %(slice.mk slC (W64 (go.arrayLiteralSize [KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Cmp.ty #c1)])) (W64 (go.arrayLiteralSize [KeyedElement none (ElementExpression go_etcd_io.etcd.client.v3.Cmp.ty #c1)]))) %([createGuard key (W64 0)] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; unfold createGuard; iexact Hc1
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply hLe s γ client id $$ [$Hpkg $Hsess]
  (try wp_auto)
  wp_apply hWL id $$ [$Hcv] as %f0 #Hf0
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f0])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  (try wp_auto)
  ihave #Hopts : optsAt (GF := GF) _ [withLeaseM id] $$ []
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
  wp_apply hPut key pv _ [withLeaseM id] $$ [$Hcv $Hopts] as %opPut #HopPut
  · ipureintro; exact campaign_putOp_not_panics key pv id
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opPut])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opPutModel key pv [withLeaseM id]] : List OpFull) %([.put key pv id] : List TxnOp) [$HB]
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
      simp only [List.map_cons, List.map_nil, campaign_putOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_apply hGet key slice.nil [] $$ [$Hcv $Hnil] as %opKey #HopKey
  · ipureintro; exact keyOp_not_panics
  (try wp_auto)
  wp_apply wp_slice_literal (l := [opKey])
  isplitr
  · ipureintro; rfl
  iintro %slE ⟨HslE, -⟩
  ipersist HslE
  (try wp_auto)
  wp_apply_raw HElse $$ %_ %_ %([keyOp key] : List OpFull) %([.get (keyOp key)] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opKey]
      iframe HslE
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho
        unfold keyOp; iexact HopKey
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl⟩
      simp only [List.map_cons, List.map_nil, keyOp_txnOpOf]
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv' B _ ({ model := campaignTxn key pv id, cif := true, cthen := true, celse := true } : TxnBuild) (by rfl) $$ HB
  wp_apply HCommit $$ %({ model := campaignTxn key pv id, cif := true, cthen := true, celse := true } : TxnBuild) %lo [$HB $Hlo] as %resp %err Hres
  · ipureintro; exact campaignTxn_under pfx key pv id Hpk
  ihave #Hres := txnCommitResultTok_result _ _ _ _ _ $$ Hres
  iunfold txnCommitResult at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts⟩)
  · obtain ⟨e', rfl⟩ : ∃ e', err = GoInterface.ok e' := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e' => exact ⟨e', rfl⟩
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Hne
    iexists st
    unfold electionState
    iframe
    ipureintro; exact Hsess0
  subst Heq
  have hm : ({ model := campaignTxn key pv id, cif := true, cthen := true, celse := true } :
      TxnBuild).model = campaignTxn key pv id := rfl
  rw [hm]
  ihave %hpos := campaign_txnStates_pos pfx r s0 _ _ $$ Hts
  obtain ⟨Hlo_r0, Hr0, Hrmax, Hwf0⟩ := Hrr
  have Hlo_r := Hlo_r0 rfl
  iunfold txnRespAt at Hresp
  icases Hresp with ⟨%hdr, %rsl, %ps, #HH, %Hhdr, #HRev, #HSucc, #HR, #Hps, %Hlens, #Hops⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hps
  (try wp_auto)
  obtain hok | hok : (runTxn r s0 (campaignTxn key pv id)).1 = false ∨
      (runTxn r s0 (campaignTxn key pv id)).1 = true := by
    cases (runTxn r s0 (campaignTxn key pv id)).1 <;> simp
  · obtain ⟨⟨v, hv, hvk⟩, h1, h2, h3⟩ := campaignTxn_else key pv id r s0 hok
    have hb : (campaignTxn key pv id).branch false = [.get (keyOp key)] := rfl
    simp only [h2, h1, hok, hb] at Hlens ⊢
    simp only [h3] at Hlens ⊢
    have hok' : [createGuard key (W64 0)].all (cmpHolds s0) = false := hok
    rw [hok']
    (try wp_auto)
    ihave #Hs := campaign_txnStates_false pfx r s0 s0 $$ Hts
    ihave %Hrevs := etcdState_revs r pfx s0 $$ Hs
    obtain ⟨p0, hp0⟩ : ∃ p, ps[0]? = some p :=
      ⟨ps[0]'(by simp at Hlens; omega), List.getElem?_eq_getElem _⟩
    have h0 : sint.Z (W64 0) = 0 := by decide
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
      rw [h0]; have := campaign_len_eq_sint _ _ Hlen; simp at Hlens; omega))]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) ps _ p0 (by decide) $$ [Hps] as -
    · iframe Hps; ipureintro; exact hp0
    ihave #Hop0 := Hops $$ %0 %p0 %(TxnOp.get (keyOp key)) %(TxnOpResult.range (rangeSel s0 (keyOp key)) (rangeIn s0 (keyOp key)).length) %hp0 %rfl %rfl
    iunfold txnOpRespAt at Hop0
    icases Hop0 with ⟨%Hpnn, %u, #Hu, %w, %rr, %Huw, #Hw, %Hrrnn, #Hrr⟩
    subst Huw
    ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p0 w rr $$ [$Hpbi $Hu $Hw]
    · ipureintro; exact Hpnn
    iunfold rangeRespAt at Hrr
    icases Hrr with ⟨%ksl, %kps, %kvs, #HK, #Hkps, #Hkv, %Hokv, -⟩
    obtain rfl := (keyOp_kvs pfx key s0 kvs Hwf0 Hokv).2 v hv hvk
    iunfold kvPtrsAt at Hkv
    icases Hkv with ⟨%Hkl, #Hkv⟩
    obtain ⟨kp, rfl⟩ : ∃ kp, kps = [kp] := by
      match kps, Hkl with
      | [kp], _ => exact ⟨kp, rfl⟩
    ihave #Hkp := Hkv $$ %0 %kp %v %rfl %rfl
    ihave %Hklen := ownSlice_len _ _ _ $$ Hkps
    (try wp_auto)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len by
      rw [h0]; have := campaign_len_eq_sint _ _ Hklen; simp at this; omega))]
    wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) [kp] _ kp (by decide) $$ [Hkps] as -
    · iframe Hkps; ipureintro; rfl
    iunfold kvValAt at Hkp
    icases Hkp with ⟨%kks, %kvsl, -, -, #Hcr, -, -, #Hval, #Hvsl, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string kvsl v.value DFrac.discard $$ [$Hvsl] as -
    (try wp_auto)
    obtain ⟨hc0, hc1, hc2, -⟩ := Hrevs v hv
    have Hcr_r : sint.Z v.createRev ≤ sint.Z r := Int.le_trans hc1 hc2
    wp_if_destruct
    · -- the same value: it is the proposal at `r`
      ihave #HKV' : keyValAt (GF := GF) pfx key v.createRev v.value r $$ []
      · unfold keyValAt; iexists s0; iframe Hs; ipureintro; exact ⟨v, hv, hvk, rfl, rfl⟩
      have HREV : 0 < sint.Z (v.createRev) ∧ sint.Z (v.createRev) ≤ sint.Z r ∧ sint.Z r ≤ sint.Z (r) := ⟨hc0, Hcr_r, Int.le_refl _⟩
      (try wp_auto)
      wp_apply hWD ctx cs client pfx ((v.createRev) - W64 1) (r) $$ [$Hcl $Hctx $Hcc $Hr] as %werr Hwd
      · ipureintro; exact ⟨Hpfx, by have := HREV.1; word⟩
      icases Hwd with (%Hwne | ⟨%Hwnil, %R, %sw, #HRR, #Hsw, %Hw⟩)
      · obtain ⟨e', rfl⟩ : ∃ e', werr = GoInterface.ok e' := by
          cases werr with
          | nil => exact absurd rfl Hwne
          | ok e' => exact ⟨e', rfl⟩
        (try wp_auto)
        ihave HΦ' : iprop(∀ st' : ElectionSt, electionState e s st' -∗ Φ #(GoInterface.ok e')) $$ [HΦ]
        · iintro %st' Hst'
          iapply HΦ
          iright
          isplitr
          · ipureintro; intro h; cases h
          iexists st'
          iexact Hst'
        ihave #Hctx2 := Hctx
        iNamed Hctx2
        wp_apply HDone as %dch %γd #Hdone
        wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
            iprop(e_ptr ↦ e ∗ client_ptr ↦ client ∗ err_ptr ↦ (GoInterface.ok e' : GoInterface) ∗
              structFieldRef Election go!"leaderKey" e ↦ key ∗
              structFieldRef Election go!"leaderRev" e ↦ (v.createRev) ∗
              structFieldRef Election go!"leaderSession" e ↦ s ∗
              structFieldRef Election go!"hdr" e ↦ (st.hdr) ∗
              (∀ st' : ElectionSt, electionState e s st' -∗ Φ #(GoInterface.ok e')))
            $$ [] [e client err Hk Hrv Hls Hh HΦ'] []
        · iapply BigSepL2.bigSepL2_singleton.2
          iintro ⟨e, client, err, Hk, Hrv, Hls, Hh, HΦ'⟩
          simp only [chan.nonblockingAltClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply context.isContextDone_is_chan $$ Hdone
          iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
          isplit
          · iintro -
            (try wp_auto)
            wp_apply hCtx client (GoInterface.ok cctx) $$ [$Hcv $Hctxf]
            ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
            · iapply etcdReached_zero
            wp_apply hResign e s γ client id pfx ⟨key, (v.createRev), s, (st.hdr)⟩ cctx ccs (W64 0)
              $$ [$Hpkg $He Hk Hrv Hls Hh $Hcctx $H0] as %rerr Hres
            · unfold electionState; iframe; ipureintro; right; rfl
            (try wp_auto)
            icases Hres with (⟨-, Hst'⟩ | ⟨-, %hdr'', Hst', -⟩ | ⟨-, Hst'⟩) <;> iapply HΦ' $$ Hst'
          · iframe
        · iframe
        · iintro ⟨e, client, err, Hk, Hrv, Hls, Hh, HΦ'⟩ -
          (try wp_auto)
          iapply HΦ' $$ %(⟨key, (v.createRev), null, (st.hdr)⟩ : ElectionSt)
          unfold electionState
          iframe
          ipureintro; left; rfl
      subst Hwnil
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists key, (v.createRev), r, (r), R, hdr
      isplitl [Hk Hrv Hls Hh]
      · unfold electionState; iframe; ipureintro; right; rfl
      isplitr
      · unfold hdrRevAt; iframe HRev; ipureintro; exact Hhdr
      iframe HRR HKV'
      have Hmin : ∀ w ∈ sw, sint.Z (v.createRev) ≤ sint.Z w.createRev := by
        intro w hw
        have h1 := Hw.2 w hw
        have h2 : sint.Z ((v.createRev) - W64 1) = sint.Z (v.createRev) - 1 := by have := HREV.1; word
        omega
      isplitr
      · by_cases hh : HasKeyAt key (v.createRev) sw
        · ileft; unfold leaderAt lockedAt; iexists sw; iframe Hsw; ipureintro; exact ⟨hh, Hmin⟩
        · iright; unfold campaignLost; iexists sw; iframe Hsw; ipureintro; exact ⟨hh, Hmin⟩
      ipureintro
      exact ⟨Hpk, HREV.1, HREV.2.1, Hlo_r, HREV.2.2, Hw.1⟩
    · -- a different value: `Proclaim`
      ihave Hst : electionState (GF := GF) e s ⟨key, v.createRev, s, st.hdr⟩ $$ [Hk Hrv Hls Hh]
      · unfold electionState; iframe; ipureintro; right; rfl
      wp_apply hProclaim e s γ client id pfx ⟨key, v.createRev, s, st.hdr⟩ ctx cs pv r
        $$ [$Hpkg $He $Hst $Hctx $Hr] as %perr Hpr
      icases Hpr with (⟨%Hpn, %hdr', Hst, Hfact⟩ | ⟨#Herr, Hrest⟩ | ⟨%Hpne, Hst⟩)
      · obtain ⟨rfl, -⟩ := Hpn
        icases Hfact with (%Hnp | ⟨%r', #Hhr', #Hr', #Hpc, %Hrr'⟩)
        · exact absurd Hpk Hnp
        iunfold proclaimedAt at Hpc
        icases Hpc with ⟨%sp0, %sp, -, #Hsp, %Hstep⟩
        obtain ⟨-, Hkv'⟩ := proclaimStep_guard key v.createRev pv id r' sp0 sp Hstep hc0
        ihave #HKV' : keyValAt (GF := GF) pfx key v.createRev pv r' $$ []
        · unfold keyValAt; iexists sp; iframe Hsp; ipureintro; exact Hkv'
        iunfold electionState at Hst
        icases Hst with ⟨Hk, Hrv, Hls, Hh, -⟩
        (try wp_auto)
        have HREV : 0 < sint.Z (v.createRev) ∧ sint.Z (v.createRev) ≤ sint.Z r ∧ sint.Z r ≤ sint.Z (r') := ⟨hc0, Hcr_r, Hrr'⟩
        (try wp_auto)
        wp_apply hWD ctx cs client pfx ((v.createRev) - W64 1) (r') $$ [$Hcl $Hctx $Hcc $Hr'] as %werr Hwd
        · ipureintro; exact ⟨Hpfx, by have := HREV.1; word⟩
        icases Hwd with (%Hwne | ⟨%Hwnil, %R, %sw, #HRR, #Hsw, %Hw⟩)
        · obtain ⟨e', rfl⟩ : ∃ e', werr = GoInterface.ok e' := by
            cases werr with
            | nil => exact absurd rfl Hwne
            | ok e' => exact ⟨e', rfl⟩
          (try wp_auto)
          ihave HΦ' : iprop(∀ st' : ElectionSt, electionState e s st' -∗ Φ #(GoInterface.ok e')) $$ [HΦ]
          · iintro %st' Hst'
            iapply HΦ
            iright
            isplitr
            · ipureintro; intro h; cases h
            iexists st'
            iexact Hst'
          ihave #Hctx2 := Hctx
          iNamed Hctx2
          wp_apply HDone as %dch %γd #Hdone
          wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
              iprop(e_ptr ↦ e ∗ client_ptr ↦ client ∗ err_ptr ↦ (GoInterface.ok e' : GoInterface) ∗
                structFieldRef Election go!"leaderKey" e ↦ key ∗
                structFieldRef Election go!"leaderRev" e ↦ (v.createRev) ∗
                structFieldRef Election go!"leaderSession" e ↦ s ∗
                structFieldRef Election go!"hdr" e ↦ (hdr') ∗
                (∀ st' : ElectionSt, electionState e s st' -∗ Φ #(GoInterface.ok e')))
              $$ [] [e client err Hk Hrv Hls Hh HΦ'] []
          · iapply BigSepL2.bigSepL2_singleton.2
            iintro ⟨e, client, err, Hk, Hrv, Hls, Hh, HΦ'⟩
            simp only [chan.nonblockingAltClausePre]
            iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
            isplitr
            · ipureintro; rfl
            isplitr
            · iapply context.isContextDone_is_chan $$ Hdone
            iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
            isplit
            · iintro -
              (try wp_auto)
              wp_apply hCtx client (GoInterface.ok cctx) $$ [$Hcv $Hctxf]
              ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
              · iapply etcdReached_zero
              wp_apply hResign e s γ client id pfx ⟨key, (v.createRev), s, (hdr')⟩ cctx ccs (W64 0)
                $$ [$Hpkg $He Hk Hrv Hls Hh $Hcctx $H0] as %rerr Hres
              · unfold electionState; iframe; ipureintro; right; rfl
              (try wp_auto)
              icases Hres with (⟨-, Hst'⟩ | ⟨-, %hdr'', Hst', -⟩ | ⟨-, Hst'⟩) <;> iapply HΦ' $$ Hst'
            · iframe
          · iframe
          · iintro ⟨e, client, err, Hk, Hrv, Hls, Hh, HΦ'⟩ -
            (try wp_auto)
            iapply HΦ' $$ %(⟨key, (v.createRev), null, (hdr')⟩ : ElectionSt)
            unfold electionState
            iframe
            ipureintro; left; rfl
        subst Hwnil
        (try wp_auto)
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists key, (v.createRev), r, (r'), R, hdr
        isplitl [Hk Hrv Hls Hh]
        · unfold electionState; iframe; ipureintro; right; rfl
        isplitr
        · unfold hdrRevAt; iframe HRev; ipureintro; exact Hhdr
        iframe HRR HKV'
        have Hmin : ∀ w ∈ sw, sint.Z (v.createRev) ≤ sint.Z w.createRev := by
          intro w hw
          have h1 := Hw.2 w hw
          have h2 : sint.Z ((v.createRev) - W64 1) = sint.Z (v.createRev) - 1 := by have := HREV.1; word
          omega
        isplitr
        · by_cases hh : HasKeyAt key (v.createRev) sw
          · ileft; unfold leaderAt lockedAt; iexists sw; iframe Hsw; ipureintro; exact ⟨hh, Hmin⟩
          · iright; unfold campaignLost; iexists sw; iframe Hsw; ipureintro; exact ⟨hh, Hmin⟩
        ipureintro
        exact ⟨Hpk, HREV.1, HREV.2.1, Hlo_r, HREV.2.2, Hw.1⟩
      · -- `ErrElectionNotLeader`: `Resign`, return the error
        iunfold isPkgErr at Herr
        icases Herr with ⟨-, %Hpne⟩
        obtain ⟨e', rfl⟩ : ∃ e', perr = GoInterface.ok e' := by
          cases perr with
          | nil => exact absurd rfl Hpne
          | ok e' => exact ⟨e', rfl⟩
        ihave Hst : iprop(∃ st'' : ElectionSt, electionState (GF := GF) e s st'') $$ [Hrest]
        · icases Hrest with (⟨-, Hst⟩ | ⟨-, Hst, -⟩) <;> iexists _ <;> iexact Hst
        icases Hst with ⟨%st'', Hst⟩
        (try wp_auto)
        wp_apply hResign e s γ client id pfx st'' ctx cs r $$ [$Hpkg $He $Hst $Hctx $Hr] as %rerr Hres
        (try wp_auto)
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        icases Hres with (⟨-, Hst'⟩ | ⟨-, %hdr'', Hst', -⟩ | ⟨-, Hst'⟩) <;> iexists _ <;> iexact Hst'
      · obtain ⟨e', rfl⟩ : ∃ e', perr = GoInterface.ok e' := by
          cases perr with
          | nil => exact absurd rfl Hpne
          | ok e' => exact ⟨e', rfl⟩
        (try wp_auto)
        wp_apply hResign e s γ client id pfx _ ctx cs r $$ [$Hpkg $He $Hst $Hctx $Hr] as %rerr Hres
        (try wp_auto)
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        icases Hres with (⟨-, Hst'⟩ | ⟨-, %hdr'', Hst', -⟩ | ⟨-, Hst'⟩) <;> iexists _ <;> iexact Hst'
  · obtain ⟨h1, h2, h3, hkv⟩ := campaignTxn_then key pv id r s0 hpos hok
    have hb : (campaignTxn key pv id).branch true = [.put key pv id] := rfl
    simp only [h2, h1, hok, hb] at Hlens ⊢
    simp only [h3] at Hlens ⊢
    have hok' : [createGuard key (W64 0)].all (cmpHolds s0) = true := hok
    rw [hok']
    ihave #Hs := campaign_txnStates_true pfx r s0 _ $$ Hts
    ihave #HKV' : keyValAt (GF := GF) pfx key r pv r $$ []
    · unfold keyValAt; iexists _; iframe Hs; ipureintro; exact hkv
    have HREV : 0 < sint.Z (r) ∧ sint.Z (r) ≤ sint.Z r ∧ sint.Z r ≤ sint.Z (r) := ⟨Hr0, Int.le_refl _, Int.le_refl _⟩
    (try wp_auto)
    wp_apply hWD ctx cs client pfx ((r) - W64 1) (r) $$ [$Hcl $Hctx $Hcc $Hr] as %werr Hwd
    · ipureintro; exact ⟨Hpfx, by have := HREV.1; word⟩
    icases Hwd with (%Hwne | ⟨%Hwnil, %R, %sw, #HRR, #Hsw, %Hw⟩)
    · obtain ⟨e', rfl⟩ : ∃ e', werr = GoInterface.ok e' := by
        cases werr with
        | nil => exact absurd rfl Hwne
        | ok e' => exact ⟨e', rfl⟩
      (try wp_auto)
      ihave HΦ' : iprop(∀ st' : ElectionSt, electionState e s st' -∗ Φ #(GoInterface.ok e')) $$ [HΦ]
      · iintro %st' Hst'
        iapply HΦ
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists st'
        iexact Hst'
      ihave #Hctx2 := Hctx
      iNamed Hctx2
      wp_apply HDone as %dch %γd #Hdone
      wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
          iprop(e_ptr ↦ e ∗ client_ptr ↦ client ∗ err_ptr ↦ (GoInterface.ok e' : GoInterface) ∗
            structFieldRef Election go!"leaderKey" e ↦ key ∗
            structFieldRef Election go!"leaderRev" e ↦ (r) ∗
            structFieldRef Election go!"leaderSession" e ↦ s ∗
            structFieldRef Election go!"hdr" e ↦ (st.hdr) ∗
            (∀ st' : ElectionSt, electionState e s st' -∗ Φ #(GoInterface.ok e')))
          $$ [] [e client err Hk Hrv Hls Hh HΦ'] []
      · iapply BigSepL2.bigSepL2_singleton.2
        iintro ⟨e, client, err, Hk, Hrv, Hls, Hh, HΦ'⟩
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply context.isContextDone_is_chan $$ Hdone
        iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
        isplit
        · iintro -
          (try wp_auto)
          wp_apply hCtx client (GoInterface.ok cctx) $$ [$Hcv $Hctxf]
          ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
          · iapply etcdReached_zero
          wp_apply hResign e s γ client id pfx ⟨key, (r), s, (st.hdr)⟩ cctx ccs (W64 0)
            $$ [$Hpkg $He Hk Hrv Hls Hh $Hcctx $H0] as %rerr Hres
          · unfold electionState; iframe; ipureintro; right; rfl
          (try wp_auto)
          icases Hres with (⟨-, Hst'⟩ | ⟨-, %hdr'', Hst', -⟩ | ⟨-, Hst'⟩) <;> iapply HΦ' $$ Hst'
        · iframe
      · iframe
      · iintro ⟨e, client, err, Hk, Hrv, Hls, Hh, HΦ'⟩ -
        (try wp_auto)
        iapply HΦ' $$ %(⟨key, (r), null, (st.hdr)⟩ : ElectionSt)
        unfold electionState
        iframe
        ipureintro; left; rfl
    subst Hwnil
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, (r), r, (r), R, hdr
    isplitl [Hk Hrv Hls Hh]
    · unfold electionState; iframe; ipureintro; right; rfl
    isplitr
    · unfold hdrRevAt; iframe HRev; ipureintro; exact Hhdr
    iframe HRR HKV'
    have Hmin : ∀ w ∈ sw, sint.Z (r) ≤ sint.Z w.createRev := by
      intro w hw
      have h1 := Hw.2 w hw
      have h2 : sint.Z ((r) - W64 1) = sint.Z (r) - 1 := by have := HREV.1; word
      omega
    isplitr
    · by_cases hh : HasKeyAt key (r) sw
      · ileft; unfold leaderAt lockedAt; iexists sw; iframe Hsw; ipureintro; exact ⟨hh, Hmin⟩
      · iright; unfold campaignLost; iexists sw; iframe Hsw; ipureintro; exact ⟨hh, Hmin⟩
    ipureintro
    exact ⟨Hpk, HREV.1, HREV.2.1, Hlo_r, HREV.2.2, Hw.1⟩

end proof

end concurrency
end EtcdGrove
end Perennial
