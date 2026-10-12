/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStoreTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__notify

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.rest_shift (n : Nat) (L : List Loc) (Φ : Nat → Loc → IProp GF) :
    ([∗list] k ↦ y ∈ L, Φ (n + (k + 1)) y) ⊢ [∗list] k ↦ y ∈ L, Φ (n + 1 + k) y :=
  BigSepL.bigSepL_mono (fun {k y} _ => by rw [show n + (k + 1) = n + 1 + k by omega])

theorem mvcc.set_replicate_step {α : Type} (done : List α) (z e : α) (m : Nat)
    (hm : done.length < m) :
    (done ++ List.replicate (m - done.length) z).set done.length e =
      (done ++ [e]) ++ List.replicate (m - (done.length + 1)) z := by
  obtain ⟨k, hk⟩ : ∃ k, m - done.length = k + 1 := ⟨m - done.length - 1, by omega⟩
  rw [hk, show m - (done.length + 1) = k by omega, List.set_append_right _ _ (by omega)]
  simp [List.replicate_succ]

theorem mvcc.ownToks_join_pred (γr : GName) (b : Nat) (h : 1 ≤ b) :
    ownToks (GF := GF) γr (b - 1) ∗ ownToks γr 1 ⊢ ownToks γr b := by
  have hb : b = (b - 1) + 1 := by omega
  conv => rhs; rw [hb]
  exact (ownToks_add 1 (b - 1) γr).2

/-- A write transaction leaves room for its revision (its token is counted by the budget). -/
theorem mvcc.isTxnWriteCore_room (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log)
    (pend : List mvcc.Change) (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc)
    (b : Bool) :
    mvcc.isTxnWriteCore (GF := GF) mw s γ ilog pend puts deletes putSize chs ps b ⊢
      mvcc.isTxnWriteCore mw s γ ilog pend puts deletes putSize chs ps b ∗
        ⌜ilog.length + 4 ≤ 2 ^ 63⌝ := by
  iintro H
  iunfold mvcc.isTxnWriteCore at H
  iNamed H
  iunfold mvcc.storeTxnWriteCore at Htw
  iNamed Htw
  unfold mvcc.revToken
  icombine Htoks Htok gives %Hle
  isplitl
  · iunfold mvcc.isTxnWriteCore
    iexists tw, ranges
    iframe Hmw
    iunfold mvcc.storeTxnWriteCore
    iexists trace, ti, bt, Locked, ntok
    simp only [named]
    unfold mvcc.revToken
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩
  ipureintro; omega

/-- The writer's unsealed history bounds every synced watcher's delivery: its lower bound is
of a log the writer has committed. -/
theorem mvcc.syncedBelow_of (γ : mvcc.WsNames) (σ : mvcc.WsState) (hok : mvcc.WsOk σ)
    (ilog : mvcc.Log) (pend : List mvcc.Change) :
    ([∗map] w ↦ st ∈ σ.ST, mvcc.memberRes (GF := GF) γ 1 σ w st) ∗
      monoListAuthOwn γ.st.idx.hist 1 (mvcc.histShape ilog pend) ⊢
      ⌜σ.syncedBelow ilog.length⌝ := by
  iintro ⟨Hmem, Hauth⟩
  unfold mvcc.WsState.syncedBelow
  iapply pure_forall.2; iintro %w
  iapply pure_forall.2; iintro %γw
  iapply pure_forall.2; iintro %ed
  by_cases hws : (σ.Ws !! w).isSome
  rotate_left
  · ipureintro; intro h; exact absurd h hws
  by_cases hm : σ.M !! w = some γw
  rotate_left
  · ipureintro; intro _ h; exact absurd h hm
  by_cases he : σ.E !! w = some ed
  rotate_left
  · ipureintro; intro _ _ h; exact absurd h he
  have hlive : σ.live w := Or.inl hws
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 (hok.live_st w hlive)
  icases (BigSepM.bigSepM_lookup_acc hst).1 $$ Hmem with ⟨Hw, -⟩
  iunfold mvcc.memberRes at Hw
  icases Hw with ⟨%γw', %r, %fcs, %hm', -, -, Hw⟩
  rw [if_pos hlive]
  icases Hw with ⟨-, -, -, %evsw, %d, %he', -, -, #Hpop⟩
  iunfold mvcc.popFacts at Hpop
  rw [if_pos hws]
  icases Hpop with ⟨-, Hwf⟩
  iunfold mvcc.evsWf at Hwf
  icases Hwf with ⟨%L, #Hlb, %Hf⟩
  ihave %hp := mono_list_auth_lb_valid _ _ _ _ $$ Hauth Hlb
  ipureintro
  intro _ _ _
  have hpre := mvcc.histOf_prefix_shape_log hp.2
  rw [hm] at hm'; cases hm'
  rw [he] at he'; cases he'
  rcases Hf.2 with h | h
  · exact Or.inl (Nat.le_trans h hpre.length_le)
  · exact Or.inr h

/-- Under the lock, with the sole writer's transaction: the notified log is the writer's, and
the synced watchers are delivered at most up to it (before the seal). -/
theorem mvcc.body_pin (s stw st : Loc) (γ : mvcc.WsNames) (σ : mvcc.WsState) (ilog : mvcc.Log)
    (pend : List mvcc.Change) (chs : GoSlice) (ps : List Loc) :
    mvcc.watchStoreBody (GF := GF) s γ 1 σ ∗ ghostVar γ.wlog (1 : Qp).half ilog ∗
      mvcc.storeTxnWriteCore stw st γ.st ilog pend chs ps false ⊢
      ⌜σ.Lmu = ilog ∧ σ.syncedBelow ilog.length⌝ := by
  iintro ⟨Hb, Hwl, Hc⟩
  iunfold mvcc.watchStoreBody at Hb
  iNamed Hb
  ihave %Hl := ghostVar_agree γ.wlog _ _ _ _ $$ Hwlog Hwl
  iunfold mvcc.storeTxnWriteCore at Hc
  iNamed Hc
  simp only [mvcc.idxWriterB_false]
  iunfold mvcc.idxWriter at Hw
  icases Hw with ⟨Hauth, -, -, -⟩
  ihave %Hbel := mvcc.syncedBelow_of γ σ Hok ilog pend $$ [$Hmem $Hauth]
  ipureintro
  exact ⟨Hl, Hbel⟩

/-- The notified log catches up with the commit. -/
theorem mvcc.body_commit (s : Loc) (γ : mvcc.WsNames) (σ : mvcc.WsState) (L : mvcc.Log)
    (hab : σ.syncedAbove L.length) :
    mvcc.watchStoreBody (GF := GF) s γ 1 σ ∗ ghostVar γ.wlog (1 : Qp).half σ.Lmu ∗
      mvcc.idxCert γ.st.idx L ==∗
      mvcc.watchStoreBody s γ 1 { σ with Lmu := L } ∗ ghostVar γ.wlog (1 : Qp).half L := by
  iintro ⟨Hb, Hwl, #Hc⟩
  iunfold mvcc.watchStoreBody at Hb
  iNamed Hb
  imod ghostVar_update { σ with Lmu := L } γ.wst σ $$ Hσ with Hσ
  imod ghostVar_update_halves L γ.wlog _ _ $$ Hwlog Hwl with ⟨Hwlog, Hwl⟩
  imodintro
  iframe Hwl
  iunfold mvcc.watchStoreBody
  simp only [named]
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hvlen
  isplitr
  · iapply (BigSepM.bigSepM_mono (fun {k v} _ => by unfold mvcc.outRes; exact .rfl)) $$ Hout
  ipureintro
  exact { Hok with synced_d := fun w γw ed h1 h2 h3 => hab w γw ed h1 h2 h3 }

theorem mvcc.watchableStoreTxnWrite.End.wp_proof
    (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hRev : mvcc.storeTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hNotify : mvcc.watchableStore.notify.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro tw s st γ ilog pend puts deletes putSize P f
  wp_start as ⟨Hw, #Hhook, HPh⟩
  iunfold mvcc.isWatchTxnWrite at Hw
  iNamed Hw
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"Changes")]; wp_call
  (try wp_auto)
  wp_apply (hCh mw st γ.st ilog pend puts deletes putSize) $$ [$Htx] as %chs %ps ⟨Hchs, Hkvs, %Hps, Hcore⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
  icases mvcc.isTxnWriteCore_room _ _ _ _ _ _ _ _ _ _ _ $$ Hcore with ⟨Hcore, %Hroom⟩
  (try wp_auto)
  have hpend : pend = [] ↔ chs.len = W64 0 := by
    constructor
    · intro h
      have hz : ps.length = 0 := by rw [Hps, h]; rfl
      rw [← mvcc.W64_sint_nat chs.len Hlen.2, ← Hlen.1, hz]; rfl
    · intro h
      have h1 := Hlen.1
      rw [h] at h1
      exact List.length_eq_zero_iff.1 (by rw [← Hps, h1]; rfl)
  wp_if_destruct
  · -- no change: the inner transaction ends, no revision
    have hnil : pend = [] := hpend.2 Hif
    subst hnil
    (try wp_auto)
    ihave Hte : mvcc.isTxnEnd mw st γ.st (.write ilog [] puts deletes putSize) $$ [Hcore]
    · simp only [mvcc.isTxnEnd]; iexists chs, ps, false; iexact Hcore
    wp_apply (hEnd mw st γ.st (.write ilog [] puts deletes putSize)) $$ [$Hte Hhook HPh]
      as ⟨Hrd, Hpost⟩
    · iapply mvcc.txnEndPre_write; iframe Hhook HPh
    simp only [mvcc.txnEndPost, mvcc.commitLog, ↓reduceIte]
    icases Hpost with ⟨#Hc, Htok⟩
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hc
    iunfold mvcc.watchWriter
    iframe Hc Hwlog
    iapply mvcc.ownToks_join_pred γ.st.revs (mvcc.wBudget ilog) (by unfold mvcc.wBudget; omega)
    unfold mvcc.revToken
    iframe Htok Htoks
  have hne : pend ≠ [] := fun h => Hif (hpend.1 h)
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  iunfold mvcc.isTxnWriteCore at Hcore
  icases Hcore with ⟨%stw, %ranges, Hmw, Hcore⟩
  wp_bind (App (Val #(methods (go.GoType.PointerType metricsTxnWrite.ty) go!"Rev" #mw)) (Val #()))
  rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  wp_apply (hRev stw st γ.st ilog pend chs ps false) $$ [$Hcore] as Hcore
  icases mvcc.storeTxnWriteCore_wf _ _ _ _ _ _ _ _ $$ Hcore with ⟨Hcore, %Hwfc⟩
  (try wp_auto)
  wp_apply wp_slice_make2 (V := Loc) chs.len $$ [] as %esl ⟨Hesl, Hecap⟩
  · ipureintro; exact Hlen.2
  (try wp_auto)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  iunfold mvcc.changesAre at Hkvs
  ihave IH : iprop(∃ (n : w64) (cv : Loc) (iv : w64) (done : List Loc) (evd : List mvcc.EvM),
      "i" ∷ i_ptr ↦ n ∗ "change" ∷ change_ptr ↦ cv ∗ "Higo" ∷ igo ↦ iv ∗
      "Hesl" ∷ esl ↦* (done ++ List.replicate (sint.nat chs.len - sint.nat n) (zero_val Loc)) ∗
      "Hchs" ∷ chs ↦* ps ∗
      "Hrest" ∷ ([∗list] j ↦ p ∈ ps.drop (sint.nat n), ∃ kv : EtcdKv,
        ⌜mvcc.changeKv (W64 ilog.length) (mvcc.stateAfter ilog) pend (sint.nat n + j) = some kv⌝ ∗
        mvcc.kvPtrIs true p kv) ∗
      "Hdone" ∷ ([∗list] x ∈ done.zip evd, mvcc.evIs x.1 x.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z chs.len ∧ done.length = sint.nat n ∧
        evd.length = sint.nat n ∧ evd = (List.range (sint.nat n)).filterMap (fun i =>
          (mvcc.changeKv (W64 ilog.length) (mvcc.stateAfter ilog) pend i).map
            (mvcc.evOfKv ilog.length))⌝) $$ [i change Higo Hesl Hchs Hkvs]
  · iexists W64 0, _, _, [], []
    simp only [named]
    iframe i change Higo Hchs
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.drop_zero, Nat.sub_zero, List.nil_append]
    iframe Hesl
    simp only [Nat.zero_add, List.zip_nil_left]
    iframe Hkvs
    isplitl []
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    ipureintro; refine ⟨by word, Hlen.2, rfl, rfl, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by rw [Hlen.1]; word
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index chs (sint.Z n) ps (DFrac.own 1) p Hn.1 $$ [Hchs] as Hchs
    · iframe; ipureintro; exact Hp
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index chs (sint.Z n) ps (DFrac.own 1) p Hn.1 $$ [Hchs] as Hchs
    · iframe; ipureintro; exact Hp
    (try wp_auto)
    ihave %Hel := ownSlice_len _ _ _ $$ Hesl
    have Hdl := Hn.2.2.1
    have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl.len := by
      refine ⟨Hn.1, ?_⟩
      have h1 := Hel.1
      rw [List.length_append, List.length_replicate] at h1
      word
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index esl (sint.Z n) _ «$r0_ptr» $$ [$Hesl] as Hesl
    · ipureintro
      have h1 := Hel.1
      rw [List.length_append, List.length_replicate] at h1 ⊢
      word
    -- the change's key-value
    have hpe : ps[sint.nat n] = p := by
      have := List.getElem?_eq_getElem Hlt; rw [this] at Hp; exact Option.some.inj Hp
    have hdrop : ps.drop (sint.nat n) = p :: ps.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons Hlt, hpe]
    rw [hdrop]
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hrest with ⟨⟨%kv, %Hkv, Hkvp⟩, Hrest⟩
    iunfold mvcc.kvPtrIs at Hkvp
    simp only [↓reduceIte]
    icases Hkvp with ⟨%ks, %kst, %kuf, %ksc, #Hks, %vs, #Hvs, Hkvp⟩
    ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hkvp
    ihave %Henn := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamedPrefix Hkvp "K"
    iStructNamedPrefix «$r0» "E"
    (try wp_auto)
    have Hset : ((done ++ List.replicate (sint.nat chs.len - sint.nat n) (zero_val Loc)).set
        (sint.Z n).toNat «$r0_ptr»)[(sint.Z n).toNat]? = some «$r0_ptr» := by
      apply List.getElem?_set_self
      have h1 := Hel.1
      rw [List.length_append, List.length_replicate] at h1 ⊢
      word
    wp_if_destruct
    · -- DELETE
      try simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index esl (sint.Z n) _ (DFrac.own 1) «$r0_ptr» Hn.1 $$ [Hesl] as Hesl
      · iframe; ipureintro; exact Hset
      simp only [go_etcd_io.etcd.api.v3.mvccpb.Event_DELETE]
      (try wp_auto)
      try simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index esl (sint.Z n) _ (DFrac.own 1) «$r0_ptr» Hn.1 $$ [Hesl] as Hesl
      · iframe; ipureintro; exact Hset
      (try wp_auto)
      have hN : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
        rw [← mvcc.W64_add_one]; congr 1; omega
      rw [hN]
      ihave Hpk : (p ↦
          ({ state' := kst, Key' := ks, CreateRevision' := kv.createRev,
             ModRevision' := W64 (ilog.length : Int), Version' := kv.version, Value' := vs,
             Lease' := kv.lease, unknownFields' := kuf, sizeCache' := ksc } :
            go_etcd_io.etcd.api.v3.mvccpb.KeyValue) : IProp GF) $$
          [Kstate KKey KCreateRevision KModRevision KVersion KValue KLease KunknownFields KsizeCache]
      · iapply typedPointsto_combine _ _ _ Hpnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave He : («$r0_ptr» ↦
          ({ state' := zero_val _, Type' := W32 1, Kv' := p, PrevKv' := null,
             unknownFields' := slice.nil, sizeCache' := W32 0 } :
            go_etcd_io.etcd.api.v3.mvccpb.Event) : IProp GF) $$ [Estate EType' EKv EPrevKv EunknownFields EsizeCache]
      · iapply typedPointsto_combine _ _ _ Henn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_for_post_core
      ipersist Hpk
      ipersist He
      have hev : mvcc.evOfKv ilog.length kv =
          ⟨true, { kv with modRev := W64 (ilog.length : Int) }, none⟩ := by
        unfold mvcc.evOfKv; rw [if_pos Hif]
      ihave #Hev : mvcc.evIs «$r0_ptr» (mvcc.evOfKv ilog.length kv) $$ []
      · rw [hev]
        iunfold mvcc.evIs
        iexists p, null, _, slice.nil, W32 0
        simp only [mvcc.evType, ↓reduceIte]
        iframe He
        isplitr
        · ipureintro; exact ⟨Henn, Hpnn⟩
        isplitr
        · iunfold mvcc.kvPtrFixed
          iexists ks, vs, kst, kuf, ksc
          iframe Hks Hvs Hpk
        first | (ipureintro; rfl) | (ipureintro; trivial) | itrivial
      (try wp_auto)
      iframe
      iexists n + W64 1, _, _, done ++ [«$r0_ptr»], evd ++ [mvcc.evOfKv ilog.length kv]
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hn1]
      have hset : (done ++ List.replicate (sint.nat chs.len - sint.nat n) (zero_val Loc)).set
          (sint.Z n).toNat «$r0_ptr» =
          (done ++ [«$r0_ptr»]) ++ List.replicate (sint.nat chs.len - (sint.nat n + 1)) (zero_val Loc) := by
        have h1 : (sint.Z n).toNat = done.length := by rw [Hdl]; try rfl
        rw [h1, ← Hdl]
        apply mvcc.set_replicate_step
        first | (rw [Hdl]; word) | rw [Hdl] | word
      rw [hset]
      iframe
      isplitl [Hrest]
      · iapply mvcc.rest_shift (sint.nat n) _ (fun j p => iprop(∃ kv : EtcdKv,
          ⌜mvcc.changeKv (W64 ilog.length) (mvcc.stateAfter ilog) pend j = some kv⌝ ∗
          mvcc.kvPtrIs true p kv)) $$ Hrest
      isplitl [Hdone]
      · rw [List.zip_append (by rw [Hn.2.2.1, Hn.2.2.2.1])]
        simp only [List.zip_cons_cons, List.zip_nil_left]
        iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
        iframe Hdone
        iexact Hev
      ipureintro
      refine ⟨by word, by word, by simp [Hn.2.2.1], by simp [Hn.2.2.2.1], ?_⟩
      rw [List.range_succ, List.filterMap_append, ← Hn.2.2.2.2]
      simp only [Nat.add_zero] at Hkv
      simp only [List.filterMap_cons, List.filterMap_nil, Hkv, Option.map_some, List.append_nil]
    · simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index esl (sint.Z n) _ (DFrac.own 1) «$r0_ptr» Hn.1 $$ [Hesl] as Hesl
      · iframe; ipureintro; exact Hset
      simp only [go_etcd_io.etcd.api.v3.mvccpb.Event_PUT]
      (try wp_auto)
      ihave Hpk : (p ↦
          ({ state' := kst, Key' := ks, CreateRevision' := kv.createRev,
             ModRevision' := kv.modRev, Version' := kv.version, Value' := vs,
             Lease' := kv.lease, unknownFields' := kuf, sizeCache' := ksc } :
            go_etcd_io.etcd.api.v3.mvccpb.KeyValue) : IProp GF) $$
          [Kstate KKey KCreateRevision KModRevision KVersion KValue KLease KunknownFields KsizeCache]
      · iapply typedPointsto_combine _ _ _ Hpnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave He : («$r0_ptr» ↦
          ({ state' := zero_val _, Type' := W32 0, Kv' := p, PrevKv' := null,
             unknownFields' := slice.nil, sizeCache' := W32 0 } :
            go_etcd_io.etcd.api.v3.mvccpb.Event) : IProp GF) $$ [Estate EType' EKv EPrevKv EunknownFields EsizeCache]
      · iapply typedPointsto_combine _ _ _ Henn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_for_post_core
      ipersist Hpk
      ipersist He
      have hev : mvcc.evOfKv ilog.length kv = ⟨false, kv, none⟩ := by
        unfold mvcc.evOfKv; rw [if_neg Hif]
      ihave #Hev : mvcc.evIs «$r0_ptr» (mvcc.evOfKv ilog.length kv) $$ []
      · rw [hev]
        iunfold mvcc.evIs
        iexists p, null, _, slice.nil, W32 0
        simp only [mvcc.evType, Bool.false_eq_true, ↓reduceIte]
        iframe He
        isplitr
        · ipureintro; exact ⟨Henn, Hpnn⟩
        isplitr
        · iunfold mvcc.kvPtrFixed
          iexists ks, vs, kst, kuf, ksc
          iframe Hks Hvs Hpk
        first | (ipureintro; rfl) | (ipureintro; trivial) | itrivial
      (try wp_auto)
      iframe
      iexists n + W64 1, _, _, done ++ [«$r0_ptr»], evd ++ [mvcc.evOfKv ilog.length kv]
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hn1]
      have hset : (done ++ List.replicate (sint.nat chs.len - sint.nat n) (zero_val Loc)).set
          (sint.Z n).toNat «$r0_ptr» =
          (done ++ [«$r0_ptr»]) ++ List.replicate (sint.nat chs.len - (sint.nat n + 1)) (zero_val Loc) := by
        have h1 : (sint.Z n).toNat = done.length := by rw [Hdl]; try rfl
        rw [h1, ← Hdl]
        apply mvcc.set_replicate_step
        first | (rw [Hdl]; word) | rw [Hdl] | word
      rw [hset]
      iframe
      isplitl [Hrest]
      · iapply mvcc.rest_shift (sint.nat n) _ (fun j p => iprop(∃ kv : EtcdKv,
          ⌜mvcc.changeKv (W64 ilog.length) (mvcc.stateAfter ilog) pend j = some kv⌝ ∗
          mvcc.kvPtrIs true p kv)) $$ Hrest
      isplitl [Hdone]
      · rw [List.zip_append (by rw [Hn.2.2.1, Hn.2.2.2.1])]
        simp only [List.zip_cons_cons, List.zip_nil_left]
        iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
        iframe Hdone
        iexact Hev
      ipureintro
      refine ⟨by word, by word, by simp [Hn.2.2.1], by simp [Hn.2.2.2.1], ?_⟩
      rw [List.range_succ, List.filterMap_append, ← Hn.2.2.2.2]
      simp only [Nat.add_zero] at Hkv
      simp only [List.filterMap_cons, List.filterMap_nil, Hkv, Option.map_some, List.append_nil]
  have hnl : sint.nat n = pend.length := by
    have h1 := Hn.2.1
    rw [← Hps, Hlen.1]; word
  have hevd : evd = mvcc.evsOfRevM ilog.length (mvcc.stateAfter ilog) pend := by
    rw [Hn.2.2.2.2, hnl]; rfl
  have hdl : done.length = evd.length := by rw [Hn.2.2.1, Hn.2.2.2.1]
  have hsub : sint.nat chs.len - sint.nat n = 0 := by word
  rw [hsub, List.replicate_zero, List.append_nil]
  have hN : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
    rw [← mvcc.W64_add_one]; congr 1; omega
  rw [hN]
  ihave #Hws0 : mvcc.isWatchableStore s st γ $$ []
  · iexact Hws
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ 1)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  icases persistent_entails_right (mvcc.body_pin s stw st γ σ ilog pend chs ps) $$
    [$HP $Hwlog $Hcore] with ⟨%Hpin, HP, Hwlog, Hcore⟩
  obtain ⟨hLmu, hbel⟩ := Hpin
  -- the seal: the revision's history lower bound, before the watchers get its events
  ihave Hcw : mvcc.isTxnWriteCore mw st γ.st ilog pend puts deletes putSize chs ps false $$
    [Hmw Hcore]
  · iunfold mvcc.isTxnWriteCore; iexists stw, ranges; iframe
  imod mvcc.isTxnWriteCore_seal _ _ _ _ _ _ _ _ _ _ hne $$ Hcw with ⟨Hcw, #Hlb⟩
  wp_apply (hNotify s st γ σ ilog pend esl (DFrac.own 1) done evd) $$
    [$Hws0 $HP $Hlb $Hesl $Hdone] as ⟨Hesl, %σ', HP, %Hσ'⟩
  · ipureintro
    exact ⟨⟨hLmu, hbel, by omega, Hwfc.2.2.2.2⟩, hdl, hevd⟩
  obtain ⟨hLmu', hab⟩ := Hσ'
  (try wp_auto)
  ihave Hte : mvcc.isTxnEnd mw st γ.st (.write ilog pend puts deletes putSize) $$ [Hcw]
  · simp only [mvcc.isTxnEnd]; iexists chs, ps, true; iexact Hcw
  wp_apply (hEnd mw st γ.st (.write ilog pend puts deletes putSize)) $$ [$Hte Hhook HPh]
    as ⟨Hrd, Hpost⟩
  · iapply mvcc.txnEndPre_write; iframe Hhook HPh
  have hcl : mvcc.commitLog ilog pend = ilog ++ [pend] := by
    unfold mvcc.commitLog; rw [if_neg hne]
  simp only [mvcc.txnEndPost, hcl]
  icases Hpost with ⟨#Hc, -⟩
  rw [← hLmu'] at *
  imod mvcc.body_commit s γ σ' (σ'.Lmu ++ [pend]) (by simpa using hab) $$ [$HP $Hwlog $Hc]
    with ⟨HP, Hwlog⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HP]
  · inext; iunfold mvcc.watchStoreInv; iexists _; iexact HP
  (try wp_auto)
  iapply HΦ
  iframe Hrd Hc
  iunfold mvcc.watchWriter
  iframe Hc Hwlog
  have hb : mvcc.wBudget (σ'.Lmu ++ [pend]) = mvcc.wBudget σ'.Lmu - 1 := by
    unfold mvcc.wBudget; simp only [List.length_append, List.length_singleton]; omega
  rw [hb]
  iexact Htoks

end proof

end EtcdGrove
end Perennial
