/-
Lemmas for `txn.go`'s `eval`, `commitToCache`, `revokeFallback`, `serverTxn` and `Commit`
(`InvLeasingKV.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheWrite
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__revokeFallback

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3 leasing

/-- `mapM` of `txnOpOf` as `map`. -/
theorem mapM_txnOpOf : ∀ (os : List OpFull) (ops : List TxnOp),
    os.mapM txnOpOf = some ops → os.map txnOpOf = ops.map some
  | [], ops, h => by simp at h; subst h; rfl
  | o :: os, ops, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h1 : txnOpOf o with
    | none => simp [h1] at h
    | some a =>
      cases h2 : os.mapM txnOpOf with
      | none => simp [h1, h2] at h
      | some l =>
        simp [h1, h2] at h
        subst h
        simp [h1, mapM_txnOpOf os l h2]

section pure
variable [ext : FfiSyntax]

/-- A state reached from `st0` by changing entries in place (keeping their `*leaseKey`s): well
formed, with `st0`'s installed list, readiness, map contents and map. -/
def CacheSame (st0 st : LeaseCacheSt) : Prop :=
  LeaseCacheWf st ∧ st.installed = st0.installed ∧ st.readyN = st0.readyN ∧ st.lis = st0.lis ∧
    st.emap = st0.emap

theorem cacheSame_refl (st0 : LeaseCacheSt) (h : LeaseCacheWf st0) : CacheSame st0 st0 :=
  ⟨h, rfl, rfl, rfl, rfl⟩

theorem cacheSame_modify (st0 st : LeaseCacheSt) (k : GoString) (f : LeaseEntry → LeaseEntry)
    (hli : ∀ e, (f e).li = e.li) (h : CacheSame st0 st) : CacheSame st0 (st.modify k f) := by
  obtain ⟨hwf, hi, hr, hl, he⟩ := h
  have ho := modify_other k f st
  refine ⟨modify_wf k f st hli hwf, ?_, ?_, ?_, ?_⟩
  · rw [ho.2.2.2.2.2.2, hi]
  · unfold LeaseCacheSt.readyN; rw [ho.1]; exact hr
  · rw [modify_lis k f st hli, hl]
  · rw [ho.1, he]

theorem del_fields (e : LeaseEntry) (h : Loc) (hm : HdrM) :
    (e.del h hm).li = e.li ∧ (e.del h hm).rev = e.rev ∧ (e.del h hm).lease = e.lease ∧
      (e.del h hm).acq = e.acq := by
  unfold LeaseEntry.del; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A nested transaction of a transaction's operations runs as the transaction. -/
theorem applyTxnOp_txn (r : w64) (s : List EtcdKv) (m : TxnModel) :
    applyTxnOp r s (.txn m.cmps m.thenOps m.elseOps) =
      ((runTxn r s m).2.1, .txn (runTxn r s m).1 (runTxn r s m).2.2) := by
  unfold runTxn TxnModel.branch
  simp only [applyTxnOp]
  split <;> rename_i h <;> simp [h]

/-- `txnOpOf` never gives a nested transaction. -/
theorem txnOpOf_not_txn {o : OpFull} {op : TxnOp} (h : txnOpOf o = some op) :
    ∀ cs ts es, op ≠ .txn cs ts es := by
  intro cs ts es heq
  subst heq
  unfold txnOpOf at h
  repeat (first | (split at h) | (simp at h))

theorem mapM_txnOpOf_not_txn : ∀ (os : List OpFull) (ops : List TxnOp),
    os.mapM txnOpOf = some ops → ∀ op ∈ ops, ∀ cs ts es, op ≠ .txn cs ts es
  | [], ops, h => by simp at h; subst h; simp
  | o :: os, ops, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases h1 : txnOpOf o with
    | none => simp [h1] at h
    | some a =>
      cases h2 : os.mapM txnOpOf with
      | none => simp [h1, h2] at h
      | some l =>
        simp [h1, h2] at h
        subst h
        intro op hop
        simp only [List.mem_cons] at hop
        rcases hop with rfl | hop
        · exact txnOpOf_not_txn h1
        · exact mapM_txnOpOf_not_txn os l h2 op hop

/-- The outer transaction of `serverTxn`, when its comparisons held: the user's transaction ran. -/
theorem runTxn_outer (r : w64) (s : List EtcdKv) (m : TxnModel) (ms : List CmpModel)
    (fb : List TxnOp)
    (h : (runTxn r s { cmps := ms, thenOps := [.txn m.cmps m.thenOps m.elseOps], elseOps := fb }).1 = true) :
    (runTxn r s { cmps := ms, thenOps := [.txn m.cmps m.thenOps m.elseOps], elseOps := fb }).2.1 =
        (runTxn r s m).2.1 ∧
    (runTxn r s { cmps := ms, thenOps := [.txn m.cmps m.thenOps m.elseOps], elseOps := fb }).2.2 =
        [.txn (runTxn r s m).1 (runTxn r s m).2.2] ∧
    txnWrote (runTxn r s { cmps := ms, thenOps := [.txn m.cmps m.thenOps m.elseOps], elseOps := fb }).2.2 =
        txnWrote (runTxn r s m).2.2 := by
  have h' : ms.all (cmpHolds s) = true := h
  have e : (runTxn r s { cmps := ms, thenOps := [.txn m.cmps m.thenOps m.elseOps], elseOps := fb }) =
      (true, (runTxn r s m).2.1, [.txn (runTxn r s m).1 (runTxn r s m).2.2]) := by
    unfold runTxn
    simp only [h', TxnModel.branch, ↓reduceIte, runOps]
    have := applyTxnOp_txn r s m
    simp only [runTxn, TxnModel.branch] at this
    rw [this]
  rw [e]
  refine ⟨rfl, rfl, ?_⟩
  simp [txnWrote, TxnOpResult.wrote, TxnOpResult.wroteL_eq]


end pure

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- A transaction being built has operations a transaction can run. -/
theorem ownTxnLeasing_ops (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) :
    ownTxnLeasing txn lkv γ pfx ctx cs b ⊢
      ⌜∃ tops eops, b.thenOps = some tops ∧ b.elseOps = some eops⌝ := by
  unfold ownTxnLeasing
  iintro ⟨%t, %B, %csl, %tsl, %esl, %tops, %eops, -, -, -, -, -, -, -, -, -, -, -, -, -, %h⟩
  ipureintro; exact ⟨tops, eops, h⟩

/-- **Reading a transaction being built**: its fields (owned), what they hold (read-only, the
slices' elements and the KV), and the way back. -/
theorem ownTxnLeasing_acc (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) :
    ownTxnLeasing txn lkv γ pfx ctx cs b ⊢ ∃ (csl tsl esl : GoSlice) (tops eops : List TxnOp),
      structFieldRef txnLeasing go!"lkv" txn ↦ lkv ∗
      structFieldRef txnLeasing go!"ctx" txn ↦ GoInterface.ok ctx ∗
      structFieldRef txnLeasing go!"cs" txn ↦ csl ∗
      structFieldRef txnLeasing go!"opst" txn ↦ tsl ∗
      structFieldRef txnLeasing go!"opse" txn ↦ esl ∗
      □ (isLeasingKV lkv γ pfx ∗ context.isContext ctx cs ∗ cmpsSetAt csl b.cmps ∗
        opsAt tsl b.thenOs ∗ opsAt esl b.elseOs) ∗
      ⌜b.thenOps = some tops ∧ b.elseOps = some eops⌝ ∗
      (structFieldRef txnLeasing go!"lkv" txn ↦ lkv -∗
        structFieldRef txnLeasing go!"ctx" txn ↦ GoInterface.ok ctx -∗
        structFieldRef txnLeasing go!"cs" txn ↦ csl -∗
        structFieldRef txnLeasing go!"opst" txn ↦ tsl -∗
        structFieldRef txnLeasing go!"opse" txn ↦ esl -∗ ownTxnLeasing txn lkv γ pfx ctx cs b) := by
  unfold ownTxnLeasing
  iintro ⟨%t, %B, %csl, %tsl, %esl, %tops, %eops, Ht, HB, #HBs, Hl, #Hlkv, Hc, #Hctx, Hcs, Hcso,
    Hts, Htso, Hes, Heso, %Hops⟩
  iexists csl, tsl, esl, tops, eops
  iframe Hl Hc Hcs Hts Hes
  unfold cmpsOwn opsOwn
  icases Hcso with ⟨%cvs, #Hcv, Hccap, %Hcl, #Hcall⟩
  icases Htso with ⟨%tvs, #Htv, Htcap, %Htl, #Htall⟩
  icases Heso with ⟨%evs, #Hev, Hecap, %Hel, #Heall⟩
  isplitr
  · imodintro
    iframe #
    unfold cmpsSetAt opsAt
    isplitr
    · iexists cvs; iframe #; ipureintro; exact Hcl
    isplitr
    · iexists tvs; iframe #; ipureintro; exact Htl
    · iexists evs; iframe #; ipureintro; exact Hel
  isplitr
  · ipureintro; exact Hops
  iintro Hl Hc Hcs Hts Hes
  iexists t, B, csl, tsl, esl, tops, eops
  iframe
  iframe #
  ipureintro; exact ⟨Hcl, Htl, Hel, Hops⟩

/-- Plain operations' trees do not depend on the capacity flag. -/
theorem opListAtC_leaves_true : ∀ (vs : List go_etcd_io.etcd.client.v3.Op) (os : List OpFull),
    opListAtC (GF := GF) false vs (os.map OpT.leaf) ⊢ opListAtC true vs (os.map OpT.leaf)
  | [], [] => by simp only [List.map_nil, opListAtC]; iintro -; itrivial
  | v :: vs, o :: os => by
    simp only [List.map_cons, opListAtC, opTAtC]
    iintro ⟨H1, H2⟩
    iframe H1
    iapply opListAtC_leaves_true vs os $$ H2
  | [], _ :: _ => by simp only [List.map_cons, opListAtC]; iintro H; iexact H
  | _ :: _, [] => by simp only [List.map_nil, opListAtC]; iintro H; iexact H

/-- Plain operations as the trees `gatherOps` takes. -/
theorem opsAt_gather (sl : GoSlice) (os : List OpFull) (ops : List TxnOp)
    (h : os.mapM txnOpOf = some ops) :
    opsAt (GF := GF) sl os ⊢ ∃ vs, sl ↦*□ vs ∗ opListAtC true vs (os.map OpT.leaf) := by
  iintro H
  ihave H := opsAt_leaves sl os ops (mapM_txnOpOf os ops h) $$ H
  unfold opsTAt
  icases H with ⟨%vs, #Hs, #Hl⟩
  iexists vs
  iframe Hs
  iapply opListAtC_leaves_true $$ Hl

/-- Two slices' worth of operations, concatenated. -/
theorem opsAt_app (sl : GoSlice) (vs1 vs2 : List go_etcd_io.etcd.client.v3.Op)
    (os1 os2 : List OpFull) (h1 : vs1.length = os1.length) (h2 : vs2.length = os2.length) :
    sl ↦*□ (vs1 ++ vs2) ∗
      (□ ∀ (i : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs1[i]? = some v⌝ -∗
        ⌜os1[i]? = some o⌝ -∗ opFullAt v o) ∗
      (□ ∀ (i : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs2[i]? = some v⌝ -∗
        ⌜os2[i]? = some o⌝ -∗ opFullAt v o) ⊢ opsAt (GF := GF) sl (os1 ++ os2) := by
  iintro ⟨#Hs, #H1, #H2⟩
  unfold opsAt
  iexists vs1 ++ vs2
  iframe Hs
  isplitr
  · ipureintro; simp [h1, h2]
  imodintro
  iintro %i %v %o %Hv %Ho
  by_cases hi : i < vs1.length
  · rw [List.getElem?_append_left hi] at Hv
    rw [List.getElem?_append_left (by omega)] at Ho
    iapply H1 $$ %i %v %o %Hv %Ho
  · rw [List.getElem?_append_right (by omega)] at Hv
    rw [List.getElem?_append_right (by omega)] at Ho
    rw [h1] at Hv
    iapply H2 $$ %(i - os1.length) %v %o %Hv %Ho

/-- The leasing KV's cache. -/
theorem isLeasingKV_cache (lkv : Loc) (γ : LeasingNames) (pfx : GoString) :
    isLeasingKV (GF := GF) lkv γ pfx ⊢ lkvCache lkv γ pfx := by
  unfold isLeasingKV
  iintro ⟨%cl, %kv, %ctx, %cs, %cancel, %osl, -, -, -, -, -, -, -, -, -, -, -, -, -, Hc, -⟩
  iexact Hc

/-- The leasing KV's client `KV`, with its transactions, and its prefix. -/
theorem isLeasingKV_kv (lkv : Loc) (γ : LeasingNames) (pfx : GoString) :
    isLeasingKV (GF := GF) lkv γ pfx ⊢ ∃ kv : GoInterfaceOk,
      structFieldRef leasingKV go!"kv" lkv ↦□ GoInterface.ok kv ∗ isEtcdTxnKVO kv [] ∗
      structFieldRef leasingKV go!"pfx" lkv ↦□ pfx ∗ ⌜pfx ≠ []⌝ := by
  unfold isLeasingKV
  iintro ⟨%cl, %kv, %ctx, %cs, %cancel, %osl, %Hp, -, #Hkv, #Hpfx, -, -, -, -, -, #Htxn, -⟩
  iexists kv
  iframe #
  ipureintro; exact Hp

/-- A plain operation's response, nested or not, is `txnOpRespAt`'s. -/
theorem txnOpRespN_flat1 (p : Loc) (op : TxnOp) (res : TxnOpResult)
    (h : ∀ cs ts es, op ≠ .txn cs ts es) :
    txnOpRespN (GF := GF) p op res ⊢ txnOpRespAt p op res := by
  cases op with
  | txn cs ts es => exact absurd rfl (h cs ts es)
  | _ => unfold txnOpRespN; exact .rfl

/-- The responses of plain operations, in `txnRespAt`'s form. -/
theorem txnOpsRespN_flat : ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult),
    (∀ op ∈ ops, ∀ cs ts es, op ≠ .txn cs ts es) →
    txnOpsRespN (GF := GF) ps ops rs ⊢ ⌜ps.length = ops.length ∧ rs.length = ops.length⌝ ∗
      □ ∀ (i : Nat) (p : Loc) (op : TxnOp) (res : TxnOpResult), ⌜ps[i]? = some p⌝ -∗
        ⌜ops[i]? = some op⌝ -∗ ⌜rs[i]? = some res⌝ -∗ txnOpRespAt p op res
  | [], [], [], _ => by
    iintro -
    isplitr
    · ipureintro; simp
    imodintro
    iintro %i %p %op %res %hp
    simp at hp
  | p :: ps, op :: ops, r :: rs, h => by
    simp only [txnOpsRespN]
    iintro ⟨#H1, #H2⟩
    ihave ⟨%hl, #Hall⟩ := txnOpsRespN_flat ps ops rs (fun op' hop => h op' (List.mem_cons_of_mem _ hop)) $$ H2
    ihave #H1' := txnOpRespN_flat1 p op r (h op List.mem_cons_self) $$ H1
    isplitr
    · ipureintro; simp [hl.1, hl.2]
    imodintro
    iintro %i %p' %op' %res' %hp %ho %hr
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp ho hr
      subst hp ho hr
      iexact H1'
    · simp only [List.getElem?_cons_succ] at hp ho hr
      iapply Hall $$ %i %p' %op' %res' %hp %ho %hr
  | [], [], _ :: _, _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H
  | [], _ :: _, _, _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H
  | _ :: _, [], _, _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H
  | _ :: _, _ :: _, [], _ => by simp only [txnOpsRespN]; iintro H; iexfalso; iexact H

/-- An owned key-value, read-only. -/
theorem cachedKvOwn_kvValAt_c (c : CachedKv) :
    cachedKvOwn (GF := GF) c (DFrac.own 1) ⊢ |==> kvValAt c.p c.kv := by
  haveI := (cachedKvOwn_dfractional (GF := GF) c).dfractional_persistent
  iintro H
  imod (cachedKvOwn_dfractional c).dfractional_persist (DFrac.own 1) $$ H with #H
  imodintro
  unfold cachedKvOwn kvValAt
  icases H with ⟨-, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8⟩
  iexists c.keySl, c.valSl
  iframe #

theorem cachedKvOwns_kvPtrsAt : ∀ (cs : List CachedKv),
    ([∗list] c ∈ cs, cachedKvOwn (GF := GF) c (DFrac.own 1)) ⊢
      |==> kvPtrsAt (cs.map CachedKv.p) (cs.map CachedKv.kv)
  | [] => by
    iintro -
    imodintro
    unfold kvPtrsAt
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %p %v %hp
    simp at hp
  | c :: cs => by
    iintro ⟨H1, H2⟩
    imod cachedKvOwn_kvValAt_c c $$ H1 with #H1
    imod cachedKvOwns_kvPtrsAt cs $$ H2 with H2
    unfold kvPtrsAt
    icases H2 with ⟨%hl, #Hall⟩
    imodintro
    isplitr
    · ipureintro; simp [hl]
    imodintro
    iintro %i %p %v %hp %hv
    rcases i with _ | i
    · simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hp hv
      subst hp hv
      iexact H1
    · simp only [List.map_cons, List.getElem?_cons_succ] at hp hv
      iapply Hall $$ %i %p %v %hp %hv

/-- The owned responses of the fallback gets, read-only (`revokeFallback`'s premise). -/
theorem fallbackResps_ro : ∀ (ps : List Loc) (fos : List OpFull) (rs : List TxnOpResult),
    txnOpsRespOwn (GF := GF) ps (fos.map TxnOp.get) rs ⊢
      |==> ∃ kvss : List (List EtcdKv), ⌜ps.length = kvss.length⌝ ∗
        [∗list] i ↦ p ∈ ps, ∃ kvs, ⌜kvss[i]? = some kvs⌝ ∗ rangeKvsRO p kvs
  | [], [], [] => by
    iintro -
    imodintro
    iexists []
    isplitr
    · ipureintro; rfl
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | p :: ps, o :: fos, r :: rs => by
    simp only [List.map_cons, txnOpsRespOwn]
    iintro ⟨H1, H2⟩
    imod fallbackResps_ro ps fos rs $$ H2 with ⟨%kvss, %hl, H2⟩
    cases r with
    | range sel n =>
      simp only [txnOpRespOwn]
      icases H1 with ⟨%hp, %w, %rr, #Hu, #Hw, %hrr, H1⟩
      unfold rangeRespOwn rangeBodyOwn
      icases H1 with ⟨%h, -, %sl, %cs, %more, Hk, Hsl, -, Hcs, -, -, -⟩
      ipersist Hk
      imod ownSlice_persist $$ Hsl with #Hsl
      imod cachedKvOwns_kvPtrsAt cs $$ Hcs with #Hcs
      imodintro
      iexists (cs.map CachedKv.kv) :: kvss
      isplitr
      · ipureintro; simp [hl]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iexists cs.map CachedKv.kv
        isplitr
        · ipureintro; rfl
        unfold rangeKvsRO
        iexists w, rr, sl, cs.map CachedKv.p
        iframe #
        ipureintro; exact ⟨hp, hrr⟩
      iapply BigSepL.bigSepL_mono ?_ $$ H2
      intro i p' _
      iintro ⟨%kvs, %hk, H⟩
      iexists kvs
      iframe
      ipureintro; simpa using hk
    | _ => simp only [txnOpRespOwn]; iexfalso; iexact H1
  | [], [], _ :: _ => by simp only [List.map_nil, txnOpsRespOwn]; iintro H; iexfalso; iexact H
  | [], _ :: _, _ => by simp only [List.map_cons, txnOpsRespOwn]; iintro H; iexfalso; iexact H
  | _ :: _, [], _ => by simp only [List.map_nil, txnOpsRespOwn]; iintro H; iexfalso; iexact H
  | _ :: _, _ :: _, [] => by simp only [List.map_cons, txnOpsRespOwn]; iintro H; iexfalso; iexact H

/-- Comparisons with their operands set are comparisons. -/
theorem cmpsSetAt_cmpsAt_c (sl : GoSlice) (ms : List CmpModel) :
    cmpsSetAt (GF := GF) sl ms ⊢ cmpsAt sl ms := by
  unfold cmpsSetAt cmpsAt
  iintro ⟨%cs, #Hs, %Hl, #Hall⟩
  iexists cs
  iframe #
  isplitr
  · ipureintro; exact Hl
  imodintro
  iintro %i %c %m %hc %hm
  ihave #H := Hall $$ %i %c %m %hc %hm
  unfold cmpSetAt cmpAt compareAt
  icases H with ⟨%hnn, %ksl, %esl, %u, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, -⟩
  isplitr
  · ipureintro; exact hnn
  iexists ksl, esl, u
  iframe #

/-- The user's transaction `OpTxn(cs, opst, opse)` as an operation tree. -/
theorem userTxn_tree (uv : go_etcd_io.etcd.client.v3.Op) (ms : List CmpModel) (tsl esl : GoSlice)
    (tos eos : List OpFull) (tops eops : List TxnOp)
    (ht : tos.mapM txnOpOf = some tops) (he : eos.mapM txnOpOf = some eops)
    (hs : uv.thenOps' = tsl ∧ uv.elseOps' = esl) :
    opFullAt (GF := GF) uv OpFull.txnInit ∗ cmpsAt uv.cmps' ms ∗ opsAt tsl tos ∗ opsAt esl eos ⊢
      opTAtC false uv (.txn OpFull.txnInit ms (tos.map OpT.leaf) (eos.map OpT.leaf)) := by
  iintro ⟨#H1, #H2, #H3, #H4⟩
  ihave #H3' := opsAt_leaves tsl tos tops (mapM_txnOpOf tos tops ht) $$ H3
  ihave #H4' := opsAt_leaves esl eos eops (mapM_txnOpOf eos eops he) $$ H4
  unfold opsTAt
  icases H3' with ⟨%tvs, #Htv, #Htl⟩
  icases H4' with ⟨%evs, #Hev, #Hel⟩
  obtain ⟨h1, h2⟩ := hs
  unfold opTAtC
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe #
  rw [h1, h2]
  iframe #
  ipureintro; rfl

theorem userTxn_txnOps (ms : List CmpModel) (tos eos : List OpFull) (tops eops : List TxnOp)
    (ht : tos.mapM txnOpOf = some tops) (he : eos.mapM txnOpOf = some eops) :
    OpT.txnOps [.txn OpFull.txnInit ms (tos.map OpT.leaf) (eos.map OpT.leaf)] =
      some [.txn ms tops eops] := by
  simp [OpT.txnOps, OpT.txnOp, txnOps_leaves tos tops (mapM_txnOpOf tos tops ht),
    txnOps_leaves eos eops (mapM_txnOpOf eos eops he)]

end lemmas

end EtcdGrove
end Perennial
