/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StartSubTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StopSubTrace
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange
public import Spec.google_golang_org.protobuf.proto.Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.getPrevKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.opSkel_put_et (s0 : List EtcdKv) (p : Loc) (o : OpFull) :
    txn.opSkel (GF := GF) s0 p (txn.putTxnOp o) = txn.putSkel p := by
  unfold txn.putTxnOp; split <;> (try split) <;> simp only [txn.opSkel]

theorem txn.opPath_put_et (s0 : List EtcdKv) (o : OpFull) : txn.opPath s0 (txn.putTxnOp o) = [] := by
  unfold txn.putTxnOp; split <;> (try split) <;> simp only [txn.opPath]

theorem txn.opIsGet_put_et (o : OpFull) : txn.opIsGet (txn.putTxnOp o) = false := by
  unfold txn.putTxnOp; split <;> (try split) <;> simp only [txn.opIsGet]

/-- A put of the run finds the previous key-value it needs. -/
theorem txn.opOk_put_et (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (o : OpFull)
    (h : txn.OpOk false s0 r s (txn.putTxnOp o)) :
    txn.needsPrev o = true → (mvcc.findKey o.key s).isSome := by
  intro hn
  unfold txn.putTxnOp at h
  unfold txn.needsPrev at hn
  cases hv : o.ignoreValue <;> cases hl : o.ignoreLease <;>
    simp only [hv, hl, Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_self] at h hn <;>
    simp only [txn.OpOk, txn.IgnOk, Bool.false_eq_true, false_and, or_false] at h <;> exact h

theorem txn.responseOpIs_put_et (skip : Bool) (p w r : Loc) (o : OpFull) :
    ⊢ ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ r -∗
      (∃ (rev : w64) (prev : Option EtcdKv), txn.putResponseIs (GF := GF) r rev prev) -∗
      txn.responseOpIs skip p (txn.putTxnOp o) .put := by
  iintro %Hp #Hu #Hw #⟨%rev, %prev, #Hr⟩
  unfold txn.putTxnOp
  split <;> (try split) <;>
  · unfold txn.responseOpIs
    imodintro
    isplitl []; · ipureintro; exact Hp
    iexists _, w, r
    iframe Hu
    isplitl []; · ipureintro; rfl
    iframe Hw
    iexists rev, prev
    iexact Hr

/-- A suffix of a persistent slice. -/
theorem txn.slice_from_et (pl : GoSlice) (L : List Bool) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z pl.len) :
    pl ↦*□ L ⊢ (slice.slice pl Bool k pl.len ↦*□ L.drop (sint.nat k) : IProp GF) := by
  iintro #H
  ihave %Hl := ownSlice_len _ _ _ $$ H
  icases (ownSlice_slice k pl.len pl DFrac.discard L ⟨hk.1, hk.2, Int.le_refl _⟩).1 $$ H with ⟨-, Hm, -⟩
  have h : subslice (sint.nat k) (sint.nat pl.len) L = L.drop (sint.nat k) := by
    unfold subslice; rw [← Hl.1, List.take_length]
  rw [h]
  iexact Hm

theorem txn.drop_last_et (R : List Bool) :
    ∀ (a : Bool) (P : List Bool), ∃ y, (a :: (P ++ R)).drop P.length = y :: R
  | a, [] => ⟨a, rfl⟩
  | a, b :: P => by
    obtain ⟨y, hy⟩ := txn.drop_last_et R b P
    exact ⟨y, by simpa using hy⟩

theorem txn.opsSkel_match_et (s0 : List EtcdKv) (ps : List Loc) (ts es : List TxnOp) (b : Bool) :
    (match b with
      | true => txn.opsSkel (GF := GF) s0 ps ts
      | false => txn.opsSkel s0 ps es) ⊢ txn.opsSkel s0 ps (if b then ts else es) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iintro H <;> iexact H

theorem txn.opOk_txn_et (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (cs : List CmpModel)
    (ts es : List TxnOp) (h : txn.OpOk false s0 r s (.txn cs ts es)) :
    txn.OpsOk false s0 r s (if cs.all (cmpHolds s0) then ts else es) := by
  simp only [txn.OpOk] at h
  cases hb : cs.all (cmpHolds s0) <;> rw [hb] at h <;> simpa using h

theorem txn.opLeases_txn_et (s0 : List EtcdKv) (cs : List CmpModel) (ts es : List TxnOp) :
    txn.opLeases s0 (.txn cs ts es) = txn.opsLeases s0 (if cs.all (cmpHolds s0) then ts else es) := by
  simp only [txn.opLeases]
  cases cs.all (cmpHolds s0) <;> rfl

theorem txn.respsSkel_et (s0 : List EtcdKv) (r : Loc) (cs : List CmpModel) (ts es : List TxnOp)
    (sl : GoSlice) (ps : List Loc) :
    structFieldRef etcdserverpb.TxnResponse go!"Responses" r ↦□ sl ∗ sl ↦*□ ps ∗
      (match cs.all (cmpHolds s0) with
        | true => txn.opsSkel (GF := GF) s0 ps ts
        | false => txn.opsSkel s0 ps es) ⊢
    txn.respsSkel s0 r (({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel).branch
      (txn.txnOk s0 { cmps := cs, thenOps := ts, elseOps := es })) := by
  iintro ⟨#Hr, #Hs, H⟩
  unfold txn.respsSkel TxnModel.branch txn.txnOk
  iexists sl, ps
  iframe Hr Hs
  iapply txn.opsSkel_match_et $$ H

/-- A nested transaction's response from its skeleton's fields and its responses. -/
theorem txn.responseOpIs_txn_et (skip : Bool) (s0 : List EtcdKv) (p w r h : Loc) (cs : List CmpModel)
    (ts es : List TxnOp) (rs : List TxnOpResult) :
    ⊢ ⌜p ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ r -∗ ⌜r ≠ null⌝ -∗
      structFieldRef etcdserverpb.TxnResponse go!"Header" r ↦□ h -∗ ⌜h ≠ null⌝ -∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ (W64 0 : w64) -∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" r ↦□ (cs.all (cmpHolds s0)) -∗
      txn.respsIs skip r (if cs.all (cmpHolds s0) then ts else es) rs -∗
      txn.responseOpIs (GF := GF) skip p (.txn cs ts es) (.txn (cs.all (cmpHolds s0)) rs) := by
  iintro %Hp #Hu #Hw %Hr #Hh %Hhn #Hrev #Hs #Hresps
  iunfold txn.respsIs at Hresps
  icases Hresps with ⟨%sl, %ps, #Hrs, #Hps, #Hops⟩
  unfold txn.responseOpIs
  imodintro
  isplitl []; · ipureintro; exact Hp
  iexists w, r
  iframe Hu Hw
  isplitl []; · ipureintro; exact Hr
  iexists h, sl, ps
  iframe Hh Hrev Hs Hrs Hps
  isplitl []; · ipureintro; exact Hhn
  cases cs.all (cmpHolds s0) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iexact Hops

instance txn.ite_persistent_et (b : Bool) (P Q : IProp GF) [Persistent P] [Persistent Q] :
    Persistent (if b then P else Q) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

theorem txn.executeTxn.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hStart : traceutil.Trace.StartSubTrace.spec (GF := GF) (hG := hG))
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hRoRev : mvcc.txnReadWrite.Rev.spec (GF := GF) (hG := hG))
    (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hRoCh : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG))
    (hExec : txn.executeRange.spec (GF := GF) (hG := hG))
    (hStop : traceutil.Trace.StopSubTrace.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG))
    (hPrev : txn.getPrevKV.spec (GF := GF) (hG := hG))
    (hPut : txn.put.spec (GF := GF) (hG := hG))
    (hDel : txn.deleteRange.spec (GF := GF) (hG := hG)) :
    txn.executeTxn.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg s γ tw ro ilog pend rt t pl rest tresp skip
  iloeb as IH generalizing %pend %rt %t %pl %rest %tresp
  wp_start as ⟨Htw, #Hctx, #Hnd, #Hrt, #Hpl, Hskel, #Hleases, #Hknown, %Hpre⟩
  ihave %Htwok := txn.txnWriteIs_ok tw s γ ro ilog pend $$ Htw
  obtain ⟨twi, rfl⟩ := Htwok
  iunfold txn.txnRequestIs at Hrt
  icases Hrt with ⟨%Hrtn, #Hrt⟩
  iunfold txn.txnFieldsIs at Hrt
  icases Hrt with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hf, #Hfs, #Hfm⟩
  iunfold txn.respsSkel at Hskel
  icases Hskel with ⟨%rsl, %rps, #Hrsp, #Hrsl, Hskel⟩
  ihave %Hplen := ownSlice_len _ _ _ $$ Hpl
  wp_auto
  wp_apply (hGet ctx cd) $$ [$Hctx] as %trace %Htrace
  -- the branch the path's first verdict chooses
  generalize hs0 : mvcc.stateAfter ilog = s0 at *
  generalize hok : txnOk s0 t = ok at *
  generalize hops : t.branch ok = ops at *
  have hp0 : (txnPath s0 t ++ rest)[(0 : Nat)]? = some ok := by
    simp [txnPath, hok]
  have hplpos : 0 < sint.Z pl.len := by
    have h1 := Hplen.1; simp [txnPath] at h1; word
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z pl.len := ⟨by decide, by word⟩
  simp only [Hb0, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ DFrac.discard ok (by decide) $$ [Hpl] as -
  · iframe Hpl; ipureintro; exact hp0
  wp_join iprop(∃ (bsl : GoSlice) (bps : List Loc), reqs_ptr ↦ bsl ∗ rt_ptr ↦ rt ∗
      bsl ↦*□ bps ∗ requestOpsIs bps ops) at (if: _ then _ else _) with [reqs rt]
      as ⟨%bsl, %bps, reqs, rt, #Hbs, #Hbm⟩
  · cases ok
    · wp_auto
      isplitl []; · ipureintro; rfl
      iexists fsl, fps
      iframe reqs rt Hfs
      rw [← hops]; simp only [TxnModel.branch, Bool.false_eq_true, ↓reduceIte]; iexact Hfm
    · wp_auto
      isplitl []; · ipureintro; rfl
      iexists ssl, sps
      iframe reqs rt Hss
      rw [← hops]; simp only [TxnModel.branch, ↓reduceIte]; iexact Hsm
  -- the loop over the branch's operations
  generalize hr : (W64 (ilog.length : Int) : w64) = r at *
  generalize hst : pendState ilog pend = st at *
  have hpath : txnPath s0 t = ok :: opsPath s0 ops := by
    unfold txnPath; rw [hok, hops]
  rw [hpath] at Hplen
  ihave %Hbl := requestOpsIs_length bps ops $$ Hbm
  ihave %Hrl := opsSkel_length s0 rps ops $$ Hskel
  ihave %Hbsl := ownSlice_len _ _ _ $$ Hbs
  rename_i iv_ptr
  irename : (iv_ptr ↦ zero_val w64 : IProp GF) => iv
  ihave HI : iprop(∃ (n iv : w64) (rv : Loc) (plv : GoSlice) (x : Bool) (e : GoInterface),
      "i" ∷ i_ptr ↦ n ∗ "iv" ∷ iv_ptr ↦ iv ∗ "req" ∷ req_ptr ↦ rv ∗
      "txns" ∷ txns_ptr ↦ (W64 ((opsPath s0 (ops.take (sint.nat n))).length : Int) : w64) ∗
      "txnPath" ∷ txnPath_ptr ↦ plv ∗
      "#Hplv" ∷ plv ↦*□ (x :: (opsPath s0 (ops.drop (sint.nat n)) ++ rest)) ∗
      "err" ∷ err_ptr ↦ e ∗
      "Htw" ∷ txnWriteIs (GoInterface.ok twi) s γ ro ilog
        (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1) ∗
      "Hskel" ∷ opsSkel s0 (rps.drop (sint.nat n)) (ops.drop (sint.nat n)) ∗
      "#Hdone" ∷ responseOpsIs skip (rps.take (sint.nat n)) (ops.take (sint.nat n))
        (srvOps s0 r st (ops.take (sint.nat n))).2 ∗
      "#Hknown" ∷ leasesKnown γ.leases
        (mvcc.applyChanges r st (srvOps s0 r st (ops.take (sint.nat n))).1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ops.length⌝) $$ [i iv req txns txnPath err Htw Hskel]
  · iexists W64 0, _, _, pl, ok, GoInterface.nil
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, srvOps_nil,
      List.append_nil]
    iframe
    isplitl []
    · have hpl : txnPath s0 t ++ rest = ok :: (opsPath s0 ops ++ rest) := by rw [hpath]; rfl
      rw [← hpl]; iexact Hpl
    isplitl []
    · iapply responseOpsIs_nil
    isplitl []
    · rw [applyChanges_nil']; rw [← hst]; iexact Hknown
    ipureintro; exact ⟨by decide, by omega⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z bsl.len := by simpa using Hif
    have hnl : sint.nat n < ops.length := by
      have h1 := Hbsl.1; have h2 := Hbl; have h3 := Hn.1; word
    list_elem ops (sint.nat n) as op
    list_elem bps (sint.nat n) as rq
    list_elem rps (sint.nat n) as p
    have Hbn : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z bsl.len := ⟨Hn.1, hlt⟩
    simp only [Hbn, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index bsl (sint.Z n) bps DFrac.discard rq Hn.1 $$ [Hbs] as -
    · iframe Hbs; ipureintro; exact Hrq_lookup
    icases (opsSkel_drop s0 rps ops (sint.nat n) p op Hp_lookup Hop_lookup).1 $$ Hskel with ⟨Hp, Hskel⟩
    ihave #Hrq := requestOpsIs_lookup bps ops (sint.nat n) rq op Hrq_lookup Hop_lookup $$ Hbm
    -- the facts of the step
    have hdropo := opsPath_drop s0 ops (sint.nat n) op Hop_lookup
    have htake := srvOps_take_succ s0 r st ops (sint.nat n) op Hop_lookup
    have hokn := (opsOk_drop false s0 r _ ops (sint.nat n) op Hop_lookup).1
      (opsOk_drop' false s0 r st ops (sint.nat n) Hpre.1)
    have hmem : op ∈ ops := List.mem_of_getElem? Hop_lookup
    have hbnd : pend.length + (srvOps s0 r st (ops.take (sint.nat n))).1.length +
        (srvOp s0 r (mvcc.applyChanges r st (srvOps s0 r st (ops.take (sint.nat n))).1) op).1.length
          < 2 ^ 63 := by
      have h := Hpre.2.1
      rw [srvOps_take_drop s0 r st ops (sint.nat n + 1), htake] at h
      simp only [List.length_append] at h; omega
    have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have hrl : sint.nat n < rps.length := by omega
    ihave %Hrsll := ownSlice_len _ _ _ $$ Hrsl
    have Hbr : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rsl.len :=
      ⟨Hn.1, by have h1 := Hrsll.1; have h2 := Hrl; have h3 := Hn.1; word⟩
    generalize hstn : mvcc.applyChanges r st (srvOps s0 r st (ops.take (sint.nat n))).1 = stn at *
    simp only [Hbr, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index rsl (sint.Z n) rps DFrac.discard p Hn.1 $$ [Hrsl] as -
    · iframe Hrsl; ipureintro; exact Hp_lookup
    cases op with
    | get o =>
      iunfold txn.opSkel at Hp
      icases Hp with ⟨%Hpn, %w, #Hpw, Hw⟩
      icases requestOpIs_get rq o $$ Hrq with ⟨%Hrqn, %w', %rr, #Hrqw, #Hw'rr, #Hrr⟩
      ihave #Hrr2 := Hrr
      iunfold txn.rangeRequestIs at Hrr2
      icases Hrr2 with ⟨%Hrrn, %ksl, %esl, %k, %e0, %rev0, %limit, %order, %target, %ser, %ko, %co,
        %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, -, #Hrev, -, -, -, -, -, -, -, -, -, %Ho⟩
      wp_auto
      wp_apply wp_bytes_to_string ksl k DFrac.discard $$ [$Hks] as -
      wp_apply wp_bytes_to_string esl e0 DFrac.discard $$ [$Hes] as -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl' ⟨-, -⟩
      wp_auto
      wp_apply (hStart trace _) $$ []
      · ipureintro; exact Htrace
      wp_join iprop(∃ (rr0 : Loc) (e1 : GoInterface), resp_ptr ↦ rr0 ∗ err_ptr ↦ e1 ∗
          txnWrite_ptr ↦ GoInterface.ok twi ∗ ctx_ptr ↦ GoInterface.ok ctx ∗ lg_ptr ↦ lg ∗
          tv_ptr ↦ w' ∗
          txnWriteIs (GoInterface.ok twi) s γ ro ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1) ∗
          ∃ rev : w64, if skip then rangeResponseIs rr0 rev [] false (W64 0)
            else ∃ (kvs : List EtcdKv) (more : Bool),
              rangeResponseIs rr0 rev kvs more (W64 ((rangeIn stn o).length : Int)) ∗
              ⌜∃ kvs', rangeKvsOk o (rangeSel stn o) kvs' ∧ kvs = kvs'.map (leaseZ (fastKeysOnly o))⌝)
        with [resp err txnWrite ctx lg tv Htw] as ⟨%rr0, %e1, resp, err, txnWrite, ctx, lg, tv, Htw, %rev1, Hrr0⟩
      · -- the range, at the transaction's state
        icases txnWriteIs_kind _ s γ ro ilog _ $$ Htw with ⟨%kind, Hv, %Hk⟩
        obtain ⟨hkis, hkok, hkst, hne, hlen⟩ := Hk
        have hget : GetOk stn o := hokn.1
        have hkst' : kindState kind = stn := by
          rw [hkst, pendState_append, hr, hst, hstn]
        have hRR : mvcc.rangeRev kind.readRev o.base.rev = kind.readRev := by
          unfold mvcc.rangeRev; rw [hget.1]; simp
        ihave %Hset := rangeRequestIs_sortSet rr o $$ Hrr
        wp_apply (hExec ctx cd true lg s γ (GoInterface.ok twi) kind ro rr o true)
          $$ [$Hv $Hctx $Hrr] as %resp %err ⟨Hv, #Hres, %Hnd'⟩
        · isplitl []
          · simp only [↓reduceIte]; iexact Hnd
          ipureintro
          refine ⟨hget.2.1, ?_⟩
          rw [hRR]; unfold kindState at hkst'; rw [hkst']; exact hget.2.2.2
        icases rangeResult_txn resp err _ _ o hget.1 hkok.2.1 Hset hget.2.2.1 (Hnd' rfl) $$ Hres
          with ⟨%Herr, %kvs, %more, #Hresp, %Hkvs⟩
        subst Herr
        wp_auto
        isplitl []; · ipureintro; rfl
        iexists resp, GoInterface.nil
        iframe resp err txnWrite ctx lg tv
        isplitl [Hv]
        · iapply txnWriteIs_of_view _ s γ ro ilog _ kind hkis $$ Hv
        iexists kind.readRev
        try simp only [Bool.false_eq_true, ↓reduceIte]
        iexists kvs, more
        unfold kindState at hkst'
        rw [hkst'] at Hkvs
        rw [hkst']
        iframe Hresp
        ipureintro; exact Hkvs
      · -- header-only
        iapply wp_fupd
        wp_apply (wp_txnWrite_Rev hRev hRoRev twi s γ ro ilog _) $$ [$Htw] as Htw
        wp_apply (wp_txnWrite_Changes hCh hRoCh twi s γ ro ilog _) $$ [$Htw] as %chs ⟨%Hchs, Htw⟩
        wp_join iprop(∃ rv : w64, rev_ptr ↦ rv) with [rev] as ⟨%rv, rev⟩
        ihave %Hrn := typedPointsto_not_null _ _ _ $$ «$r0»
        ihave %Hhn := typedPointsto_not_null _ _ _ $$ «$v0»
        iStructNamedPrefix «$r0» "R"
        iStructNamedPrefix «$v0» "H"
        ipersist RHeader
        ipersist RKvs
        ipersist RMore
        ipersist RCount
        ipersist HRevision
        imodintro
        isplitl []; · itrivial
        iexists «$r0_ptr», e
        iframe resp err txnWrite ctx lg tv Htw
        iexists rv
        iunfold rangeResponseIs
        isplitl []; · ipureintro; exact Hrn
        iexists «$v0_ptr», slice.nil, []
        rw [show (W64 0 : w64) = 0 from rfl]
        iframe RHeader HRevision RKvs RMore RCount
        isplitl []; · ipureintro; exact Hhn
        isplitl []; · iapply ownSlice_nil
        iapply kvsIs_nil
      ipersist Hw
      icases Hrr0 with #Hrr0
      wp_apply (hStop trace _) $$ []
      · ipureintro; exact Htrace
      have hpathn : opPath s0 (.get o) = [] := opPath_nontxn s0 _ (by intros; simp)
      have hchn : (srvOp s0 r stn (.get o)).1 = [] := by rw [srvOp_get]
      wp_for_post
      iframe
      iexists n + W64 1, n, rq, plv, x, e1
      rw [hsn, opsPath_take_succ s0 ops _ _ Hop_lookup, hpathn, List.append_nil, htake, hchn,
        List.append_nil]
      rw [show opsPath s0 (ops.drop (sint.nat n)) = opsPath s0 (ops.drop (sint.nat n + 1)) by
        rw [hdropo, hpathn, List.nil_append]]
      iframe
      iframe Hplv
      simp only
      rw [hstn]
      isplitl []
      · rw [List.take_add_one, Hp_lookup, List.take_add_one, Hop_lookup]
        simp only [Option.toList_some]
        iapply responseOpsIs_snoc
        iframe Hdone
        rw [srvOp_get]
        unfold responseOpIs
        imodintro
        isplitl []; · ipureintro; exact Hpn
        iexists _, w, rr0
        iframe Hpw
        isplitl []; · ipureintro; rfl
        iframe Hw
        iexists rev1
        iexact Hrr0
      isplitl []
      · iexact Hknown
      ipureintro; exact ⟨by word, by omega⟩
    | delete o =>
      iunfold txn.opSkel at Hp
      icases Hp with ⟨%Hpn, %w, #Hpw, Hw⟩
      icases requestOpIs_delete rq o $$ Hrq with ⟨%Hrqn, %w', %dr, #Hrqw, #Hw'dr, #Hdr⟩
      have hro : ro = false := by
        cases ro
        · rfl
        · have := Hpre.2.2 rfl _ hmem; simp [txn.opIsGet] at this
      subst hro
      icases txnWriteIs_kind _ s γ false ilog _ $$ Htw with ⟨%kind, Hv, %Hk⟩
      obtain ⟨hkis, hkok, hkst, hne, hlen⟩ := Hk
      unfold KindIs at hkis
      simp only [Bool.false_eq_true, ↓reduceIte] at hkis
      obtain ⟨puts, deletes, putSize, rfl⟩ := hkis
      iunfold txnViewIs at Hv
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%mw, %Htw', Htx⟩
      cases twi with
      | mk tyX vX =>
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at Htw'
      obtain ⟨rfl, rfl⟩ := Htw'
      have hps : pendState ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1) = stn := by
        rw [pendState_append, hr, hst, hstn]
      have hdel1 := srvOp_delete s0 r stn o
      rw [hdel1] at hbnd htake
      have hdl : (delChanges stn o).length = (rangeIn stn o).length := by simp [delChanges]
      ihave Htx : mvcc.isTxnWrite mw s γ ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1)
          puts deletes putSize $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      wp_auto
      wp_apply (hDel ctx cd true mw s γ ilog _ puts deletes putSize dr o)
        $$ [$Hctx $Htx $Hdr] as %dresp %derr Hout
      · isplitl []
        · simp only [↓reduceIte]; iexact Hnd
        ipureintro
        rw [hps]; simp only [List.length_append] at hbnd ⊢; omega
      rw [hps]
      icases Hout with (⟨%Herr, ⟨%deletes', Htx⟩, #Hdresp, -⟩ | ⟨%Hc, -⟩)
      rotate_left
      · exact Hc.elim
      subst Herr
      iapply wp_fupd
      wp_auto
      ipersist Hw
      imodintro
      wp_for_post
      iframe
      iexists n + W64 1, n, rq, plv, x, e
      rw [hsn, opsPath_take_succ s0 ops _ _ Hop_lookup,
        opPath_nontxn s0 _ (by intros; simp), List.append_nil, htake]
      rw [show opsPath s0 (ops.drop (sint.nat n)) = opsPath s0 (ops.drop (sint.nat n + 1)) by
        rw [hdropo, opPath_nontxn s0 _ (by intros; simp), List.nil_append]]
      iframe
      iframe Hplv
      simp only
      rw [applyChanges_append, hstn]
      isplitl [Htx]
      · iapply txnWriteIs_of_view _ s γ false ilog _
          (.write ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1 ++ delChanges stn o)
            puts deletes' putSize)
        · rw [List.append_assoc]; exact ⟨puts, deletes', putSize, rfl⟩
        iapply (txnViewIs_mw mw s γ _).2
        simp only [mvcc.isTxn]
        iexact Htx
      isplitl []
      · rw [List.take_add_one, Hp_lookup, List.take_add_one, Hop_lookup]
        simp only [Option.toList_some]
        iapply responseOpsIs_snoc
        iframe Hdone
        unfold responseOpIs
        imodintro
        isplitl []; · ipureintro; exact Hpn
        iexists _, w, dresp
        iframe Hpw
        isplitl []; · ipureintro; rfl
        iframe Hw
        iexists _, _
        iexact Hdresp
      isplitl []
      · iapply leasesKnown_delete $$ Hknown
      ipureintro; exact ⟨by word, by omega⟩
    | txn cs ts es =>
      iunfold txn.opSkel at Hp
      icases Hp with ⟨%Hpn, %w, %r0, #Hpw, #Hwr, %Hr0n, %h0, %sl0, %ps0, #Hh0, %Hh0n, #Hrev0, #Hsucc0,
        #Hrsp0, #Hps0, Hsk0⟩
      icases requestOpIs_txn rq cs ts es $$ Hrq with ⟨%Hrqn, %w', %rq', #Hrqw, #Hw'rq, #Hrq'⟩
      wp_auto
      have hps : pendState ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1) = stn := by
        rw [pendState_append, hr, hst, hstn]
      rw [opPath_txn] at hdropo
      ihave %Hpll := ownSlice_len _ _ _ $$ Hplv
      ihave %Hplw := ownSlice_wf _ _ _ $$ Hplv
      rw [hdropo] at Hpll
      have hTlen := txnPath_length s0 { cmps := cs, thenOps := ts, elseOps := es }
      have hlen1 : 1 ≤ sint.Z plv.len := by
        simp only [List.length_cons, List.length_append] at Hpll; word
      simp only [show (0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z plv.len ∧
        sint.Z plv.len ≤ sint.Z plv.cap) from ⟨by decide, hlen1, Hplw.2⟩, _root_.and_self, ite_true]
      ihave #Hsub := txn.slice_from_et plv _ (W64 1) ⟨by decide, hlen1⟩ $$ Hplv
      rw [hdropo, show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons, List.append_assoc]
      wp_auto
      ihave Hrsk := txn.respsSkel_et s0 r0 cs ts es sl0 ps0 $$ [Hsk0]
      · iframe Hrsp0 Hps0 Hsk0
      have hokT := txn.opOk_txn_et s0 r stn cs ts es hokn.1
      have hsrv := srvOp_txn s0 r stn cs ts es
      rw [hsrv] at hbnd htake
      wp_apply IH $$ %(pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1) %rq'
          %({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel) %(slice.slice plv Bool (W64 1) plv.len)
          %(opsPath s0 (List.drop (sint.nat n + 1) ops) ++ rest) %r0 [Htw Hrsk]
        as %napp %nerr ⟨%Hres, Htw, #Hresps, #Hknown'⟩
      · iframe Htw Hrsk Hctx Hnd Hrq' Hsub
        rw [hps]
        iframe Hknown
        isplitl []
        · iapply leasesOk_sub γ.leases _ _ ?_ $$ Hleases
          intro l hl
          apply opsLeases_mem s0 ops _ hmem
          rw [txn.opLeases_txn_et]; exact hl
        ipureintro
        refine ⟨hokT, ?_, ?_⟩
        · simp only [List.length_append, TxnModel.branch, txnOk] at hbnd ⊢; omega
        · intro hro; have := Hpre.2.2 hro _ hmem; simp [txn.opIsGet] at this
      obtain ⟨rfl, rfl⟩ := Hres
      have hTl : (txnPath s0 { cmps := cs, thenOps := ts, elseOps := es }).length =
          nestedCount s0 { cmps := cs, thenOps := ts, elseOps := es } + 1 := hTlen
      generalize hnc : nestedCount s0 { cmps := cs, thenOps := ts, elseOps := es } = nc at hTl ⊢
      wp_auto
      have hL : nc + 2 ≤ sint.nat plv.len := by
        rw [← Hpll.1]; simp only [List.length_cons, List.length_append, hTl]; omega
      have hz : sint.Z (W64 (nc : Int) + W64 1) = nc + 1 := by
        have := Hplw.1; have : sint.Z plv.len < 2 ^ 63 := by word
        word
      have hzn : sint.nat (W64 (nc : Int) + W64 1) = nc + 1 := by
        have h2 : (sint.Z (W64 (nc : Int) + W64 1)).toNat = nc + 1 := by rw [hz]; omega
        exact h2
      have hle : sint.Z (W64 (nc : Int) + W64 1) ≤ sint.Z plv.len := by
        rw [hz]; have := Hpll.2; word
      simp only [show (0 ≤ sint.Z (W64 (nc : Int) + W64 1) ∧ sint.Z (W64 (nc : Int) + W64 1) ≤ sint.Z plv.len ∧
        sint.Z plv.len ≤ sint.Z plv.cap) from ⟨by omega, hle, Hplw.2⟩, _root_.and_self, ite_true]
      ihave #Hnew := txn.slice_from_et plv _ (W64 (nc : Int) + W64 1) ⟨by omega, hle⟩ $$ Hplv
      obtain ⟨y, hy⟩ := txn.drop_last_et (opsPath s0 (List.drop (sint.nat n + 1) ops) ++ rest) x
        (txnPath s0 { cmps := cs, thenOps := ts, elseOps := es })
      rw [hTl] at hy
      rw [hzn, hy]
      wp_auto
      have htk := opsPath_take_succ s0 ops (sint.nat n) _ Hop_lookup
      rw [opPath_txn] at htk
      have hcnt : W64 ((opsPath s0 (List.take (sint.nat n) ops)).length : Int) + (W64 (nc : Int) + W64 1) =
          W64 ((opsPath s0 (List.take (sint.nat n + 1) ops)).length : Int) := by
        rw [htk, List.length_append, hTl]
        simp only [W64, Int.natCast_add, Int.cast_ofNat_Int, BitVec.ofInt_add]
      rw [hcnt]
      wp_for_post
      iframe
      iexists n + W64 1, n, rq, slice.slice plv Bool (W64 (nc : Int) + W64 1) plv.len, y, e
      rw [hsn, htake]
      iframe
      iframe Hnew
      simp only
      rw [hps]
      isplitl [Htw]
      · rw [List.append_assoc]
        simp only [TxnModel.branch, txnOk]
        iexact Htw
      isplitl []
      · rw [List.take_add_one, Hp_lookup, List.take_add_one, Hop_lookup]
        simp only [Option.toList_some]
        iapply responseOpsIs_snoc
        iframe Hdone
        iapply txn.responseOpIs_txn_et skip s0 p w r0 h0 cs ts es _ $$ %Hpn Hpw Hwr %Hr0n Hh0 %Hh0n Hrev0
          Hsucc0
        simp only [TxnModel.branch, txnOk]
        iexact Hresps
      isplitl []
      · rw [show ∀ A B : List mvcc.Change, mvcc.applyChanges r st (A ++ B) = pendState ilog (pend ++ A ++ B)
          from fun A B => by rw [List.append_assoc, pendState_append, hr, hst]]
        simp only [TxnModel.branch, txnOk]
        iexact Hknown'
      ipureintro; exact ⟨by word, by omega⟩
    | _ =>
      -- a put (of any of the three kinds): `putTxnOp o`
      icases requestOpIs_put rq _ (by
          first
          | exact Or.inl ⟨_, _, _, rfl⟩
          | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
          | exact Or.inr (Or.inr ⟨_, _, rfl⟩)) $$ Hrq
        with ⟨%Hrqn, %w', %pr, %o, %Hop, #Hrqw, #Hw'pr, #Hpr⟩
      rw [Hop] at Hop_lookup hokn htake hbnd hmem hdropo
      rw [Hop, txn.opSkel_put_et]
      iunfold txn.putSkel at Hp
      icases Hp with ⟨%Hpn, %w, #Hpw, Hw⟩
      -- not the read-only wrapper: only a write transaction has puts
      have hro : ro = false := by
        cases ro
        · rfl
        · have := Hpre.2.2 rfl _ hmem; rw [txn.opIsGet_put_et] at this; cases this
      subst hro
      ihave #Hpr2 := Hpr
      iunfold txn.putRequestIs at Hpr2
      icases Hpr2 with ⟨%Hprn, %ksl, %vsl, %k, %v0, %lease, %pk, %iv0, %il, #Hk, #Hks, -, -, -, -, -, -, -, %Ho⟩
      wp_auto
      wp_apply wp_bytes_to_string ksl k DFrac.discard $$ [$Hks] as -
      wp_apply (hSize pr o) $$ [$Hpr] as %sz -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl' ⟨-, -⟩
      wp_auto
      wp_apply (hStart trace _) $$ []
      · ipureintro; exact Htrace
      -- the write transaction
      icases txnWriteIs_kind _ s γ false ilog _ $$ Htw with ⟨%kind, Hv, %Hk⟩
      obtain ⟨hkis, hkok, hkst, hne, hlen⟩ := Hk
      unfold KindIs at hkis
      simp only [Bool.false_eq_true, ↓reduceIte] at hkis
      obtain ⟨puts, deletes, putSize, rfl⟩ := hkis
      iunfold txnViewIs at Hv
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨%mw, %Htw', Htx⟩
      cases twi with
      | mk tyX vX =>
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at Htw'
      obtain ⟨rfl, rfl⟩ := Htw'
      have hps : pendState ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1) = stn := by
        rw [pendState_append, hr, hst, hstn]
      wp_apply (hPrev trace mw s γ _ pr o) $$ [$Htx $Hpr] as %pv ⟨Htx, Hpv⟩
      · ipureintro; exact Htrace
      rw [hkst, hps]
      have hput1 := srvOp_putTxnOp s0 r stn o
      rw [hput1] at hbnd htake
      simp only [List.length_singleton] at hbnd
      ihave Htx : mvcc.isTxnWrite mw s γ ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1)
          puts deletes putSize $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ihave #Hlo : leaseOk γ.leases (putLeaseOf o (mvcc.findKey o.key stn)) $$ []
      · iapply leaseOk_put γ.leases s0 stn o
        iframe Hknown
        iapply leasesOk_sub γ.leases _ _ (opsLeases_mem s0 ops _ hmem) $$ Hleases
      wp_apply (hPut ctx cd mw s γ ilog _ puts deletes putSize pr o pv)
        $$ [$Hctx $Htx $Hpr Hpv] as %presp ⟨⟨%puts', %putSize', Htx⟩, #Hpresp, -⟩
      · rw [hps]
        iframe Hpv Hlo
        ipureintro
        refine ⟨txn.opOk_put_et s0 r stn o hokn.1, ?_⟩
        simp only [List.length_append]; omega
      rw [hps]
      ipersist Hw
      wp_apply (hStop trace _) $$ []
      · ipureintro; exact Htrace
      wp_for_post
      iframe
      iexists n + W64 1, n, rq, plv, x, e
      rw [hsn, opsPath_take_succ s0 ops _ _ Hop_lookup, txn.opPath_put_et, List.append_nil, htake]
      rw [show opsPath s0 (ops.drop (sint.nat n)) = opsPath s0 (ops.drop (sint.nat n + 1)) by
        rw [hdropo, txn.opPath_put_et, List.nil_append]]
      iframe
      iframe Hplv
      simp only
      rw [applyChanges_append, hstn]
      isplitl [Htx]
      · iapply txnWriteIs_of_view _ s γ false ilog _
          (.write ilog (pend ++ (srvOps s0 r st (ops.take (sint.nat n))).1 ++
            [putChangeOf o (mvcc.findKey o.key stn)]) puts' deletes putSize')
        · rw [List.append_assoc]; exact ⟨puts', deletes, putSize', rfl⟩
        iapply (txnViewIs_mw mw s γ _).2
        simp only [mvcc.isTxn]
        iexact Htx
      isplitl []
      · rw [List.take_add_one, Hp_lookup, List.take_add_one, Hop_lookup]
        simp only [Option.toList_some]
        iapply responseOpsIs_snoc
        iframe Hdone
        iapply txn.responseOpIs_put_et skip p w presp o $$ %Hpn Hpw Hw
        iexists _, _
        iexact Hpresp
      isplitl []
      · rw [show mvcc.applyChanges r stn [putChangeOf o (mvcc.findKey o.key stn)] =
            putKv r o.key (putValOf o (mvcc.findKey o.key stn)) (putLeaseOf o (mvcc.findKey o.key stn))
              stn from rfl]
        iapply leasesKnown_put $$ [Hknown Hlo]
        iframe Hknown Hlo
      ipureintro; exact ⟨by word, by omega⟩
  · -- the end of the loop: every operation done
    have hge : ¬ sint.Z n < sint.Z bsl.len := by simpa using Hif
    have hnlen : sint.nat n = ops.length := by
      have h1 := Hbsl.1; have h2 := Hbl; have h3 := Hn.2; have h4 := Hn.1; word
    rw [hnlen, List.take_length, List.drop_length] at *
    rw [show rps.take ops.length = rps by rw [← Hrl, List.take_length]]
    iapply HΦ
    isplitl []
    · ipureintro; refine ⟨rfl, ?_⟩
      unfold nestedCount; rw [hok, hops]
    iframe Htw
    isplitl []
    · iunfold respsIs
      iexists rsl, rps
      iframe Hrsp Hrsl Hdone
    rw [pendState_append, hr, hst]
    iexact Hknown

end proof

end EtcdGrove
end Perennial
