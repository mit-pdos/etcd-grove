/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkTxn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkPut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- A `*pb.RequestOp`'s four kinds, as `checkTxn`'s type switch sees them. -/
theorem txn.requestOpIs_cases_ct (p : Loc) (op : TxnOp) :
    txn.requestOpIs (GF := GF) p op ⊢ ⌜p ≠ null⌝ ∗
      ((∃ (w r : Loc) (o : OpFull), ⌜op = .get o⌝ ∗
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
          txn.rangeRequestIs r o) ∨
       (∃ (w r : Loc) (o : OpFull), ⌜op = txn.putTxnOp o⌝ ∗
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
          txn.putRequestIs r o) ∨
       (∃ (w : Loc) (o : OpFull), ⌜op = .delete o⌝ ∗
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
              GoInterface)) ∨
       (∃ (w r : Loc) (cs : List CmpModel) (ts es : List TxnOp), ⌜op = .txn cs ts es⌝ ∗
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗
          txn.txnRequestIs r { cmps := cs, thenOps := ts, elseOps := es })) := by
  cases op
  case txn cs ts es =>
    unfold txn.requestOpIs
    iintro #⟨%Hpn, %w, %r, #HR, #Hw, %Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #H1, #H2, #H3, #H4,
      #H5, #H6, #H7, #H8, #H9⟩
    isplitl []
    · ipureintro; exact Hpn
    iright; iright; iright
    iexists w, r, cs, ts, es
    isplitl []
    · ipureintro; rfl
    iframe HR Hw
    unfold txn.txnRequestIs txn.txnFieldsIs
    isplitl []
    · ipureintro; exact Hrn
    iexists csl, ssl, fsl, cps, sps, fps
    iframe #
  all_goals
    unfold txn.requestOpIs
    iintro #⟨%Hpn, %u, %w, %r, %o, #HR, (⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩)⟩
    all_goals
      obtain ⟨rfl, hop⟩ := Hu
      isplitl []
      · ipureintro; exact Hpn
    · ileft; iexists w, r, o; iframe #; ipureintro; exact hop
    · iright; ileft; iexists w, r, o; iframe #; ipureintro; exact hop
    · iright; iright; ileft; iexists w, o; iframe #; ipureintro; exact hop

/-- The `i`-th request of the list. -/
theorem txn.requestOpsIs_elem_ct :
    ∀ (ps : List Loc) (ops : List TxnOp) (i : Nat) (p : Loc), ps[i]? = some p →
      txn.requestOpsIs (GF := GF) ps ops ⊢ ∃ op, ⌜ops[i]? = some op⌝ ∗ txn.requestOpIs p op
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | q :: ps, op :: ops, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    unfold txn.requestOpsIs
    iintro ⟨H, -⟩
    iexists op
    iframe H
    ipureintro; rfl
  | q :: ps, op :: ops, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    iapply txn.requestOpsIs_elem_ct ps ops i p h $$ H

theorem txn.requestOpsIs_length_ct :
    ∀ (ps : List Loc) (ops : List TxnOp), txn.requestOpsIs (GF := GF) ps ops ⊢ ⌜ps.length = ops.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | p :: ps, op :: ops => by
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    ihave %h := txn.requestOpsIs_length_ct ps ops $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H

/-- Dropping a nested transaction's path leaves its last verdict, then the rest. -/
theorem txn.drop_path_ct (x : Bool) (l R : List Bool) (h : l ≠ []) :
    ∃ y, (x :: (l ++ R)).drop l.length = y :: R := by
  obtain ⟨l', y, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left h
  refine ⟨y, ?_⟩
  simp

theorem txn.take_succ_ct (ops : List TxnOp) (i : Nat) (op : TxnOp) (h : ops[i]? = some op) :
    ops.take (i + 1) = ops.take i ++ [op] := by
  rw [List.take_add_one, h]; rfl

theorem txn.pathsIgnOk_step_ct (s0 : List EtcdKv) (ops : List TxnOp) (i : Nat) (op : TxnOp)
    (h : ops[i]? = some op) (h1 : txn.PathsIgnOk s0 (ops.take i)) (h2 : txn.PathIgnOk s0 op) :
    txn.PathsIgnOk s0 (ops.take (i + 1)) := by
  rw [txn.take_succ_ct ops i op h, txn.pathsIgnOk_append]
  exact ⟨h1, h2, by simp [txn.PathsIgnOk]⟩

theorem txn.leases_step_ct (L : List w64) (s0 : List EtcdKv) (ops : List TxnOp) (i : Nat) (op : TxnOp)
    (h : ops[i]? = some op) :
    txn.leasesOk (GF := GF) L (txn.opsLeases s0 (ops.take i)) ∗ txn.leasesOk L (txn.opLeases s0 op) ⊢
      txn.leasesOk L (txn.opsLeases s0 (ops.take (i + 1))) := by
  rw [txn.take_succ_ct ops i op h, txn.opsLeases_append]
  have : txn.opsLeases s0 [op] = txn.opLeases s0 op := by simp [txn.opsLeases]
  rw [this]
  exact (txn.leasesOk_append L _ _).2

/-- The path after a non-transaction operation: unchanged. -/
theorem txn.path_step_ct (s0 : List EtcdKv) (ops : List TxnOp) (i : Nat) (op : TxnOp)
    (h : ops[i]? = some op) (hn : txn.opPath s0 op = []) :
    txn.opsPath s0 (ops.drop i) = txn.opsPath s0 (ops.drop (i + 1)) ∧
      txn.opsPath s0 (ops.take (i + 1)) = txn.opsPath s0 (ops.take i) := by
  rw [txn.opsPath_drop s0 ops i op h, txn.opsPath_take_succ s0 ops i op h, hn]
  simp

theorem txn.putTxnOp_ign_ct (s0 : List EtcdKv) (o : OpFull)
    (h : txn.needsPrev o = true → (mvcc.findKey o.key s0).isSome) : txn.PathIgnOk s0 (txn.putTxnOp o) := by
  unfold txn.putTxnOp
  cases hv : o.ignoreValue <;> cases hl : o.ignoreLease <;>
    simp_all [txn.PathIgnOk, txn.needsPrev]

theorem txn.putTxnOp_leases_ct (s0 : List EtcdKv) (o : OpFull) :
    ∀ l ∈ txn.opLeases s0 (txn.putTxnOp o), l ∈ [o.leaseID] := by
  unfold txn.putTxnOp
  cases hv : o.ignoreValue <;> cases hl : o.ignoreLease <;> simp [txn.opLeases]

theorem txn.pathIgnOk_txn_ct (s0 : List EtcdKv) (cs : List CmpModel) (ts es : List TxnOp) :
    txn.PathIgnOk s0 (.txn cs ts es) ↔
      txn.PathsIgnOk s0 (({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel).branch
        (txn.txnOk s0 { cmps := cs, thenOps := ts, elseOps := es })) := by
  simp only [txn.PathIgnOk, TxnModel.branch, txn.txnOk]
  cases cs.all (cmpHolds s0) <;> rfl

theorem txn.opLeases_txn_ct (s0 : List EtcdKv) (cs : List CmpModel) (ts es : List TxnOp) :
    txn.opLeases s0 (.txn cs ts es) =
      txn.opsLeases s0 (({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel).branch
        (txn.txnOk s0 { cmps := cs, thenOps := ts, elseOps := es })) := by
  simp only [txn.opLeases, TxnModel.branch, txn.txnOk]
  cases cs.all (cmpHolds s0) <;> rfl

/-- `checkTxn`'s spec, with `0` returned on an error (as the Go code does; the recursive call's
`txnPath[txns+1:]` needs it in bounds). -/
theorem txn.checkTxn_strong
    (hRange : txn.checkRange.spec (GF := GF) (hG := hG))
    (hPut : txn.checkPut.spec (GF := GF) (hG := hG)) :
  ∀ (trace mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (rt : Loc)
    (t : TxnModel) (le : GoInterface) (γl : GName) (pl : GoSlice) (rest : List Bool)
    (Lv : List w64) (lu : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜trace ≠ null⌝ ∗
      mvcc.isTxnRead mw s γ log rev ∗ txn.txnRequestIs rt t ∗
      txn.isTxnLessor le γl ∗ (⌜lu = false⌝ ∨ lease.lessorUser γl Lv) ∗
      pl ↦*□ (txn.txnPath (mvcc.stateAfter log) t ++ rest) ∗
      ⌜lu = false → txn.txnReadonly t = true⌝ }}
    (App (App (App (App (App (Val (@! txn.checkTxn)) (Val #trace))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)))
      (Val #rt)) (Val #le)) (Val #pl))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); mvcc.isTxnRead mw s γ log rev ∗
      (⌜lu = false⌝ ∨ lease.lessorUser γl Lv) ∗
      ((⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount (mvcc.stateAfter log) t : Int) ∧
          txn.PathsIgnOk (mvcc.stateAfter log)
            (t.branch (txn.txnOk (mvcc.stateAfter log) t))⌝ ∗
        txn.leasesOk Lv (txn.opsLeases (mvcc.stateAfter log)
          (t.branch (txn.txnOk (mvcc.stateAfter log) t)))) ∨
       (⌜err ≠ GoInterface.nil ∧ n = W64 0⌝ ∗ txn.checkErrIs err)) }} := by
  intro trace mw s γ log rev rt t le γl pl rest Lv lu
  iloeb as IH generalizing %rt %t %pl %rest
  wp_start as ⟨%Htr, Htx, #Hrt, #Hle, Hu, #Hpl, %Hlu⟩
  iunfold txn.txnRequestIs at Hrt
  icases Hrt with ⟨%Hrtn, Hrt⟩
  iunfold txn.txnFieldsIs at Hrt
  icases Hrt with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcsl, #Hcs, #Hs, #Hssl, #Hss, #Hf, #Hfsl, #Hfs⟩
  wp_auto
  icases txn.isTxnRead_pure mw s γ log rev $$ Htx with ⟨Htx, %Hlog⟩
  have hks : txn.kindState (.read log rev) = mvcc.stateAfter log := by
    obtain ⟨hok, hne, hrev⟩ := Hlog
    unfold txn.kindState
    simp only [mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
    rw [hrev]; exact txn.stateAt_lastRev log hne (by have := hok.len; omega)
  generalize hs0 : mvcc.stateAfter log = s0
  rw [hs0] at hks
  have hpath : txn.txnPath s0 t ++ rest =
      txn.txnOk s0 t :: (txn.opsPath s0 (t.branch (txn.txnOk s0 t)) ++ rest) := by
    simp [txn.txnPath]
  rw [hpath]
  ihave %Hpll := ownSlice_len _ _ _ $$ Hpl
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z pl.len := by
    have h1 := Hpll.1; have h2 := Hpll.2; simp only [List.length_cons] at h1
    refine ⟨by decide, ?_⟩
    unfold sint.nat at h1; word
  simp only [Hb0, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ DFrac.discard (txn.txnOk s0 t) (by decide)
    $$ [] as -
  · iframe Hpl; ipureintro; rfl
  wp_join iprop(∃ (rsl : GoSlice) (rps : List Loc), reqs_ptr ↦ rsl ∗ rt_ptr ↦ rt ∗ rsl ↦*□ rps ∗
      txn.requestOpsIs rps (t.branch (txn.txnOk s0 t))) at (if: _ then _ else _) with [reqs rt]
      as ⟨%rsl, %rps, reqs, rt, #Hrsl, #Hrps⟩
  · cases hok : txn.txnOk s0 t
    · wp_auto
      isplitl []; · itrivial
      iexists fsl, fps; iframe; simp only [TxnModel.branch, Bool.false_eq_true, ↓reduceIte]; iframe #
    · wp_auto
      isplitl []; · itrivial
      iexists ssl, sps; iframe; simp only [TxnModel.branch, ↓reduceIte]; iframe #
  have Hro : lu = false → ∀ op ∈ t.branch (txn.txnOk s0 t), txn.opIsGet op = true :=
    fun h => txn.readonly_branch t (Hlu h) _
  generalize hops : t.branch (txn.txnOk s0 t) = ops
  rw [hops] at Hro
  ihave %Hrl := txn.requestOpsIs_length_ct _ _ $$ Hrps
  ihave %Hrsll := ownSlice_len _ _ _ $$ Hrsl
  ihave HI : (∃ (i : Nat) (pv : GoSlice) (x : Bool) (q : Loc),
      "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "req" ∷ req_ptr ↦ q ∗
      "txnPath" ∷ txnPath_ptr ↦ pv ∗ "#Hpv" ∷ pv ↦*□ (x :: (txn.opsPath s0 (ops.drop i) ++ rest)) ∗
      "txnCount" ∷ txnCount_ptr ↦ W64 ((txn.opsPath s0 (ops.take i)).length : Int) ∗
      "%Hi" ∷ ⌜i ≤ ops.length ∧ txn.PathsIgnOk s0 (ops.take i)⌝ ∗
      "#Hls" ∷ txn.leasesOk Lv (txn.opsLeases s0 (ops.take i)) ∗
      "Hu" ∷ (⌜lu = false⌝ ∨ lease.lessorUser γl Lv)) $$ [i req txnPath txnCount Hu]
  · iexists 0, pl, txn.txnOk s0 t, zero_val Loc
    simp only [named, List.drop_zero, List.take_zero]
    iframe
    iframe Hpl
    isplitl []
    · ipureintro; simp [txn.PathsIgnOk]
    simp only [txn.opsLeases]
    iapply txn.leasesOk_nil
  wp_for HI
  have hlen63 : ops.length < 2 ^ 63 := by
    have h2 := Hrsll.1; rw [Hrl] at h2; rw [h2]
    unfold sint.nat; have := BitVec.toInt_lt (x := rsl.len); omega
  have hiZ : sint.Z (W64 (i : Int)) = i := by have := Hi.1; word
  by_cases Hif : sint.Z (W64 (i : Int)) < sint.Z rsl.len
  · rw [decide_eq_true Hif]
    (try simp only [↓reduceIte])
    have hlt : i < ops.length := by
      have h2 := Hrsll.1; rw [Hrl] at h2
      have h4 : (i : Int) < sint.Z rsl.len := hiZ ▸ Hif
      unfold sint.nat at h2; unfold sint.Z at h4; omega
    obtain ⟨p, hp⟩ : ∃ p, rps[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave ⟨%op, %hop, #Hop⟩ := txn.requestOpsIs_elem_ct rps ops i p hp $$ Hrps
    have Hb : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z rsl.len :=
      ⟨by rw [hiZ]; omega, Hif⟩
    wp_auto
    simp only [Hb, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 (i : Int))) rps DFrac.discard p (by omega)
      $$ [] as -
    · iframe Hrsl; ipureintro; rw [hiZ]; exact hp
    icases txn.requestOpIs_cases_ct p op $$ Hop with ⟨%Hpn, (⟨%w, %r, %o, %Hopk, #HR, #Hw, #Hr⟩ |
      ⟨%w, %r, %o, %Hopk, #HR, #Hw, #Hr⟩ | ⟨%w, %o, %Hopk, #HR⟩ |
      ⟨%w, %r, %cs, %ts, %es, %Hopk, #HR, #Hw, #Hr⟩)⟩
    · -- a range
      subst Hopk
      wp_auto
      wp_apply (hRange mw s γ log rev r o) $$ [$Htx $Hr] as %err ⟨Htx, #Herr⟩
      iunfold txn.checkRangeErr at Herr
      icases Herr with (%He | ⟨%Hne, %ef, #Hef, %He⟩ | ⟨%Hne, %ec, #Hec, %He⟩)
      · obtain ⟨rfl, -⟩ := He
        wp_auto
        wp_for_post
        have hps := txn.path_step_ct s0 ops i _ hop (by simp [txn.opPath])
        iframe
        iexists (i + 1), pv, x, p
        rw [show (W64 ((i + 1 : Nat) : Int) : w64) = W64 (i : Int) + W64 1 by word, ← hps.1, hps.2]
        iframe
        iframe Hpv
        isplitl []
        · ipureintro
          exact ⟨hlt, txn.pathsIgnOk_step_ct s0 ops i _ hop Hi.2 (by simp [txn.PathIgnOk])⟩
        iapply txn.leases_step_ct Lv s0 ops i _ hop
        iframe Hls
        simp only [txn.opLeases]
        iapply txn.leasesOk_nil
      · subst He
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Htx Hu
        iright
        isplitl []
        · ipureintro; exact ⟨by simp, rfl⟩
        iunfold txn.checkErrIs
        iright; iright; ileft
        iexists ef; iframe Hef; ipureintro; rfl
      · subst He
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Htx Hu
        iright
        isplitl []
        · ipureintro; exact ⟨by simp, rfl⟩
        iunfold txn.checkErrIs
        iright; iright; iright
        iexists ec; iframe Hec; ipureintro; rfl
    · -- a put
      subst Hopk
      cases lu
      · exfalso
        have := Hro rfl _ (List.mem_of_getElem? hop)
        simp [txn.putTxnOp] at this
        split at this <;> (try split at this) <;> simp [txn.opIsGet] at this
      icases Hu with (%Hlu' | Hu)
      · cases Hlu'
      wp_auto
      ihave Htx : mvcc.isTxn mw s γ (.read log rev) $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      wp_apply (hPut trace mw s γ (.read log rev) le γl r o Lv) $$ [$Htx $Hr $Hle $Hu]
        as %err ⟨Htx, Hu, Herr⟩
      · ipureintro; exact Htr
      ihave Htx : mvcc.isTxnRead mw s γ log rev $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      rw [hks]
      icases Herr with (⟨⟨%He, %Hnp⟩, #Hlok⟩ | ⟨%Hne, #He⟩ | ⟨%Hne, #He⟩)
      · subst He
        wp_auto
        wp_for_post
        have hps := txn.path_step_ct s0 ops i _ hop (by
          unfold txn.putTxnOp; split <;> (try split) <;> simp [txn.opPath])
        iframe
        iexists (i + 1), pv, x, p
        rw [show (W64 ((i + 1 : Nat) : Int) : w64) = W64 (i : Int) + W64 1 by word, ← hps.1, hps.2]
        iframe
        iframe Hpv
        isplitl []
        · ipureintro
          exact ⟨hlt, txn.pathsIgnOk_step_ct s0 ops i _ hop Hi.2 (txn.putTxnOp_ign_ct s0 o Hnp)⟩
        isplitr [Hu]
        rotate_left
        · iright; iexact Hu
        iapply txn.leases_step_ct Lv s0 ops i _ hop
        iframe Hls
        iapply txn.leasesOk_sub Lv [o.leaseID] _ (txn.putTxnOp_leases_ct s0 o)
        iapply txn.leasesOk_one
        iexact Hlok
      all_goals
        ihave #He' := He
        iunfold txn.errVarIs at He'
        icases He' with ⟨%e, -, %Hee⟩
        subst Hee
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Htx
        isplitl [Hu]
        · iright; iexact Hu
        iright
        isplitl []
        · ipureintro; exact ⟨by simp, rfl⟩
        iunfold txn.checkErrIs
      · ileft; iexact He
      · iright; ileft; iexact He
    · -- a delete: no check
      subst Hopk
      wp_auto
      wp_for_post
      have hps := txn.path_step_ct s0 ops i _ hop (by simp [txn.opPath])
      iframe
      iexists (i + 1), pv, x, p
      rw [show (W64 ((i + 1 : Nat) : Int) : w64) = W64 (i : Int) + W64 1 by word, ← hps.1, hps.2]
      iframe
      iframe Hpv
      isplitl []
      · ipureintro
        exact ⟨hlt, txn.pathsIgnOk_step_ct s0 ops i _ hop Hi.2 (by simp [txn.PathIgnOk])⟩
      iapply txn.leases_step_ct Lv s0 ops i _ hop
      iframe Hls
      simp only [txn.opLeases]
      iapply txn.leasesOk_nil
    · -- a nested transaction
      subst Hopk
      cases lu
      · exfalso
        have := Hro rfl _ (List.mem_of_getElem? hop)
        simp [txn.opIsGet] at this
      icases Hu with (%Hlu' | Hu)
      · cases Hlu'
      wp_auto
      have hdrop := txn.opsPath_drop s0 ops i _ hop
      rw [txn.opPath_txn] at hdrop
      generalize htn : ({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel) = tn at hdrop
      generalize hL : txn.txnPath s0 tn = L at hdrop
      generalize hR : txn.opsPath s0 (ops.drop (i + 1)) ++ rest = R
      have hpv : x :: (txn.opsPath s0 (ops.drop i) ++ rest) = x :: (L ++ R) := by
        rw [hdrop, ← hR, List.append_assoc]
      rw [hpv]
      ihave %Hpvl := ownSlice_len _ _ _ $$ Hpv
      ihave %Hpvw := ownSlice_wf _ _ _ $$ Hpv
      have hLlen : L.length = txn.nestedCount s0 tn + 1 := by rw [← hL]; exact txn.txnPath_length s0 tn
      have hpvlen : (sint.Z pv.len) = (L.length : Int) + R.length + 1 := by
        have h1 := Hpvl.1; have h2 := Hpvl.2
        simp only [List.length_cons, List.length_append] at h1
        unfold sint.nat at h1; unfold sint.Z at h2 ⊢; omega
      have Hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z pv.len ∧ sint.Z pv.len ≤ sint.Z pv.cap := by
        refine ⟨by decide, ?_, Hpvw.2⟩
        have : sint.Z (W64 1) = 1 := rfl
        omega
      simp only [Hb1, _root_.and_self, ite_true]
      icases (ownSlice_split_all (W64 1) pv DFrac.discard _ ⟨by decide, Hb1.2.1⟩).1 $$ Hpv
        with ⟨-, #Hpv1⟩
      have hd1 : (x :: (L ++ R)).drop (sint.nat (W64 1)) = L ++ R := by
        rw [show sint.nat (W64 1) = 1 from rfl]; rfl
      rw [hd1]
      rw [← hL]
      wp_apply IH $$ %r %tn %(slice.slice pv Bool (W64 1) pv.len) %R [Htx Hu]
        as %n %err ⟨Htx, Hu, Hres⟩
      · iframe Htx Hle Hpv1
        isplitl []; · ipureintro; exact Htr
        isplitl []
        · rw [← htn]; iexact Hr
        isplitl [Hu]
        · iright; iexact Hu
        ipureintro; intro h; cases h
      rw [hL]
      have hnc : (txn.nestedCount s0 tn : Int) + 1 ≤ sint.Z pv.len := by omega
      have hlen63 : sint.Z pv.len < 2 ^ 63 := by unfold sint.Z; have := BitVec.toInt_lt (x := pv.len); omega
      icases Hres with (⟨⟨%He, %Hn, %Hig⟩, #Hls'⟩ | ⟨⟨%He, %Hn⟩, #Herr⟩)
      · subst He Hn
        have hsum : W64 (txn.nestedCount s0 tn : Int) + W64 1 = W64 (L.length : Int) := by
          rw [hLlen]; word
        rw [hsum]
        have Hb2 : 0 ≤ sint.Z (W64 (L.length : Int)) ∧ sint.Z (W64 (L.length : Int)) ≤ sint.Z pv.len ∧
            sint.Z pv.len ≤ sint.Z pv.cap := by
          have : sint.Z (W64 (L.length : Int)) = L.length := by word
          refine ⟨by omega, by omega, Hpvw.2⟩
        simp only [Hb2, _root_.and_self, ite_true]
        wp_auto
        wp_for_post
        have hLne : L ≠ [] := by intro h; rw [h] at hLlen; simp at hLlen
        obtain ⟨y, hy⟩ := txn.drop_path_ct x L R hLne
        icases (ownSlice_split_all (W64 (L.length : Int)) pv DFrac.discard _
          ⟨by omega, Hb2.2.1⟩).1 $$ Hpv with ⟨-, #Hpv2⟩
        have hn2 : sint.nat (W64 (L.length : Int)) = L.length := by
          have h : sint.Z (W64 (L.length : Int)) = L.length := by word
          unfold sint.nat; unfold sint.Z at h; rw [h]; rfl
        rw [hn2, hy]
        have htk := txn.opsPath_take_succ s0 ops i _ hop
        rw [txn.opPath_txn, htn, hL] at htk
        iframe
        iexists (i + 1), slice.slice pv Bool (W64 (L.length : Int)) pv.len, y, p
        rw [show (W64 ((i + 1 : Nat) : Int) : w64) = W64 (i : Int) + W64 1 by word, hR, htk]
        iframe
        iframe Hpv2
        isplitl [txnCount]
        · simp only [List.length_append]
          rw [show (W64 ((((txn.opsPath s0 (ops.take i)).length + L.length : Nat)) : Int) : w64) =
            W64 ((txn.opsPath s0 (ops.take i)).length : Int) + W64 (L.length : Int) by word]
          iexact txnCount
        isplitl []
        · ipureintro
          refine ⟨hlt, txn.pathsIgnOk_step_ct s0 ops i _ hop Hi.2 ?_⟩
          rw [txn.pathIgnOk_txn_ct, htn]; exact Hig
        isplitr [Hu]
        rotate_left
        · icases Hu with (Hf | Hu)
          · iexfalso; iexact Hf
          iright; iexact Hu
        iapply txn.leases_step_ct Lv s0 ops i _ hop
        iframe Hls
        rw [txn.opLeases_txn_ct, htn]
        iexact Hls'
      · subst Hn
        have h01 : sint.Z (W64 0 + W64 1 : w64) = 1 := by decide
        have Hb3 : 0 ≤ sint.Z (W64 0 + W64 1 : w64) ∧ sint.Z (W64 0 + W64 1 : w64) ≤ sint.Z pv.len ∧
            sint.Z pv.len ≤ sint.Z pv.cap := ⟨by omega, by omega, Hpvw.2⟩
        simp only [Hb3, _root_.and_self, ite_true]
        cases err with
        | nil => exact absurd rfl He
        | ok e =>
          wp_auto
          wp_for_post
          iapply HΦ
          iframe Htx
          isplitl [Hu]
          · icases Hu with (Hf | Hu)
            · iexfalso; iexact Hf
            iright; iexact Hu
          iright
          isplitl []
          · ipureintro; exact ⟨by simp, rfl⟩
          iexact Herr
  · rw [decide_eq_false Hif]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hiL : i = ops.length := by
      have h2 := Hrsll.1; rw [Hrl] at h2
      have h4 : ¬ (i : Int) < sint.Z rsl.len := hiZ ▸ Hif
      have h1 := Hi.1
      unfold sint.nat at h2; unfold sint.Z at h4; omega
    subst hiL
    rw [List.take_length]
    rw [List.take_length] at Hi
    wp_auto
    iapply HΦ
    iframe Htx Hu
    ileft
    isplitl []
    · ipureintro
      refine ⟨rfl, ?_, Hi.2⟩
      unfold txn.nestedCount; rw [hops]
    iexact Hls

theorem txn.checkTxn.wp_proof
    (hRange : txn.checkRange.spec (GF := GF) (hG := hG))
    (hPut : txn.checkPut.spec (GF := GF) (hG := hG)) :
    txn.checkTxn.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ log rev rt t le γl pl rest Lv lu hlu
  iintro %Φ ⟨#Hpkg, %Htr, Htx, #Hrt, #Hle, Hu, #Hpl⟩ HΦ
  iapply (txn.checkTxn_strong hRange hPut trace mw s γ log rev rt t le γl pl rest Lv lu) $$
    [Htx Hu] HΦ
  iframe Hpkg Htx Hrt Hle Hu Hpl
  isplitl []; · ipureintro; exact Htr
  ipureintro; exact hlu

end proof

end EtcdGrove
end Perennial
