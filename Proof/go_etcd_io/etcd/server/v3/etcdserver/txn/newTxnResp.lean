/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.newTxnResp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.newTxnResp_opsIs_length :
    ∀ (ps : List Loc) (ops : List TxnOp),
      txn.requestOpsIs (GF := GF) ps ops ⊢ ⌜ps.length = ops.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | p :: ps, op :: ops => by
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    ihave %h := txn.newTxnResp_opsIs_length ps ops $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H

theorem txn.newTxnResp_opsIs_lookup :
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
    simp only [List.getElem?_cons_succ] at h
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    simp only [List.getElem?_cons_succ]
    iapply txn.newTxnResp_opsIs_lookup ps ops i p h $$ H

theorem txn.newTxnResp_opsSkel_snoc (s0 : List EtcdKv) (p : Loc) (op : TxnOp) :
    ∀ (done : List Loc) (ops1 : List TxnOp),
      txn.opsSkel (GF := GF) s0 done ops1 ∗ txn.opSkel s0 p op ⊢
        txn.opsSkel s0 (done ++ [p]) (ops1 ++ [op])
  | [], [] => by
    simp only [List.nil_append]
    unfold txn.opsSkel txn.opsSkel
    iintro ⟨-, H⟩
    iframe H
  | q :: done, o :: ops1 => by
    simp only [List.cons_append]
    unfold txn.opsSkel
    iintro ⟨⟨Hq, H⟩, Hp⟩
    iframe Hq
    iapply txn.newTxnResp_opsSkel_snoc s0 p op done ops1 $$ [H Hp]
    iframe
  | [], _ :: _ => by unfold txn.opsSkel; iintro ⟨H, -⟩; iexfalso; iexact H
  | _ :: _, [] => by unfold txn.opsSkel; iintro ⟨H, -⟩; iexfalso; iexact H

theorem txn.newTxnResp_set_repl {α : Type} (done : List α) (z p : α) (len k : Nat)
    (hk : done.length = k) (hlt : k < len) :
    (done ++ List.replicate (len - k) z).set k p = (done ++ [p]) ++ List.replicate (len - (k + 1)) z := by
  subst hk
  obtain ⟨m, hm⟩ : ∃ m, len - done.length = m + 1 := ⟨len - done.length - 1, by omega⟩
  rw [hm, show len - (done.length + 1) = m by omega, List.replicate_succ, List.set_append_right _ _ (by omega)]
  simp

theorem txn.newTxnResp_path_drop (s0 : List EtcdKv) (ops : List TxnOp) (i : Nat) (op : TxnOp)
    (h : ops[i]? = some op) (hn : ∀ cs ts es, op ≠ .txn cs ts es) :
    txn.opsPath s0 (ops.drop i) = txn.opsPath s0 (ops.drop (i + 1)) ∧
      txn.opsPath s0 (ops.take (i + 1)) = txn.opsPath s0 (ops.take i) := by
  rw [txn.opsPath_drop s0 ops i op h, txn.opsPath_take_succ s0 ops i op h, txn.opPath_nontxn s0 op hn]
  simp

/-- A suffix of a persistent slice. -/
theorem txn.newTxnResp_slice_from (pl : GoSlice) (L : List Bool) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z pl.len) :
    pl ↦*□ L ⊢ (slice.slice pl Bool k pl.len ↦*□ L.drop (sint.nat k) : IProp GF) := by
  iintro #H
  ihave %Hl := ownSlice_len _ _ _ $$ H
  icases (ownSlice_slice k pl.len pl DFrac.discard L ⟨hk.1, hk.2, Int.le_refl _⟩).1 $$ H with ⟨-, Hm, -⟩
  have h : subslice (sint.nat k) (sint.nat pl.len) L = L.drop (sint.nat k) := by
    unfold subslice; rw [← Hl.1, List.take_length]
  rw [h]
  iexact Hm

theorem txn.newTxnResp_drop_last (R : List Bool) :
    ∀ (a : Bool) (P : List Bool), ∃ y, (a :: (P ++ R)).drop P.length = y :: R
  | a, [] => ⟨a, rfl⟩
  | a, b :: P => by
    obtain ⟨y, hy⟩ := txn.newTxnResp_drop_last R b P
    exact ⟨y, by simpa using hy⟩

/-- A nested transaction's `requestOpIs` gives its `txnRequestIs`. -/
theorem txn.newTxnResp_requestOpIs_txn (p : Loc) (cs : List CmpModel) (ts es : List TxnOp) :
    txn.requestOpIs (GF := GF) p (.txn cs ts es) ⊢
      ⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
        structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
          (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
            GoInterface) ∗
        structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗
        txn.txnRequestIs r { cmps := cs, thenOps := ts, elseOps := es } := by
  unfold txn.requestOpIs
  iintro #⟨%Hpn, %w, %r, #Hreq, #Hw, %Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #H1, #H2, #H3, #H4, #H5,
    #H6, #H7, #H8, #H9⟩
  isplitl []
  · ipureintro; exact Hpn
  iexists w, r
  iframe Hreq Hw
  unfold txn.txnRequestIs txn.txnFieldsIs
  isplitl []
  · ipureintro; exact Hrn
  iexists csl, ssl, fsl, cps, sps, fps
  iframe #

theorem txn.newTxnResp.wp_proof : txn.newTxnResp.spec (GF := GF) (hG := hG) := by
  intro rt t s0 pl rest
  iloeb as IH generalizing %rt %t %pl %rest
  wp_start as ⟨#Ht, #Hpl⟩
  iunfold txn.txnRequestIs at Ht
  icases Ht with ⟨%Hnn, Hf⟩
  iunfold txn.txnFieldsIs at Hf
  icases Hf with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hfl, #Hfs, #Hfm⟩
  ihave %Hpll := ownSlice_len _ _ _ $$ Hpl
  have hpos : 0 < sint.Z pl.len := by
    have h := Hpll.1; simp only [txn.txnPath, List.length_append, List.length_cons] at h; word
  wp_auto
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z pl.len) from ⟨by decide, hpos⟩,
    _root_.and_self, ite_true]
  wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ DFrac.discard (txn.txnOk s0 t) (by decide)
    $$ [Hpl] as -
  · iframe Hpl; ipureintro; simp [txn.txnPath]
  wp_join (iprop(reqs_ptr ↦ (if txn.txnOk s0 t then ssl else fsl) ∗ rt_ptr ↦ rt))
    at (if: _ then _ else _) with [reqs rt] as ⟨reqs, rt⟩
  · cases hok : txn.txnOk s0 t
    · wp_auto; wp_join_done
    · wp_auto; wp_join_done
  ihave #Hosl : ((if txn.txnOk s0 t then ssl else fsl) ↦*□
      (if txn.txnOk s0 t then sps else fps) : IProp GF) $$ []
  · cases txn.txnOk s0 t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iassumption
  ihave #Hops : txn.requestOpsIs (if txn.txnOk s0 t then sps else fps)
      (t.branch (txn.txnOk s0 t)) $$ []
  · unfold TxnModel.branch; cases txn.txnOk s0 t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iassumption
  generalize (if txn.txnOk s0 t then ssl else fsl) = osl
  generalize (if txn.txnOk s0 t then sps else fps) = ops_ps
  simp only [txn.txnPath, txn.nestedCount, List.cons_append]
  generalize t.branch (txn.txnOk s0 t) = ops
  generalize txn.txnOk s0 t = ok
  ihave %Hops_len := txn.newTxnResp_opsIs_length ops_ps ops $$ Hops
  ihave %Hosl_len := ownSlice_len _ _ _ $$ Hosl
  wp_apply wp_slice_make2 (V := Loc) osl.len as %rsl ⟨Hrsl, Hrcap⟩
  · ipureintro; exact Hosl_len.2
  simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z pl.len) from ⟨by decide, hpos⟩,
    _root_.and_self, ite_true]
  wp_apply wp_load_slice_index pl (sint.Z (W64 0)) _ DFrac.discard ok (by decide) $$ [Hpl] as -
  · iframe Hpl; ipureintro; rfl
  wp_pures
  irename «$v2» => Hh
  irename «$r0» => Hresp
  ihave %Hhn := typedPointsto_not_null _ _ _ $$ Hh
  ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hresp
  generalize «$r0_ptr» = respL at Hrn ⊢
  generalize «$v2_ptr» = hdrL at Hhn ⊢
  iStructNamedPrefix Hresp "R"
  iStructNamedPrefix Hh "H"
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ipersist RHeader
  ipersist RSucceeded
  ipersist RResponses
  iclear Rstate RunknownFields RsizeCache R_ Hstate HClusterId HMemberId HRaftTerm HLeaderId
    HunknownFields HsizeCache H_
  ihave IH2 : (∃ (n ig : w64) (rq : Loc) (pl' : GoSlice) (x : Bool) (done : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ ig ∗ "req" ∷ req_ptr ↦ rq ∗
      "txnPath" ∷ txnPath_ptr ↦ pl' ∗
      "#Hpl'" ∷ pl' ↦*□ (x :: (txn.opsPath s0 (ops.drop (sint.nat n)) ++ rest)) ∗
      "txnCount" ∷ txnCount_ptr ↦ W64 ((txn.opsPath s0 (ops.take (sint.nat n))).length : Int) ∗
      "Hrsl" ∷ rsl ↦* (done ++ List.replicate (sint.nat osl.len - sint.nat n) (zero_val Loc)) ∗
      "Hdone" ∷ txn.opsSkel s0 done (ops.take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z osl.len ∧ done.length = sint.nat n⌝ : IProp GF)
      $$ [i Higo req txnPath txnCount Hrsl]
  · iexists W64 0, _, _, pl, ok, []
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
    iframe Hpl
    isplitl
    · unfold txn.opsSkel; itrivial
    ipureintro; refine ⟨by decide, by word, rfl⟩
  iapply wp_fupd
  wp_for IH2
  wp_if_destruct
  · obtain ⟨hn0, hnl, hdl⟩ := Hn
    have hlt : sint.nat n < ops_ps.length := by have := Hosl_len.1; word
    list_elem ops_ps (sint.nat n) as p
    ihave ⟨%op, %Hop, #Hp⟩ := txn.newTxnResp_opsIs_lookup ops_ps ops (sint.nat n) p Hp_lookup $$ Hops
    simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z osl.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index osl (sint.Z n) ops_ps DFrac.discard p hn0 $$ [Hosl] as -
    · iframe Hosl; ipureintro; exact Hp_lookup
    cases op
    case txn cs ts es =>
      ihave ⟨%Hpn, %w, %r, #Hreq, #Hw, #Hrt⟩ := txn.newTxnResp_requestOpIs_txn p cs ts es $$ Hp
      wp_auto
      have hpath := txn.opsPath_drop s0 ops (sint.nat n) _ Hop
      rw [txn.opPath_txn] at hpath
      generalize hT : ({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel) = T at hpath ⊢
      ihave %Hpl'l := ownSlice_len _ _ _ $$ «Hpl'»
      ihave %Hpl'w := ownSlice_wf _ _ _ $$ «Hpl'»
      rw [hpath] at Hpl'l
      have hTlen := txn.txnPath_length s0 T
      have hlen1 : 1 ≤ sint.Z pl'.len := by
        simp only [List.length_cons, List.length_append] at Hpl'l; word
      simp only [show (0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z pl'.len ∧
        sint.Z pl'.len ≤ sint.Z pl'.cap) from ⟨by decide, hlen1, Hpl'w.2⟩, _root_.and_self, ite_true]
      ihave #Hsub := txn.newTxnResp_slice_from pl' _ (W64 1) ⟨by decide, hlen1⟩ $$ «Hpl'»
      rw [hpath, show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons, List.append_assoc]
      rw [txn.txnPath, List.cons_append]
      wp_apply IH $$ %r %T %(slice.slice pl' Bool (W64 1) pl'.len)
        %(txn.opsPath s0 (List.drop (sint.nat n + 1) ops) ++ rest) [] as %resp %txns ⟨Hsk, %Htxns⟩
      · iframe #
      subst Htxns
      irename «$v0» => Hw0
      irename «$r0» => Hp0
      ihave %Hp0n := typedPointsto_not_null _ _ _ $$ Hp0
      iStructNamedPrefix Hp0 "P"
      ipersist PResponse
      iStructNamedPrefix Hw0 "W"
      ipersist WResponseTxn
      iunfold txn.txnSkel at Hsk
      icases Hsk with ⟨%Hresn, %h2, #Hh2, %Hh2n, Hrev2, #Hsucc2, Hresps2⟩
      ipersist Hrev2
      iunfold txn.respsSkel at Hresps2
      icases Hresps2 with ⟨%sl2, %ps2, #Hsl2, #Hps2, Hsk2⟩
      ihave %Hrsl_len := ownSlice_len _ _ _ $$ Hrsl
      have hnr : sint.Z n < sint.Z rsl.len := by
        simp only [List.length_append, List.length_replicate] at Hrsl_len; word
      simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z rsl.len) from ⟨hn0, hnr⟩, _root_.and_self, ite_true]
      wp_apply wp_store_slice_index rsl (sint.Z n) _ _ $$ [Hrsl] as Hrsl
      · iframe Hrsl; ipureintro; refine ⟨hn0, ?_⟩; simp only [List.length_append, List.length_replicate]; word
      generalize hnc : (txn.opsPath s0 (T.branch (txn.txnOk s0 T))).length = nc
      have hTl : (txn.txnPath s0 T).length = nc + 1 := by rw [hTlen, txn.nestedCount, hnc]
      have hL : nc + 2 ≤ sint.nat pl'.len := by
        rw [← Hpl'l.1]; simp only [List.length_cons, List.length_append, hTl]; omega
      have hz : sint.Z (W64 1 + W64 (nc : Int)) = nc + 1 := by
        have := Hpl'w.1; have : sint.Z pl'.len < 2 ^ 63 := by word
        word
      have hzn : sint.nat (W64 1 + W64 (nc : Int)) = nc + 1 := by
        have h2 : (sint.Z (W64 1 + W64 (nc : Int))).toNat = nc + 1 := by rw [hz]; omega
        exact h2
      have hle : sint.Z (W64 1 + W64 (nc : Int)) ≤ sint.Z pl'.len := by
        rw [hz]; have := Hpl'l.2; word
      simp only [show (0 ≤ sint.Z (W64 1 + W64 (nc : Int)) ∧ sint.Z (W64 1 + W64 (nc : Int)) ≤ sint.Z pl'.len ∧
        sint.Z pl'.len ≤ sint.Z pl'.cap) from ⟨by omega, hle, Hpl'w.2⟩,
        _root_.and_self, ite_true]
      ihave #Hnew := txn.newTxnResp_slice_from pl' _ (W64 1 + W64 (nc : Int)) ⟨by omega, hle⟩ $$ «Hpl'»
      obtain ⟨y, hy⟩ := txn.newTxnResp_drop_last (txn.opsPath s0 (List.drop (sint.nat n + 1) ops) ++ rest)
        (txn.txnOk s0 T) (txn.opsPath s0 (T.branch (txn.txnOk s0 T)))
      rw [hnc] at hy
      rw [hzn, List.drop_succ_cons, hy]
      wp_auto
      have htake := txn.opsPath_take_succ s0 ops (sint.nat n) _ Hop
      rw [txn.opPath_txn, hT] at htake
      have hcnt : W64 ((txn.opsPath s0 (List.take (sint.nat n) ops)).length : Int) + (W64 (nc : Int) + W64 1) =
          W64 ((txn.opsPath s0 (List.take (sint.nat n + 1) ops)).length : Int) := by
        rw [htake, List.length_append, hTl]
        simp only [W64, Int.natCast_add, Int.cast_ofNat_Int, BitVec.ofInt_add]
      rw [hcnt]
      ihave Hdone : txn.opsSkel s0 (done ++ [«$r0_ptr»]) (ops.take (sint.nat n + 1)) $$ [Hdone Hsk2]
      · rw [List.take_add_one, Hop, Option.toList_some]
        iapply txn.newTxnResp_opsSkel_snoc $$ [Hdone Hsk2]
        iframe Hdone
        subst hT
        unfold txn.opSkel
        isplitl []
        · ipureintro; exact Hp0n
        iexists «$v0_ptr», resp
        isplitr
        · iexact PResponse
        isplitr
        · iexact WResponseTxn
        isplitl []
        · ipureintro; exact Hresn
        iexists h2, sl2, ps2
        iframe #
        isplitl []
        · ipureintro; exact Hh2n
        unfold TxnModel.branch txn.txnOk at *
        cases hok' : cs.all (cmpHolds s0) <;> simp only [hok', Bool.false_eq_true, ↓reduceIte] at * <;> iexact Hsk2
      wp_for_post
      iframe
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      iexists n + W64 1, n, p, _, y, done ++ [«$r0_ptr»]
      rw [hsn]
      rw [show (sint.Z n).toNat = sint.nat n from rfl,
        txn.newTxnResp_set_repl done _ _ _ _ hdl (by have := Hosl_len.1; word)]
      iframe
      isplitr
      · iexact Hnew
      ipureintro
      refine ⟨by word, by word, by simp [hdl]⟩
    all_goals
      iunfold txn.requestOpIs at Hp
      icases Hp with ⟨%Hpn, %u, %w, %r, %o', #Hreq, Hc⟩
      icases Hc with (⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩) <;>
        obtain ⟨rfl, Hop'⟩ := Hu
    all_goals first
      | (exfalso; revert Hop'; unfold txn.putTxnOp; split <;> (try split) <;> simp; done)
      | (exfalso; cases Hop'; done)
      | skip
    all_goals
      wp_auto
      irename «$v0» => Hw0
      irename «$r0» => Hp0
      ihave %Hp0n := typedPointsto_not_null _ _ _ $$ Hp0
      iStructNamedPrefix Hp0 "P"
      ipersist PResponse
      ihave %Hrsl_len := ownSlice_len _ _ _ $$ Hrsl
      have hnr : sint.Z n < sint.Z rsl.len := by
        simp only [List.length_append, List.length_replicate] at Hrsl_len; word
      simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z rsl.len) from ⟨hn0, hnr⟩, _root_.and_self, ite_true]
      wp_apply wp_store_slice_index rsl (sint.Z n) _ _ $$ [Hrsl] as Hrsl
      · iframe Hrsl; ipureintro; refine ⟨hn0, ?_⟩; simp only [List.length_append, List.length_replicate]; word
      ihave Hdone : txn.opsSkel s0 (done ++ [«$r0_ptr»]) (ops.take (sint.nat n + 1)) $$ [Hdone Hw0]
      · rw [List.take_add_one, Hop, Option.toList_some]
        iapply txn.newTxnResp_opsSkel_snoc $$ [Hdone Hw0]
        iframe Hdone
        iStructNamedPrefix Hw0 "W"
        unfold txn.opSkel
        try unfold txn.putSkel
        isplitl []
        · ipureintro; exact Hp0n
        iexists «$v0_ptr»
        iframe
        iexact PResponse
      wp_for_post
      iframe
      obtain ⟨hd, ht⟩ := txn.newTxnResp_path_drop s0 ops _ _ Hop (by intros; simp)
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      iexists n + W64 1, n, p, pl', x, done ++ [«$r0_ptr»]
      rw [hsn, ← hd, ht]
      rw [show (sint.Z n).toNat = sint.nat n from rfl,
        txn.newTxnResp_set_repl done _ _ _ _ hdl (by have := Hosl_len.1; word)]
      iframe
      isplitr
      · iexact «Hpl'»
      ipureintro
      refine ⟨by word, by word, by simp [hdl]⟩
  obtain ⟨hn0, hnl, hdl⟩ := Hn
  have hne : sint.nat n = ops.length := by have := Hosl_len.1; word
  have hol : sint.nat osl.len = ops.length := by omega
  rw [hne, List.take_length, hol, Nat.sub_self, List.replicate_zero, List.append_nil]
  ipersist Hrsl
  rw [show (zero_val etcdserverpb.ResponseHeader).Revision' = (W64 0 : w64) from rfl]
  imodintro
  iapply HΦ
  isplitl
  · iunfold txn.txnSkel
    isplitl []
    · ipureintro; exact Hrn
    iexists hdrL
    iframe RHeader RSucceeded HRevision
    isplitl []
    · ipureintro; exact Hhn
    iunfold txn.respsSkel
    iexists rsl, done
    iframe
    iframe #
  · ipureintro; rfl

end proof

end EtcdGrove
end Perennial
