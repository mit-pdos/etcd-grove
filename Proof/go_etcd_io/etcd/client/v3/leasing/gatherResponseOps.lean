/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/gatherResponseOps.lean`. Lean-first (no Rocq
counterpart). `gatherResponseOps` is recursive: the proof is by induction on the trees' size
(`OpT.sizeL`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.gatherResponseOps
public import Spec.go_etcd_io.etcd.client.v3.Op__IsTxn
public import Spec.go_etcd_io.etcd.client.v3.Op__Txn
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseTxn
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem gatherResponseOps_wp_size
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG))
    (hGRT : EtcdGrove.ResponseOp.GetResponseTxn.spec (GF := GF) (hG := hG)) :
    ∀ (N : Nat) (ts : List OpT), OpT.sizeL ts < N →
    ∀ (rsl : GoSlice) (ps : List Loc) (sl : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op)
      (ops : List TxnOp) (rs : List TxnOpResult),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ rsl ↦*□ ps ∗
      txnOpsRespN ps ops rs ∗ sl ↦*□ vs ∗ opListAtC false vs ts ∗ ⌜OpT.txnOps ts = some ops⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherResponseOps)) (Val #rsl)) (Val #sl))
  {{ (ret : GoSlice), RET #ret; opsOwn ret (OpT.chosenL ts rs) }} := by
  intro N
  induction N with
  | zero => intro ts h; omega
  | succ N IH =>
  intro ts hts rsl ps sl vs ops rs
  wp_start as ⟨#Hps, #Hresp, #Hvs, #Hts, %Hops⟩
  ihave %Hlen := opListAtC_length false vs ts $$ Hts
  ihave %Hrlen := txnOpsRespN_length ps ops rs $$ Hresp
  have Holen := OpT.txnOps_length ts ops Hops
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hpsl := ownSlice_len _ _ _ $$ Hps
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_auto
  rename_i iu_ptr
  irename : iprop(iu_ptr ↦ (zero_val w64 : w64)) => iu
  ihave IH' : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (rsl' : GoSlice)
      (rvs : List go_etcd_io.etcd.client.v3.Op) (iv : w64),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "ret" ∷ ret_ptr ↦ rsl' ∗ "#Hrsl" ∷ rsl' ↦*□ rvs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Op rsl' (DFrac.own 1) ∗
      "#Hrel" ∷ listRel opFullAt rvs (OpT.chosenL (ts.take (sint.nat n)) (rs.take (sint.nat n))) ∗
      "iu" ∷ iu_ptr ↦ iv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op ret iu]
  · iexists W64 0, _, slice.nil, [], W64 0
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, OpT.chosenL]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply listRel_nil
    ipureintro; constructor <;> word
  wp_for IH'
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨t, Hti⟩ : ∃ t, ts[sint.nat n]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    obtain ⟨r, Hri⟩ : ∃ r, rs[sint.nat n]? = some r :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hrlen.2, Holen, ← Hlen]; exact Hlt)⟩
    obtain ⟨p, Hpi⟩ : ∃ p, ps[sint.nat n]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hrlen.1, Holen, ← Hlen]; exact Hlt)⟩
    obtain ⟨op, Hop1, Hop2⟩ := OpT.txnOps_getElem ts ops _ t Hops Hti
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hsize : t.size ≤ OpT.sizeL ts := OpT.size_le_of_getElem? ts _ t Hti
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) vs DFrac.discard v Hn.1 $$ [Hvs] as -
    · iframe #; ipureintro; exact Hvi
    icases opListAtC_get false vs ts (sint.nat n) v t Hvi Hti $$ Hts with ⟨#Ht, -⟩
    ihave #Hr := txnOpsRespN_get ps ops rs (sint.nat n) p op r Hpi Hop2 Hri $$ Hresp
    cases t with
    | leaf o =>
      iunfold opTAtC at Ht
      icases Ht with ⟨#Hat, %Ho4⟩
      wp_apply hIsTxn $$ [$op $Hat] as op
      rw [decide_eq_false Ho4]
      (try wp_auto)
      wp_apply wp_slice_literal (l := [v])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, -⟩
      (try wp_auto)
      wp_apply (wp_slice_append_persistent rsl' rvs _ [v] (DFrac.own 1)) $$ [$Hrsl $Hcap $Hz]
        as %rsl'' ⟨#Hrsl'', Hcap, -⟩
      wp_for_post
      iframe
      iexists (n + W64 1), v, rsl'', rvs ++ [v], n
      simp only [named]
      rw [Hn1, OpT.chosenL_take_succ ts rs _ _ _ Hti Hri]
      simp only [OpT.chosen]
      iframe
      iframe #
      isplitr
      · iapply listRel_app
        iframe #
        iapply listRel_single
        iexact Hat
      ipureintro; constructor <;> word
    | txn o cs ts' es' =>
      obtain ⟨a, b, rfl, Ha, Hb⟩ := OpT.txnOp_txn o cs ts' es' op Hop1
      iunfold opTAtC at Ht
      icases Ht with ⟨#Hat, %Ho4, #Hcs, %tvs, %evs, #Htvs, #Hevs, -, #Hts', #Hes'⟩
      wp_apply hIsTxn $$ [$op $Hat] as op
      rw [decide_eq_true Ho4]
      (try wp_auto)
      wp_apply hTxn $$ [$op] as op
      (try wp_auto)
      have Hpb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rsl.len := ⟨Hn.1, by
        have : sint.nat n < ps.length := (List.getElem?_eq_some_iff.1 Hpi).1
        word⟩
      simp only [Hpb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index rsl (sint.Z n) ps DFrac.discard p Hn.1 $$ [Hps] as -
      · iframe #; ipureintro; exact Hpi
      cases r with
      | txn ok rs' =>
        iunfold txnOpRespN at Hr
        icases Hr with ⟨%Hpnn, %w, %tr, %sl', %ps', #Hresp', #Hw, %Htrnn, #Hsucc, #Hrsp, #Hps',
          #Hmatch⟩
        wp_apply (hGRT p w tr) $$ [$Hpb $Hresp' $Hw]
        · ipureintro; exact Hpnn
        (try wp_auto)
        have Hsz : ∀ l, (l = ts' ∨ l = es') → OpT.sizeL l < N := by
          intro l hl; simp only [OpT.size] at Hsize; rcases hl with rfl | rfl <;> omega
        cases ok with
        | true =>
          (try wp_auto)
          wp_apply (IH ts' (Hsz ts' (Or.inl rfl)) sl' ps' v.thenOps' tvs a rs') $$ [$Hps' $Hmatch $Htvs $Hts']
            as %r Hr'
          · ipureintro; exact Ha
          iunfold opsOwn at Hr'
          icases Hr' with ⟨%rvs2, #Hr2, -, %Hrl, #Hrr⟩
          (try wp_auto)
          wp_apply (wp_slice_append_persistent rsl' rvs r rvs2 DFrac.discard) $$ [$Hrsl $Hcap $Hr2]
            as %rsl'' ⟨#Hrsl'', Hcap, -⟩
          wp_for_post
          iframe
          iexists (n + W64 1), v, rsl'', rvs ++ rvs2, n
          simp only [named]
          rw [Hn1, OpT.chosenL_take_succ ts rs _ _ _ Hti Hri]
          simp only [OpT.chosen]
          iframe
          iframe #
          isplitr
          · iapply listRel_app
            iframe #
            iunfold listRel
            iframe #
            ipureintro; exact Hrl
          ipureintro; constructor <;> word
        | false =>
          (try wp_auto)
          wp_apply (IH es' (Hsz es' (Or.inr rfl)) sl' ps' v.elseOps' evs b rs') $$ [$Hps' $Hmatch $Hevs $Hes']
            as %r Hr'
          · ipureintro; exact Hb
          iunfold opsOwn at Hr'
          icases Hr' with ⟨%rvs2, #Hr2, -, %Hrl, #Hrr⟩
          (try wp_auto)
          wp_apply (wp_slice_append_persistent rsl' rvs r rvs2 DFrac.discard) $$ [$Hrsl $Hcap $Hr2]
            as %rsl'' ⟨#Hrsl'', Hcap, -⟩
          wp_for_post
          iframe
          iexists (n + W64 1), v, rsl'', rvs ++ rvs2, n
          simp only [named]
          rw [Hn1, OpT.chosenL_take_succ ts rs _ _ _ Hti Hri]
          simp only [OpT.chosen]
          iframe
          iframe #
          isplitr
          · iapply listRel_app
            iframe #
            iunfold listRel
            iframe #
            ipureintro; exact Hrl
          ipureintro; constructor <;> word
      | range _ _ => iunfold txnOpRespN at Hr; iexfalso; iexact Hr
      | put => iunfold txnOpRespN at Hr; iexfalso; iexact Hr
      | delete _ => iunfold txnOpRespN at Hr; iexfalso; iexact Hr
  · (try wp_auto)
    have hn : sint.nat n = ts.length := by
      rw [← Hlen]; word
    iapply HΦ
    rw [hn, List.take_length, show List.take ts.length rs = rs by
      rw [List.take_of_length_le]; omega]
    iunfold opsOwn
    iexists rvs
    iframe
    iframe #
    iunfold listRel at Hrel
    iexact Hrel

theorem gatherResponseOps.wp_proof
    (hIsTxn : EtcdGrove.Op.IsTxn.spec (GF := GF) (hG := hG))
    (hTxn : EtcdGrove.Op.Txn.spec (GF := GF) (hG := hG))
    (hGRT : EtcdGrove.ResponseOp.GetResponseTxn.spec (GF := GF) (hG := hG)) :
    gatherResponseOps.spec (GF := GF) (hG := hG) := by
  intro rsl ps sl vs ts ops rs
  exact gatherResponseOps_wp_size hIsTxn hTxn hGRT (OpT.sizeL ts + 1) ts (Nat.lt_succ_self _)
    rsl ps sl vs ops rs

end proof

end leasing
end EtcdGrove
end Perennial
