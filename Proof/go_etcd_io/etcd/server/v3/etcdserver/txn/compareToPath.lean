/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareToPath
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompares

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

theorem txn.compareToPath_opsIs_lookup :
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
    iapply txn.compareToPath_opsIs_lookup ps ops i p h $$ H

theorem txn.compareToPath_opsIs_length :
    ∀ (ps : List Loc) (ops : List TxnOp),
      txn.requestOpsIs (GF := GF) ps ops ⊢ ⌜ps.length = ops.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | p :: ps, op :: ops => by
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    ihave %h := txn.compareToPath_opsIs_length ps ops $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H

theorem txn.compareToPath.wp_proof
    (hCmps : txn.applyCompares.spec (GF := GF) (hG := hG)) :
    txn.compareToPath.spec (GF := GF) (hG := hG) := by
  intro mw s γ log rev rt t
  iloeb as IH generalizing %rt %t
  wp_start as ⟨Htx, #Ht⟩
  iunfold txn.txnRequestIs at Ht
  icases Ht with ⟨%Hnn, Hf⟩
  iunfold txn.txnFieldsIs at Hf
  icases Hf with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hfl, #Hfs, #Hfm⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := Bool) (W64 1)) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  wp_apply (hCmps mw s γ log rev csl cps t.cmps) $$ [$Htx $Hcs $Hcm] as Htx
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_replicate] at Hsll
  rw [ite_eq_left (by constructor <;> word)]
  wp_apply (wp_store_slice_index sl (sint.Z (W64 0)) _ (t.cmps.all (cmpHolds (mvcc.stateAfter log))))
    $$ [$Hsl] as Hsl
  · ipureintro; constructor <;> simp
  generalize hok : t.cmps.all (cmpHolds (mvcc.stateAfter log)) = ok
  rw [show (List.replicate 1 (zero_val Bool)).set 0 ok = [ok] from rfl]
  rw [ite_eq_left (by constructor <;> word)]
  wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) [ok] (DFrac.own 1) ok (by decide)) $$ [$Hsl] as Hsl
  · ipureintro; rfl
  wp_pures
  wp_join iprop(∃ (osl : GoSlice) (ops_ps : List Loc), ops_ptr ↦ osl ∗ rt_ptr ↦ rt ∗
      osl ↦*□ ops_ps ∗ txn.requestOpsIs ops_ps (t.branch ok)) at (if: _ then _ else _)
      with [ops rt] as ⟨%osl, %ops_ps, ops, rt, #Hos, #Hops⟩
  · cases ok
    · wp_auto
      wp_join_done
      iexists fsl, fps
      iframe
      simp only [TxnModel.branch, Bool.false_eq_true, ↓reduceIte]
      iframe #
    · wp_auto
      wp_join_done
      iexists ssl, sps
      iframe
      simp only [TxnModel.branch, ↓reduceIte]
      iframe #
  ihave %Hopl := txn.compareToPath_opsIs_length ops_ps _ $$ Hops
  ihave %Hosl := ownSlice_len _ _ _ $$ Hos
  ihave IHl : (∃ (n : w64) (pv : Loc) (cur : GoSlice), "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ pv ∗
      "txnPath" ∷ txnPath_ptr ↦ cur ∗
      "Hsl" ∷ cur ↦* (ok :: txn.opsPath (mvcc.stateAfter log) ((t.branch ok).take (sint.nat n))) ∗
      "Hcap" ∷ ownSliceCap Bool cur (DFrac.own 1) ∗ "Htx" ∷ mvcc.isTxnRead mw s γ log rev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z osl.len⌝ : IProp GF) $$ [i op txnPath Hsl Hcap Htx]
  · iexists W64 0, _, sl
    iframe
    ipureintro; exact ⟨by decide, Hosl.2⟩
  wp_for IHl
  wp_if_destruct
  · obtain ⟨hn0, hnl⟩ := Hn
    have hlt : sint.nat n < ops_ps.length := by have := Hosl.1; word
    list_elem ops_ps (sint.nat n) as p
    simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z osl.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index osl (sint.Z n) ops_ps DFrac.discard p hn0 $$ [Hos] as -
    · iframe Hos; ipureintro; exact Hp_lookup
    ihave ⟨%op, %Hop, #Hp⟩ := txn.compareToPath_opsIs_lookup ops_ps _ _ p Hp_lookup $$ Hops
    have htake : ∀ op', (t.branch ok)[sint.nat n]? = some op' →
        txn.opsPath (mvcc.stateAfter log) ((t.branch ok).take (sint.nat (n + W64 1))) =
          txn.opsPath (mvcc.stateAfter log) ((t.branch ok).take (sint.nat n)) ++
            txn.opPath (mvcc.stateAfter log) op' := by
      intro op' h'
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      exact txn.opsPath_take_succ _ _ _ _ h'
    cases op
    case txn cs ts es =>
      iunfold txn.requestOpIs at Hp
      icases Hp with ⟨%Hpn, %w, %r, #Hreq, #Hrt, %Hrn, %csl', %ssl', %fsl', %cps', %sps', %fps',
        #Hc', #Hcs', #Hcm', #Hs', #Hss', #Hsm', #Hf', #Hfs', #Hfm'⟩
      wp_auto
      rw [decide_eq_false Hrn]
      wp_auto
      ihave #Hrq : txn.txnRequestIs r { cmps := cs, thenOps := ts, elseOps := es } $$ []
      · iunfold txn.txnRequestIs
        isplitr
        · ipureintro; exact Hrn
        iunfold txn.txnFieldsIs
        iexists csl', ssl', fsl', cps', sps', fps'
        iframe #
      wp_apply IH $$ %r %{ cmps := cs, thenOps := ts, elseOps := es } [$Htx $Hrq]
        as %nsl ⟨Htx, Hnsl, Hncap⟩
      wp_apply (wp_slice_append cur _ nsl _ (DFrac.own 1)) $$ [$Hsl $Hcap $Hnsl] as %cur' ⟨Hsl, Hcap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, p, cur'
      rw [htake _ Hop, txn.opPath_txn, ← List.cons_append]
      iframe
      ipureintro; constructor <;> word
    all_goals
      iunfold txn.requestOpIs at Hp
      icases Hp with ⟨%Hpn, %u, %w, %r, %o, #Hreq, Hd⟩
      icases Hd with (⟨%Hu, -, -⟩ | ⟨%Hu, -, -⟩ | ⟨%Hu, -, -⟩)
      all_goals
        obtain ⟨Hu, -⟩ := Hu
        subst Hu
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p, cur
        rw [htake _ Hop, txn.opPath_nontxn _ _ (by intros; simp), List.append_nil]
        iframe
        ipureintro; constructor <;> word
  · obtain ⟨hn0, hnl⟩ := Hn
    have hn : sint.nat n = (t.branch ok).length := by rw [← Hopl]; have := Hosl.1; word
    rw [hn, List.take_length]
    iapply HΦ
    iframe Htx Hcap
    unfold txn.txnPath txn.txnOk
    rw [hok]
    iexact Hsl

end proof

end EtcdGrove
end Perennial
