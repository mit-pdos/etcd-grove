/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedCluster__Finalize.lean`.
Lean-first (no Rocq counterpart). Its callees with specs: zap's `Logger.Info` and `fmt.Errorf`;
the rest are the contracts the spec takes (`InvFinalize.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedCluster__Finalize
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- The end of `Finalize`: its post at the membership `σ'`, the four structs recombined from
their fields (the WAL's `haveWAL` generalized: `hb`). -/
macro "fz_finish " σ:term "," h:term : tactic => `(tactic| (
  iapply HΦ
  iexists $σ
  iframe HP
  ihave Hc : c ↦{dq} cb $$ [remotesC clC nodeIDC]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  ihave Hs : s ↦{dq} sb $$ [backendS walS]
  · iapply typedPointsto_combine _ _ _ Hsnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  ihave Hbb : sb.backend' ↦{dq} bb $$ [beHooksB beB ciB beExistB snapshotB]
  · iapply typedPointsto_combine _ _ _ Hbbnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  ihave Hwb : sb.wal' ↦{dq} wb $$ [lgW haveWALW wW stW entsW snapshotW meta'W]
  · iapply typedPointsto_combine _ _ _ Hwbnn
    simp only [TypedPointsto.typedPointstoDef, named]
    rw [hb]
    iframe
  iframe Hc Hs Hbb Hwb
  ipureintro; exact $h))

set_option hygiene false in
/-- The rest of `Finalize` after the WAL's branch, at the membership `σ'`: the missing
database's check (some boolean: on `true`, `os.RemoveAll` of the backend's path and an error),
then `ValidateMaxLearnerConfig` of the members. -/
macro "fz_tail " σ:term "," h:term : tactic => `(tactic| (
  wp_bind (App (Val (_ @!! _ @!! go!"databaseFileMissing")) _)
  iapply (Hcal.dbMissing $σ _) $$ HP
  inext; iintro %bm HP
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_bind (App (Val (_ @!! _ @!! go!"Members")) _)
    iapply (Hcl.members $σ) $$ HP
    inext; iintro %sl2 ⟨%l2, Hsl2, Hms2, %Hperm2, HP⟩
    (try wp_auto)
    wp_apply (Hcal.validateMaxLearner cv.MaxLearners' sl2 (l2.map Prod.fst)) $$ [Hsl2 Hms2] as %err -
    · iunfold membership.membersAt
      iframe Hsl2
      iapply membership.membersL_own $$ Hms2
    (try wp_auto)
    fz_finish $σ, $h
  · wp_apply (Hcal.backendPath _) as %path -
    (try wp_auto)
    wp_apply (Hcal.removeAll _) as %rerr -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply wp_Errorf $$ [Hasl] as %e -
    · iframe
      fmt_args_ok
    fz_finish $σ, $h))

set_option maxHeartbeats 0 in
theorem bootstrappedCluster.Finalize.wp_proof
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    bootstrappedCluster.Finalize.spec (GF := GF) (hG := hG) := by
  intro c s dq cb sb bb wb cv P σ0 σrec Hlg Hcl Hcal
  wp_start as ⟨Hc, Hs, Hbb, Hwb, HP⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %Hsnn⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hbb with ⟨Hbb, %Hbbnn⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hwb with ⟨Hwb, %Hwbnn⟩
  iStructNamedSuffix Hc "C"
  iStructNamedSuffix Hs "S"
  iStructNamedSuffix Hbb "B"
  iStructNamedSuffix Hwb "W"
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  generalize hb : wb.haveWAL' = hv at *
  cases hv <;> (try wp_auto)
  ·
    -- `c.cl.SetID(c.nodeID, c.cl.ID())`
    wp_bind (App (Val (_ @!! _ @!! go!"ID")) _)
    iapply (Hcl.id σ0) $$ HP
    inext; iintro %cid HP
    (try wp_auto)
    wp_bind (App (App (Val (_ @!! _ @!! go!"SetID")) _) _)
    iapply (Hcl.setID σ0 cb.nodeID' cid) $$ HP
    inext; iintro HP
    (try wp_auto)
    wp_apply (Hcal.newMembershipBackend cv.Logger' bb.be') as %mb -
    (try wp_auto)
    wp_bind (App (Val (_ @!! _ @!! go!"SetBackend")) _)
    iapply (Hcl.setBackend σ0 _) $$ HP
    inext; iintro HP
    (try wp_auto)
    wp_bind (App (Val (_ @!! _ @!! go!"Members")) _)
    iapply (Hcl.members σ0) $$ HP
    inext; iintro %sl ⟨%l, Hsl, Hms, %Hperm, HP⟩
    (try wp_auto)
    wp_apply (Hcal.validateMaxLearner cv.MaxLearners' sl (l.map Prod.fst)) $$ [Hsl Hms] as %err -
    · iunfold membership.membersAt
      iframe Hsl
      iapply membership.membersL_own $$ Hms
    (try wp_auto)
    fz_finish σ0, rfl
  · -- a WAL
    wp_apply (Hcal.newMembershipBackend cv.Logger' bb.be') as %mb -
    (try wp_auto)
    wp_bind (App (Val (_ @!! _ @!! go!"SetBackend")) _)
    iapply (Hcl.setBackend σ0 _) $$ HP
    inext; iintro HP
    (try wp_auto)
    wp_bind (App (Val (_ @!! _ @!! go!"Recover")) _)
    iapply (Hcl.recover σ0 _) $$ HP
    inext; iintro HP
    (try wp_auto)
    generalize hf : cv.ForceNewCluster' = fv
    cases fv <;> (try wp_auto)
    · -- no --force-new-cluster
      fz_tail σrec, (by simp [FinalizedSt])
    · -- --force-new-cluster: the PR's loop
      wp_apply wp_Info $$ []
      · iframe #; ipureintro; exact Hlg
      (try wp_auto)
      wp_bind (App (Val (_ @!! _ @!! go!"Members")) _)
      iapply (Hcl.members σrec) $$ HP
      inext; iintro %sl ⟨%l, Hsl, Hms, %Hperm, HP⟩
      (try wp_auto)
      ihave %Hlen := ownSlice_len $$ Hsl
      simp only [List.length_map] at Hlen
      ihave IH : iprop(∃ (n : w64) (mv : Loc),
          "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
          "HP" ∷ P (removeOthers cb.nodeID' ((l.map Prod.snd).take (sint.nat n)) σrec) ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (l.length : Int)⌝) $$ [i m HP]
      · iexists W64 0, _
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      wp_for IH
      wp_if_destruct
      · have Hlt0 : sint.Z n < sint.Z sl.len := by
          first | exact Hif | exact of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
        have Hlt : sint.nat n < l.length := by word
        obtain ⟨x, Hx⟩ : ∃ x, l[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
        simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hlt0⟩]
        wp_apply wp_load_slice_index sl (sint.Z n) (l.map Prod.fst) (DFrac.own 1) x.1 Hn.1 $$ [Hsl]
          as Hsl
        · iframe; ipureintro; simp [Hx]
        (try wp_auto)
        icases membership.membersL_acc l (sint.nat n) x Hx $$ Hms with ⟨Hx, Hback⟩
        icases membership.memberIs_id_acc x.1 x.2 $$ Hx with ⟨Hid, Hxb⟩
        (try wp_auto)
        have Hx2 : (l.map Prod.snd)[sint.nat n]? = some x.2 := by simp [Hx]
        have Hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        wp_if_destruct
        · -- this node
          (try wp_auto)
          ihave Hx := Hxb $$ Hid
          ihave Hms := Hback $$ Hx
          wp_for_post
          iframe
          iexists n + W64 1, _
          simp only [named]
          iframe
          isplitl [HP]
          · rw [Hsucc, removeOthers_take_succ _ _ _ _ _ Hx2, if_neg (by simpa using Hif)]
            iexact HP
          ipureintro; constructor <;> word
        · -- another member: `RemoveMember(m.ID, true)`
          wp_bind (App (App (Val (_ @!! _ @!! go!"RemoveMember")) _) _)
          iapply (Hcl.removeMember _ x.2) $$ HP
          inext; iintro HP
          (try wp_auto)
          ihave Hx := Hxb $$ Hid
          ihave Hms := Hback $$ Hx
          wp_for_post
          iframe
          iexists n + W64 1, _
          simp only [named]
          iframe
          isplitl [HP]
          · rw [Hsucc, removeOthers_take_succ _ _ _ _ _ Hx2, if_pos (by simpa using Hif)]; iexact HP
          ipureintro; constructor <;> word
      · -- the loop is done: every member's id
        have Hge : ¬ sint.Z n < sint.Z sl.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have Hall : (l.map Prod.snd).take (sint.nat n) = l.map Prod.snd := by
          apply List.take_of_length_le; simp; word
        rw [Hall] at *
        try simp only [decide_eq_false Hge, _root_.decide_true, ↓reduceIte]
        (try wp_auto)
        fz_tail (removeOthers cb.nodeID' (l.map Prod.snd) σrec),
          (removeOthers_finalized _ _ _ Hperm)

end proof

end EtcdGrove
end Perennial
