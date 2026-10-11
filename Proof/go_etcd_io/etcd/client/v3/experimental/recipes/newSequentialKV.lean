/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newSequentialKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV
public import Spec.go_etcd_io.etcd.client.v3.WithLastKey
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.context.TODO
public import Spec.fmt.Sscanf
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- The sequence number `newSequentialKV` computed from the get's state `sg`: `0` for an empty
range; otherwise one past what `Sscanf` parsed from the greatest key's last field. -/
private def SeqNum (kp : GoString) (sg : List EtcdKv) (n : w64) : Prop :=
  (rangeIn sg (lastKeyOp kp) = [] ∧ n = W64 0) ∨
  ∃ v ∈ rangeIn sg (lastKeyOp kp), (∀ w ∈ rangeIn sg (lastKeyOp kp), go.GoStringLe w.key v.key) ∧
    ∃ n0 : w64, (∀ z, fmt.scanInt (lastField v.key) = some z → sint.Z n0 = z) ∧ n = n0 + W64 1

private theorem seqNum_next (kp : GoString) (sg : List EtcdKv) (n : w64) (h : SeqNum kp sg n) :
    SeqNext kp sg (kp ++ go!"/" ++ _root_.Perennial.fmt.decimalPad 16 (sint.Z n)) := by
  rcases h with ⟨h0, rfl⟩ | ⟨v, hv, hmax, n0, hscan, rfl⟩
  · left; exact ⟨h0, rfl⟩
  · right
    refine ⟨v, hv, hmax, fun n' h' => ?_⟩
    have e := hscan _ h'
    have : n0 = n' := by word
    subst this
    rfl

/-- The transaction built, ready to commit. -/
private def seqBuild (kp key val : GoString) (g : w64) : TxnBuild :=
  { model := seqTxn kp key val g, cif := true, cthen := true, celse := false }

private theorem B_conv' {PROP : Type _} [BI PROP] (B : TxnBuild → PROP) (b b' : TxnBuild)
    (h : b = b') : B b ⊢ B b' := h ▸ .rfl

theorem newSequentialKV.wp_proof (hWLK : EtcdGrove.WithLastKey.spec (GF := GF) (hG := hG))
    (hMR : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG))
    (hScan : EtcdGrove.fmt.Sscanf.spec (GF := GF) (hG := hG)) :
    newSequentialKV.spec (GF := GF) (hG := hG) := by
  intro kv pfx kp val lo
  iloeb as IH
  wp_start as ⟨#Hkv, #Hlo, %Hk⟩
  ihave #Hkv' := Hkv
  iunfold isRecipesKV at Hkv'
  icases Hkv' with ⟨#HGet, #HTxn, -, -⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  wp_apply hWLK $$ [$Hcv] as %gsl ⟨#Hgsl, -⟩
  ihave #Hgres := optsAt_res gsl (withTopM (W64 0) (W64 2)) (iprop(True) : IProp GF) $$ Hgsl
  iunfold isEtcdKVTodo at HGet
  wp_apply HGet $$ %kp %gsl %(withTopM (W64 0) (W64 2)) %(iprop(True) : IProp GF) %lo [$Hgres $Hlo]
    as %gresp %gerr ⟨-, #Hgr, -⟩
  · ipureintro
    exact ⟨lastKeyOp_not_panics, (lastKeyOp_fields kp).1⟩
  iunfold kvGetResult at Hgr
  icases Hgr with (%Hgne | ⟨%Hgnil, %g, %gm, #HgRev, -, #Hg, %Hgle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact ⟨Hgne, rfl⟩
  subst Hgnil
  obtain ⟨hlt, hrev0, hser, -⟩ := lastKeyOp_fields kp
  have hop : opGetModel kp (withTopM (W64 0) (W64 2)) = lastKeyOp kp := rfl
  rw [hop] at Hgle ⊢
  rw [ite_eq_right (c := (lastKeyOp kp).isPrefixGet pfx = true)
    (by rw [lastKeyOp_isPrefixGet]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (lastKeyOp kp).base.rev = W64 0 ∧
      KeyRangeUnder pfx (lastKeyOp kp).key (lastKeyOp kp).base.rangeEnd from
    ⟨hrev0, lastKeyOp_under pfx kp Hk.1⟩)]
  icases Hgr with ⟨%sg, %gsl', %gps, %gkvs, #Hsg, %Hwfg, #Hgsl', #Hgps, #Hgkvs, %Hgok⟩
  have Hglo := Hgle.1 hser
  have Hcases := lastKeyOp_kvs kp sg gkvs Hgok
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, #Hgkv⟩
  ihave %Hgsl'' := ownSlice_len $$ Hgps
  have hlen0 : gsl'.len = W64 0 ↔ gkvs = [] := by
    have h1 : sint.Z gsl'.len = (gkvs.length : Int) := by rw [← Hgl, Hgsl''.1]; word
    constructor
    · intro h; rw [h] at h1; exact List.eq_nil_of_length_eq_zero (by simp at h1; omega)
    · intro h; rw [h] at h1; simp at h1; word
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ n : w64, "newSeqNum" ∷ newSeqNum_ptr ↦ n ∗
        "resp" ∷ resp_ptr ↦ gresp ∗ "%Hn" ∷ ⌜SeqNum kp sg n⌝) ∨
      (∃ e : GoInterfaceOk, ⌜v = returnVal (PairV #Loc.null #(GoInterface.ok e))⌝)))
    with [newSeqNum resp]
  · -- the range is empty
    ileft
    isplitr
    · ipureintro; first | rfl | trivial
    iexists W64 0
    iframe
    ipureintro
    left
    refine ⟨?_, rfl⟩
    rcases Hcases with ⟨-, h⟩ | ⟨v, rfl, -⟩
    · exact h
    · simp at hlen0; exact absurd Hif hlen0
  · -- the last key: parse its last field
    obtain ⟨v, rfl, hv, hmax⟩ : ∃ v, gkvs = [v] ∧ v ∈ rangeIn sg (lastKeyOp kp) ∧
        ∀ w ∈ rangeIn sg (lastKeyOp kp), go.GoStringLe w.key v.key := by
      rcases Hcases with ⟨rfl, -⟩ | h
      · exact absurd (hlen0.2 rfl) Hif
      · exact h
    obtain ⟨p, rfl⟩ : ∃ p, gps = [p] := by
      cases gps with
      | nil => simp at Hgl
      | cons p ps => cases ps with
        | nil => exact ⟨p, rfl⟩
        | cons _ _ => simp at Hgl
    ihave #Hkvp := Hgkv $$ %0 %p %v %rfl %rfl
    ihave #Hkvp' := Hkvp
    iunfold kvValAt at Hkvp'
    icases Hkvp' with ⟨%keySl, %valSl, #HK, #HKs, -⟩
    icases ownSlice_elem_acc 0 p gsl' DFrac.discard [p] (by omega) rfl $$ Hgps with ⟨#Hpe, -⟩
    have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gsl'.len := by
      have := Hgsl''.2; have : gsl'.len ≠ W64 0 := Hif; constructor <;> word
    rw [ite_eq_left hb0, show sint.Z (W64 0) = 0 from rfl]
    wp_auto
    wp_apply wp_bytes_to_string keySl v.key DFrac.discard $$ [$HKs] as -
    (try wp_auto)
    wp_apply strings.wp_Split v.key go!"/" (by decide) $$ [$Hstr] as %fsl ⟨Hfsl, -⟩
    ihave %Hflen := ownSlice_len $$ Hfsl
    have hfne := _root_.Perennial.strings.split_ne_nil v.key go!"/"
    have hflen1 : 1 ≤ (_root_.Perennial.strings.split v.key go!"/").length :=
      List.length_pos_iff.mpr hfne
    have hb1 : 0 ≤ sint.Z (fsl.len - W64 1) ∧ sint.Z (fsl.len - W64 1) < sint.Z fsl.len := by
      have := Hflen.1; have := Hflen.2; constructor <;> word
    have hidx : (sint.Z (fsl.len - W64 1)).toNat =
        (_root_.Perennial.strings.split v.key go!"/").length - 1 := by
      have := Hflen.1; have := Hflen.2; word
    have hlast : (_root_.Perennial.strings.split v.key go!"/")[(sint.Z (fsl.len - W64 1)).toNat]? =
        some (lastField v.key) := by
      rw [hidx]
      unfold lastField
      rw [← List.getLast?_eq_getElem?]
      cases h : (_root_.Perennial.strings.split v.key go!"/").getLast? with
      | none => simp at h; exact absurd h hfne
      | some x => rfl
    rw [ite_eq_left hb1]
    wp_apply wp_load_slice_index fsl (sint.Z (fsl.len - W64 1)) _ _ (lastField v.key) hb1.1
      $$ [$Hfsl] as Hfsl
    · ipureintro; exact hlast
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sla ⟨Hsla, -⟩
    (try wp_auto)
    wp_apply hScan (lastField v.key) _ _ newSeqNum_ptr (W64 0) $$ [$Hfmt $Hsla $newSeqNum]
      as %cnt %serr ⟨-, %n, HnP, Hsres⟩
    icases Hsres with (⟨%Hsnil, %Hsn⟩ | %Hsne)
    · subst Hsnil
      wp_auto
      ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iexists n + W64 1
      iframe
      ipureintro
      right
      exact ⟨v, hv, hmax, n, Hsn, rfl⟩
    · obtain ⟨Hsne, -⟩ := Hsne
      obtain ⟨e, rfl⟩ : ∃ e, serr = GoInterface.ok e := by
        cases serr with
        | nil => exact absurd rfl Hsne
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      iright
      iexists e
      ipureintro; first | rfl | trivial
  iintro (⟨%Hv, %n, newSeqNum, resp, %Hn⟩ | ⟨%e, %Hv⟩)
  rotate_left
  · subst Hv
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact ⟨by simp, rfl⟩
  subst Hv
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hfmt $Hargs] as %key ⟨-, %Hkey⟩
  case wf =>
    exact .cons_string _ _ (.cons_int _ _ _ (.int n) .nil)
  rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at Hkey
  simp only [List.set_cons_succ, List.set_cons_zero] at Hkey
  have Hkey' := sprintf_slash_016d kp n key Hkey
  have Hkpk : (kp ++ go!"/") <+: key := by rw [Hkey']; exact List.prefix_append _ _
  have Hpk : pfx <+: key := Hk.1.trans ((List.prefix_append _ _).trans Hkpk)
  have Hnext : SeqNext kp sg key := Hkey' ▸ seqNum_next kp sg n Hn
  iunfold getRespRev at HgRev
  icases HgRev with ⟨%hdr, #Hhdr, %Hhdrn, #Hhrev⟩
  (try wp_auto)
  wp_apply hMR (go!"__" ++ kp) $$ [$Hcv] as %c0 #Hc0
  (try wp_auto)
  wp_apply hCmp c0 _ go!"<" .lt _ (.num (g + W64 1)) $$ [$Hcv $Hc0] as %c1 #Hc1
  · ipureintro
    refine ⟨by simp [cmpOpOf], ?_⟩
    simp [cmpKeyM, cmpArgOf]
  (try wp_auto)
  ihave #Hnil := concurrency.optsAt_nil (GF := GF)
  wp_apply hPut (go!"__" ++ kp) [] slice.nil [] $$ [$Hcv $Hnil] as %opB #HopB
  · ipureintro; exact putOp_not_panics' _ _
  (try wp_auto)
  wp_apply hPut key val slice.nil [] $$ [$Hcv $Hnil] as %opK #HopK
  · ipureintro; exact putOp_not_panics' _ _
  (try wp_auto)
  wp_apply hTODO
  (try wp_auto)
  iunfold isEtcdTxnKVTodo at HTxn
  wp_apply HTxn as %t ⟨%B, HB, #HBs, #HCommit⟩
  iunfold txnBuilderSpec at HBs
  icases HBs with ⟨#HIf, #HThen, -, -, -⟩
  iunfold txnCommitErrTodo at HCommit
  wp_apply wp_slice_literal (l := [opB, opK])
  isplitr
  · ipureintro; rfl
  iintro %slT ⟨HslT, -⟩
  ipersist HslT
  (try wp_auto)
  wp_apply wp_slice_literal (l := [c1])
  isplitr
  · ipureintro; rfl
  iintro %slC ⟨HslC, -⟩
  ipersist HslC
  (try wp_auto)
  wp_apply_raw HIf $$ %TxnBuild.empty %_
      %([compareM (cmpKeyM .mod (go!"__" ++ kp)) .lt (.num (g + W64 1))] : List CmpModel) [$HB]
  · isplitl
    · unfold cmpsAt
      iexists [c1]
      iframe HslC
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %c %mm %Hc %Hmm
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hc Hmm; subst Hc Hmm; iexact Hc1
      · simp at Hc
    · ipureintro; simp [TxnBuild.empty]
  inext
  iintro HB
  (try wp_auto)
  wp_apply_raw HThen $$ %_ %_ %([opPutModel (go!"__" ++ kp) [] [], opPutModel key val []] : List OpFull)
      %([.put (go!"__" ++ kp) [] (W64 0), .put key val (W64 0)] : List TxnOp) [$HB]
  · isplitl
    · unfold opsAt
      iexists [opB, opK]
      iframe HslT
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %v %o %Hv %Ho
      rcases i with _ | _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hv Ho; subst Hv Ho; iexact HopB
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hv Ho
        subst Hv Ho; iexact HopK
      · simp at Hv
    · ipureintro
      refine ⟨?_, rfl, rfl⟩
      simp only [List.map_cons, List.map_nil, putOp_txnOpOf']
  inext
  iintro HB
  (try wp_auto)
  ihave HB := B_conv' B _ (seqBuild kp key val g) (by rfl) $$ HB
  wp_apply HCommit $$ %(seqBuild kp key val g) %g [$HB $Hg] as %tresp %terr ⟨Hres, -⟩
  · ipureintro; exact seqTxn_under pfx kp key val g Hk.2 Hpk
  ihave #Hres := txnCommitResultTok_result _ _ _ _ _ $$ Hres
  iunfold txnCommitResult at Hres
  icases Hres with (%Hne | ⟨%Heq, %r, %s0, #Hresp, #Hr, %Hrr, #Hts⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, terr = GoInterface.ok e := by
      cases terr with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  obtain ⟨Hg_r0, Hr0, Hrmax, Hwf0⟩ := Hrr
  have Hg_r : sint.Z g ≤ sint.Z r := Hg_r0 (by simp [TxnModel.linearizable, seqTxn, TxnOp.linearizable])
  iunfold txnRespAt at Hresp
  icases Hresp with ⟨%thdr, %rsl, %ps, #HH, %Hthdr, #HRev, #HSucc, -, -, -, -⟩
  cases hok : (runTxn r s0 (seqTxn kp key val g)).1
  · -- `__kp` changed since the get: again
    obtain ⟨h1, h2⟩ := seqTxn_else kp key val g r s0 hok
    (try rw [hok])
    wp_auto
    wp_apply IH $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
    · ipureintro; exact Hk
    (try wp_auto)
    iapply HΦ
    iexact Hres
  · -- committed
    obtain ⟨hmod, h1, h2⟩ := seqTxn_then kp key val g r s0 Hgle.2 hok
    ihave ⟨#Hs0, #Hs1⟩ := txnStates_wrote pfx r s0 _ _ _ h2 h1 $$ Hts
    (try rw [hok])
    wp_auto
    wp_alloc rk as Hrk
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, g, r
    unfold ownRemoteKV RemoteKVSt.val'
    iframe Hrk Hr
    isplitr
    · unfold seqKeyPutAt
      iexists sg, s0
      iframe Hsg Hs0 Hs1
      ipureintro
      exact ⟨Hwfg, Hwf0, Hnext, Hr0, hmod⟩
    ipureintro
    exact ⟨Hkpk, Hglo, Hg_r, Hrmax⟩

end proof

end recipes
end EtcdGrove
end Perennial
