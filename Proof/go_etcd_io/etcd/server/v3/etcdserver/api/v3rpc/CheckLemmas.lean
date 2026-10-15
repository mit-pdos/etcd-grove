/-
The joint proof of `checkRequestOp` and `checkTxnRequest` (mutually recursive over nested
transactions: Löb induction, as the apply package's `checkTxnPermission`), and the request
predicates' lemmas (`reqOpsIs_requestOpsIs`, `txnReqIs_txnRequestIs`: the txn package's
predicates of a request whose operations are all non-empty, for the server's request path).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRequestOp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkTxnRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkPutRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkDeleteRequest

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-! ## Pure -/

theorem v3rpc.opsCheck_nil (n : Int) : v3rpc.opsCheck n [] = none := by
  simp [v3rpc.opsCheck]

theorem v3rpc.opsCheck_cons (n : Int) (u : v3rpc.ReqOp) (us : List v3rpc.ReqOp) :
    v3rpc.opsCheck n (u :: us) =
      match v3rpc.opCheck n u with
      | some e => some e
      | none => v3rpc.opsCheck n us := by
  cases h : v3rpc.opCheck n u <;> simp [v3rpc.opsCheck, h]

theorem v3rpc.opsCheck_append (n : Int) :
    ∀ (xs ys : List v3rpc.ReqOp), v3rpc.opsCheck n (xs ++ ys) =
      match v3rpc.opsCheck n xs with
      | some e => some e
      | none => v3rpc.opsCheck n ys
  | [], ys => by simp [v3rpc.opsCheck_nil]
  | x :: xs, ys => by
    rw [List.cons_append, v3rpc.opsCheck_cons, v3rpc.opsCheck_cons]
    cases v3rpc.opCheck n x with
    | some e => rfl
    | none => exact v3rpc.opsCheck_append n xs ys

/-- The first `i + 1` operations' check, from the first `i`'s and the `i`-th's. -/
theorem v3rpc.opsCheck_take_succ (n : Int) (us : List v3rpc.ReqOp) (i : Nat) (u : v3rpc.ReqOp)
    (h : us[i]? = some u) :
    v3rpc.opsCheck n (us.take (i + 1)) =
      match v3rpc.opsCheck n (us.take i) with
      | some e => some e
      | none => v3rpc.opCheck n u := by
  rw [List.take_add_one, h]
  simp only [Option.toList_some]
  rw [v3rpc.opsCheck_append]
  cases v3rpc.opsCheck n (us.take i) with
  | some e => rfl
  | none =>
    rw [v3rpc.opsCheck_cons, v3rpc.opsCheck_nil]
    cases v3rpc.opCheck n u <;> rfl

theorem v3rpc.txnCheck_eq (n : Int) (cs : List CmpModel) (ts es : List v3rpc.ReqOp) :
    v3rpc.txnCheck n cs ts es =
      if n < v3rpc.txnWidth cs ts es then some .tooManyOps
      else if cs.any (fun c => decide (c.key = [])) then some .emptyKey
      else match v3rpc.opsCheck (n - v3rpc.txnWidth cs ts es) ts with
        | some e => some e
        | none => v3rpc.opsCheck (n - v3rpc.txnWidth cs ts es) es := by
  unfold v3rpc.txnCheck
  rw [v3rpc.opCheck]
  cases v3rpc.opsCheck (n - v3rpc.txnWidth cs ts es) ts <;> rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-! ## The request predicates -/

theorem v3rpc.reqOpsIs_length :
    ∀ (ps : List Loc) (us : List v3rpc.ReqOp),
      v3rpc.reqOpsIs (GF := GF) ps us ⊢ ⌜ps.length = us.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | [], _ :: _ => by unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
  | p :: ps, u :: us => by
    unfold v3rpc.reqOpsIs
    iintro ⟨-, H⟩
    ihave %h := v3rpc.reqOpsIs_length ps us $$ H
    ipureintro; simp [h]

theorem v3rpc.reqOpsIs_elem :
    ∀ (ps : List Loc) (us : List v3rpc.ReqOp) (i : Nat) (p : Loc), ps[i]? = some p →
      v3rpc.reqOpsIs (GF := GF) ps us ⊢ ∃ u, ⌜us[i]? = some u⌝ ∗ v3rpc.reqOpIs p u
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
  | q :: ps, u :: us, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    unfold v3rpc.reqOpsIs
    iintro ⟨H, -⟩
    iexists u
    iframe H
    ipureintro; rfl
  | q :: ps, u :: us, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    unfold v3rpc.reqOpsIs
    iintro ⟨-, H⟩
    simp only [List.getElem?_cons_succ]
    iapply v3rpc.reqOpsIs_elem ps us i p h $$ H

/-! ## The txn package's request predicates, of requests with no empty operation -/

mutual
/-- A checked operation that is not empty (`toTxnOp` is `some`) denotes, in the txn package's
terms (`txn.requestOpIs`), its transaction model (a put through `putTxnOp`). -/
theorem v3rpc.reqOpIs_requestOpIs : ∀ (u : v3rpc.ReqOp) (p : Loc) (t : TxnOp),
    v3rpc.ReqOp.toTxnOp u = some t → v3rpc.reqOpIs (GF := GF) p u ⊢ txn.requestOpIs p t
  | .range o, p, t, h => by
    simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h
    subst h
    unfold v3rpc.reqOpIs txn.requestOpIs
    iintro #⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
    imodintro
    isplitr
    · ipureintro; exact Hpn
    iexists _, w, r, o
    iframe HR
    ileft
    iframe Hw Hr
    ipureintro; exact ⟨rfl, rfl⟩
  | .put o, p, t, h => by
    simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h
    subst h
    have hnt : ∀ cs ts es, txn.putTxnOp o ≠ .txn cs ts es := by
      intro cs ts es; unfold txn.putTxnOp; split <;> (try split) <;> simp
    unfold v3rpc.reqOpIs
    iintro #⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
    ihave #H : iprop(□ (⌜p ≠ null⌝ ∗ ∃ (u : GoInterface) (w r : Loc) (o' : OpFull),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□ u ∗
      ((⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w ∧
          txn.putTxnOp o = .get o'⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
        txn.rangeRequestIs r o') ∨
       (⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w ∧
          txn.putTxnOp o = txn.putTxnOp o'⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
        txn.putRequestIs r o') ∨
       (⌜u = interface.mkOk
            (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w ∧
          txn.putTxnOp o = .delete o'⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
        txn.deleteRangeRequestIs r o')))) $$ []
    · imodintro
      isplitr
      · ipureintro; exact Hpn
      iexists _, w, r, o
      iframe HR
      iright; ileft
      iframe Hw Hr
      ipureintro; exact ⟨rfl, rfl⟩
    generalize hpt : txn.putTxnOp o = pt
    cases pt with
    | txn cs ts es => exact absurd hpt (hnt cs ts es)
    | _ => unfold txn.requestOpIs; iexact H
  | .delete o, p, t, h => by
    simp only [v3rpc.ReqOp.toTxnOp, Option.some.injEq] at h
    subst h
    unfold v3rpc.reqOpIs txn.requestOpIs
    iintro #⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
    imodintro
    isplitr
    · ipureintro; exact Hpn
    iexists _, w, r, o
    iframe HR
    iright; iright
    iframe Hw Hr
    ipureintro; exact ⟨rfl, rfl⟩
  | .txn cs ts es, p, t, h => by
    simp only [v3rpc.ReqOp.toTxnOp] at h
    cases hts : v3rpc.ReqOp.toTxnOps ts with
    | none => simp [hts] at h
    | some ts' =>
      cases hes : v3rpc.ReqOp.toTxnOps es with
      | none => simp [hts, hes] at h
      | some es' =>
        simp only [hts, hes, Option.some.injEq] at h
        subst h
        unfold v3rpc.reqOpIs txn.requestOpIs
        iintro #⟨%Hpn, %w, %r, #HR, #Hw, %Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs,
          #Hcm, #Hs, #Hss, #Hsm, #Hf, #Hfs, #Hfm⟩
        ihave #Hsm' := v3rpc.reqOpsIs_requestOpsIs ts sps ts' hts $$ Hsm
        ihave #Hfm' := v3rpc.reqOpsIs_requestOpsIs es fps es' hes $$ Hfm
        imodintro
        isplitr
        · ipureintro; exact Hpn
        iexists w, r
        iframe HR Hw
        isplitr
        · ipureintro; exact Hrn
        iexists csl, ssl, fsl, cps, sps, fps
        iframe #
  | .empty, p, t, h => by simp [v3rpc.ReqOp.toTxnOp] at h

/-- Checked operations none of which is empty denote, in the txn package's terms, their
transaction models. -/
theorem v3rpc.reqOpsIs_requestOpsIs : ∀ (us : List v3rpc.ReqOp) (ps : List Loc) (ts : List TxnOp),
    v3rpc.ReqOp.toTxnOps us = some ts → v3rpc.reqOpsIs (GF := GF) ps us ⊢ txn.requestOpsIs ps ts
  | [], ps, ts, h => by
    simp only [v3rpc.ReqOp.toTxnOps, Option.some.injEq] at h
    subst h
    cases ps with
    | nil => unfold v3rpc.reqOpsIs txn.requestOpsIs; iintro -; itrivial
    | cons _ _ => unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
  | u :: us, ps, ts, h => by
    simp only [v3rpc.ReqOp.toTxnOps] at h
    cases hu : v3rpc.ReqOp.toTxnOp u with
    | none => simp [hu] at h
    | some t =>
      cases hus : v3rpc.ReqOp.toTxnOps us with
      | none => simp [hu, hus] at h
      | some ts' =>
        simp only [hu, hus, Option.some.injEq] at h
        subst h
        cases ps with
        | nil => unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
        | cons p ps =>
          unfold v3rpc.reqOpsIs txn.requestOpsIs
          iintro ⟨H, Hs⟩
          isplitl [H]
          · iapply v3rpc.reqOpIs_requestOpIs u p t hu $$ H
          · iapply v3rpc.reqOpsIs_requestOpsIs us ps ts' hus $$ Hs
end

/-- **A checked transaction request with no empty operation, in the txn package's terms**
(`txn.txnRequestIs` of its transaction model). -/
theorem v3rpc.txnReqIs_txnRequestIs (r : Loc) (cs : List CmpModel) (ts es : List v3rpc.ReqOp)
    (ts' es' : List TxnOp) (hts : v3rpc.ReqOp.toTxnOps ts = some ts')
    (hes : v3rpc.ReqOp.toTxnOps es = some es') :
    v3rpc.txnReqIs (GF := GF) r cs ts es ⊢
      txn.txnRequestIs r { cmps := cs, thenOps := ts', elseOps := es' } := by
  unfold v3rpc.txnReqIs txn.txnRequestIs txn.txnFieldsIs
  iintro ⟨%Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hf, #Hfs,
    #Hfm⟩
  ihave #Hsm' := v3rpc.reqOpsIs_requestOpsIs ts sps ts' hts $$ Hsm
  ihave #Hfm' := v3rpc.reqOpsIs_requestOpsIs es fps es' hes $$ Hfm
  isplitr
  · ipureintro; exact Hrn
  iexists csl, ssl, fsl, cps, sps, fps
  iframe #

/-- `checkTxnRequest`'s triple, as a hypothesis (the Löb induction's). -/
def v3rpc.txnChkT : IProp GF :=
  iprop(□ ∀ (r : Loc) (cs : List CmpModel) (ts es : List v3rpc.ReqOp) (n : w64)
      (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.txnReqIs r cs ts es -∗
    (▷ ∀ err : GoInterface, v3rpc.checkRes (v3rpc.txnCheck (sint.Z n) cs ts es) err -∗ Φ #err) -∗
    WP (App (App (Val (@! v3rpc.checkTxnRequest)) (Val #r)) (Val #n)) {{ Φ }})

instance v3rpc.txnChkT_persistent : Persistent (v3rpc.txnChkT (GF := GF)) := by
  unfold v3rpc.txnChkT; infer_instance

/-- **`checkRequestOp`, over `checkTxnRequest`'s triple** (`txnChkT`). -/
theorem v3rpc.checkRequestOp_of
    (hRange : v3rpc.checkRangeRequest.spec (GF := GF) (hG := hG))
    (hPut : v3rpc.checkPutRequest.spec (GF := GF) (hG := hG))
    (hDel : v3rpc.checkDeleteRequest.spec (GF := GF) (hG := hG)) :
  ∀ (p : Loc) (u : v3rpc.ReqOp) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.reqOpIs p u ∗ v3rpc.txnChkT }}
    (App (App (Val (@! v3rpc.checkRequestOp)) (Val #p)) (Val #n))
  {{ (err : GoInterface), RET #err; v3rpc.checkRes (v3rpc.opCheck (sint.Z n) u) err }} := by
  intro p u n
  wp_start as ⟨#Hp, #IH⟩
  cases u with
  | range o =>
    iunfold v3rpc.reqOpIs at Hp
    icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
    wp_auto
    wp_bind (App (Val (@! v3rpc.checkRangeRequest)) (Val #r))
    iapply (hRange r o) $$ [$Hpkg $Hr]
    iintro %err
    inext
    iintro Herr
    wp_auto
    iapply HΦ
    rw [show v3rpc.opCheck (sint.Z n) (.range o) = v3rpc.rangeCheck o by simp [v3rpc.opCheck]]
    iexact Herr
  | put o =>
    iunfold v3rpc.reqOpIs at Hp
    icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
    wp_auto
    wp_bind (App (Val (@! v3rpc.checkPutRequest)) (Val #r))
    iapply (hPut r o) $$ [$Hpkg $Hr]
    iintro %err
    inext
    iintro Herr
    wp_auto
    iapply HΦ
    rw [show v3rpc.opCheck (sint.Z n) (.put o) = v3rpc.putCheck o by simp [v3rpc.opCheck]]
    iexact Herr
  | delete o =>
    iunfold v3rpc.reqOpIs at Hp
    icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
    wp_auto
    wp_bind (App (Val (@! v3rpc.checkDeleteRequest)) (Val #r))
    iapply (hDel r o) $$ [$Hpkg $Hr]
    iintro %err
    inext
    iintro Herr
    wp_auto
    iapply HΦ
    rw [show v3rpc.opCheck (sint.Z n) (.delete o) = v3rpc.deleteCheck o by simp [v3rpc.opCheck]]
    iexact Herr
  | txn cs ts es =>
    iunfold v3rpc.reqOpIs at Hp
    icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw, %Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs,
      #Hcm, #Hs, #Hss, #Hsm, #Hf, #Hfs, #Hfm⟩
    ihave #Ht : v3rpc.txnReqIs r cs ts es $$ []
    · iunfold v3rpc.txnReqIs
      isplitr
      · ipureintro; exact Hrn
      iexists csl, ssl, fsl, cps, sps, fps
      iframe #
    wp_auto
    wp_bind (App (App (Val (@! v3rpc.checkTxnRequest)) (Val #r)) (Val #n))
    iunfold v3rpc.txnChkT at IH
    iapply IH $$ %r %cs %ts %es %n %_ [$Hpkg $Ht]
    inext
    iintro %err Herr
    wp_auto
    iapply HΦ
    rw [show v3rpc.opCheck (sint.Z n) (.txn cs ts es) = v3rpc.txnCheck (sint.Z n) cs ts es from rfl]
    iexact Herr
  | empty =>
    iunfold v3rpc.reqOpIs at Hp
    icases Hp with ⟨%Hpn, #HR⟩
    ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hinit with ⟨-, ⟨-, -, -, -, -, -, #HeN⟩, -, -⟩
    iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeN
    icases HeN with ⟨%eN, #HeN⟩
    wp_auto
    iapply HΦ
    simp only [v3rpc.opCheck, v3rpc.checkRes, txn.errVarIs, v3rpc.CheckErr.var]
    iexists eN; iframe HeN; itrivial

/-- **`checkTxnRequest`, by Löb induction** (its nested transactions through `checkRequestOp`). -/
theorem v3rpc.checkTxnRequest_loeb
    (hRange : v3rpc.checkRangeRequest.spec (GF := GF) (hG := hG))
    (hPut : v3rpc.checkPutRequest.spec (GF := GF) (hG := hG))
    (hDel : v3rpc.checkDeleteRequest.spec (GF := GF) (hG := hG)) :
    v3rpc.checkTxnRequest.spec (GF := GF) (hG := hG) := by
  intro r cs ts es n
  iloeb as IH generalizing %r %cs %ts %es %n
  wp_start as #Hr
  ihave #IHT : v3rpc.txnChkT $$ []
  · iunfold v3rpc.txnChkT; iexact IH
  iclear IH
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨#HeK, -, -, -, #HeT, -, -⟩, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeK HeT
  icases HeK with ⟨%eK, #HeK⟩
  icases HeT with ⟨%eT, #HeT⟩
  iunfold v3rpc.txnReqIs at Hr
  icases Hr with ⟨%Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm,
    #Hf, #Hfs, #Hfm⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcs
  ihave %Hsl := ownSlice_len _ _ _ $$ Hss
  ihave %Hfl := ownSlice_len _ _ _ $$ Hfs
  ihave %Hsml := v3rpc.reqOpsIs_length _ _ $$ Hsm
  ihave %Hfml := v3rpc.reqOpsIs_length _ _ $$ Hfm
  iunfold txn.comparesIs at Hcm
  icases Hcm with ⟨%Hcml, #Hcm⟩
  wp_auto
  wp_bind (If (Val #(decide (sint.Z csl.len < sint.Z ssl.len))) _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ r_ptr ↦ r ∗ ∃ oc : w64, opc_ptr ↦ oc ∗
      ⌜sint.Z oc = max (sint.Z csl.len) (sint.Z ssl.len)⌝)))
  isplitl [opc r]
  · wp_if_destruct
    · (try wp_auto)
      iframe
      ipureintro; omega
    · iframe
      ipureintro
      omega
  iintro %v ⟨%Hv, r, %oc, opc, %Hoc⟩
  subst Hv
  wp_auto
  wp_bind (If (Val #(decide (sint.Z oc < sint.Z fsl.len))) _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ r_ptr ↦ r ∗ ∃ oc' : w64, opc_ptr ↦ oc' ∗
      ⌜sint.Z oc' = max (sint.Z oc) (sint.Z fsl.len)⌝)))
  isplitl [opc r]
  · wp_if_destruct
    · (try wp_auto)
      iframe
      ipureintro; omega
    · iframe
      ipureintro
      omega
  iintro %v ⟨%Hv, r, %oc', opc, %Hoc'⟩
  subst Hv
  have Hw : sint.Z oc' = (v3rpc.txnWidth cs ts es : Int) := by
    unfold v3rpc.txnWidth
    rw [Hoc', Hoc]
    have h1 : (cs.length : Int) = sint.Z csl.len := by
      rw [← Hcml, Hcl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hcl.2
    have h2 : (ts.length : Int) = sint.Z ssl.len := by
      rw [← Hsml, Hsl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hsl.2
    have h3 : (es.length : Int) = sint.Z fsl.len := by
      rw [← Hfml, Hfl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hfl.2
    omega
  wp_auto
  wp_if_destruct
  · iapply HΦ
    rw [v3rpc.txnCheck_eq, ite_eq_left (by omega)]
    unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
    iexists eT; iframe HeT; itrivial
  have Hwn : ¬ sint.Z n < (v3rpc.txnWidth cs ts es : Int) := by omega
  have Hcsl : (cs.length : Int) = sint.Z csl.len := by
    rw [← Hcml, Hcl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hcl.2
  ihave HI : iprop(∃ (j : w64) (q : Loc),
      "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ q ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z csl.len ∧
        ∀ (k : Nat) (cm : CmpModel), k < (sint.Z j).toNat → cs[k]? = some cm → cm.key ≠ []⌝)
      $$ [i c]
  · iexists W64 0, _
    iframe i c
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hcl.2,
      fun k cm hk _ => by simp at hk⟩
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z csl.len := by simpa using Hif
    obtain ⟨pc, hp⟩ : ∃ p, cps[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hcml]; omega)⟩
    obtain ⟨cm, hcm⟩ : ∃ cm, cs[(sint.Z j).toNat]? = some cm :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z csl.len := ⟨Hj.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index csl (sint.Z j) cps DFrac.discard pc Hj.1 $$ [] as -
    · iframe Hcs; ipureintro; exact hp
    ihave #Hp := Hcm $$ %_ %pc %cm [] []
    · ipureintro; exact hp
    · ipureintro; exact hcm
    iunfold txn.compareIs at Hp
    icases Hp with ⟨%Hpn, %ksl, %esl, %e, %u, -, -, #HK, #Hk, -⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hk
    wp_auto
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      have hany : (cs.any fun c => decide (c.key = [])) = true := by
        rw [List.any_eq_true]
        refine ⟨cm, List.mem_of_getElem? hcm, ?_⟩
        have : cm.key = [] := List.eq_nil_of_length_eq_zero (by rw [Hkl.1]; word)
        simp [this]
      rw [v3rpc.txnCheck_eq, ite_eq_right_iff.mpr (fun h => absurd h Hwn), ite_eq_left hany]
      unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
      iexists eK; iframe HeK; itrivial
    · wp_for_post
      iframe
      iexists j + W64 1, pc
      iframe
      ipureintro
      refine ⟨by word, by word, fun k cm' hk hk' => ?_⟩
      by_cases hkj : k < (sint.Z j).toNat
      · exact Hj.2.2 k cm' hkj hk'
      · have : k = (sint.Z j).toNat := by
          have : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
          omega
        subst this
        rw [hcm] at hk'
        cases hk'
        intro h
        apply Hif
        rw [h] at Hkl
        simp only [List.length_nil] at Hkl
        have h0 : sint.Z ksl.len = 0 := by
          have h3 : (sint.Z ksl.len).toNat = 0 := Hkl.1.symm
          have := Hkl.2; omega
        word
  have hnone : (cs.any fun c => decide (c.key = [])) = false := by
    rw [Bool.eq_false_iff]
    intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨cm, hmem, hk⟩ := hany
    obtain ⟨k, hk', hkcm⟩ := List.getElem_of_mem hmem
    have hj : sint.Z j = sint.Z csl.len := by omega
    exact Hj.2.2 k cm (by omega) (by rw [← hkcm]; exact List.getElem?_eq_getElem hk')
      (by simpa using hk)
  obtain ⟨m, Hmdef⟩ : ∃ m : Int, m = sint.Z n - (v3rpc.txnWidth cs ts es : Int) := ⟨_, rfl⟩
  have Hm' : sint.Z (n - oc') = m := by
    rw [Hmdef]
    have : 0 ≤ sint.Z oc' := by have := Hfl.2; omega
    word
  ihave HI : iprop(∃ (j : w64) (q : Loc),
      "i" ∷ i_ptr ↦ j ∗ "u" ∷ u_ptr ↦ q ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ssl.len ∧
        v3rpc.opsCheck m (ts.take (sint.Z j).toNat) = none⌝) $$ [i u]
  · iexists W64 0, _
    iframe i u
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hsl.2, ?_⟩
    simp [v3rpc.opsCheck_nil]
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z ssl.len := by simpa using Hif
    have Hpl : (sps.length : Int) = sint.Z ssl.len := by
      rw [Hsl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hsl.2
    obtain ⟨pu, hp⟩ : ∃ p, sps[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ssl.len := ⟨Hj.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ssl (sint.Z j) sps DFrac.discard pu Hj.1 $$ [] as -
    · iframe #; ipureintro; exact hp
    ihave ⟨%uo, %huo, #Hu⟩ := v3rpc.reqOpsIs_elem _ _ _ pu hp $$ Hsm
    (try wp_auto)
    wp_apply (v3rpc.checkRequestOp_of hRange hPut hDel pu uo (n - oc')) $$ [$Hpkg $Hu $IHT]
      as %err Herr
    rw [Hm'] at *
    have Htake := v3rpc.opsCheck_take_succ m ts (sint.Z j).toNat uo huo
    cases hu : v3rpc.opCheck m uo with
    | none =>
      simp only [v3rpc.checkRes]
      icases Herr with %Hee
      subst Hee
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, pu
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 by word, Htake, Hj.2.2, hu]
    | some ce =>
      simp only [v3rpc.checkRes]
      icases Herr with #Herr
      ihave He := Herr
      iunfold txn.errVarIs at He
      icases He with ⟨%ee, -, %Hee⟩
      subst Hee
      wp_auto
      wp_for_post
      iapply HΦ
      have hall : v3rpc.opsCheck m ts = some ce := by
        rw [← List.take_append_drop ((sint.Z j).toNat + 1) ts, v3rpc.opsCheck_append, Htake,
          Hj.2.2, hu]
      rw [v3rpc.txnCheck_eq, ite_eq_right_iff.mpr (fun h => absurd h Hwn), hnone]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← Hmdef]
      rw [hall]
      iexact Herr
  have Hdone_ts : v3rpc.opsCheck m ts = none := by
    have hj : sint.Z j = sint.Z ssl.len := by omega
    have hl : (ts.length : Int) = sint.Z ssl.len := by
      rw [← Hsml, Hsl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hsl.2
    have := Hj.2.2
    rwa [show (sint.Z j).toNat = ts.length by omega, List.take_length] at this
  (try wp_auto)
  ihave HI : iprop(∃ (j : w64) (q : Loc),
      "i" ∷ i_ptr ↦ j ∗ "u" ∷ u_ptr ↦ q ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z fsl.len ∧
        v3rpc.opsCheck m (es.take (sint.Z j).toNat) = none⌝) $$ [i u]
  · iexists W64 0, _
    iframe i u
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hfl.2, ?_⟩
    simp [v3rpc.opsCheck_nil]
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z fsl.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    have Hif' : sint.Z j < sint.Z fsl.len := hlt
    have Hpl : (fps.length : Int) = sint.Z fsl.len := by
      rw [Hfl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hfl.2
    obtain ⟨pu, hp⟩ : ∃ p, fps[(sint.Z j).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z fsl.len := ⟨Hj.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index fsl (sint.Z j) fps DFrac.discard pu Hj.1 $$ [] as -
    · iframe #; ipureintro; exact hp
    ihave ⟨%uo, %huo, #Hu⟩ := v3rpc.reqOpsIs_elem _ _ _ pu hp $$ Hfm
    (try wp_auto)
    wp_apply (v3rpc.checkRequestOp_of hRange hPut hDel pu uo (n - oc')) $$ [$Hpkg $Hu $IHT]
      as %err Herr
    rw [Hm'] at *
    have Htake := v3rpc.opsCheck_take_succ m es (sint.Z j).toNat uo huo
    cases hu : v3rpc.opCheck m uo with
    | none =>
      simp only [v3rpc.checkRes]
      icases Herr with %Hee
      subst Hee
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, pu
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 by word, Htake, Hj.2.2, hu]
    | some ce =>
      simp only [v3rpc.checkRes]
      icases Herr with #Herr
      ihave He := Herr
      iunfold txn.errVarIs at He
      icases He with ⟨%ee, -, %Hee⟩
      subst Hee
      wp_auto
      wp_for_post
      iapply HΦ
      have hall : v3rpc.opsCheck m es = some ce := by
        rw [← List.take_append_drop ((sint.Z j).toNat + 1) es, v3rpc.opsCheck_append, Htake,
          Hj.2.2, hu]
      rw [v3rpc.txnCheck_eq, ite_eq_right_iff.mpr (fun h => absurd h Hwn), hnone]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← Hmdef]
      rw [Hdone_ts, hall]
      iexact Herr
  have Hif : ¬ sint.Z j < sint.Z fsl.len := hlt
  simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
  have Hdone_es : v3rpc.opsCheck m es = none := by
    have hj : sint.Z j = sint.Z fsl.len := by omega
    have hl : (es.length : Int) = sint.Z fsl.len := by
      rw [← Hfml, Hfl.1]; simp only [sint.nat]; exact Int.toNat_of_nonneg Hfl.2
    have := Hj.2.2
    rwa [show (sint.Z j).toNat = es.length by omega, List.take_length] at this
  wp_auto
  iapply HΦ
  rw [v3rpc.txnCheck_eq, ite_eq_right_iff.mpr (fun h => absurd h Hwn), hnone]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Hmdef, Hdone_ts, Hdone_es]
  unfold v3rpc.checkRes
  itrivial

end proof

end EtcdGrove
end Perennial
