/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/put.lean` (restart S7.5, step c,
2026-11-14): `context.WithTimeout(context.Background(), _)` (its facts: `bgCtx_facts`), `key(i)`,
`value(i)`, the request allocated (`putRequestIs_alloc`), `s.Put` (`EtcdServer.Put.spec`, its slot
and `E.RD` borrowed from the revocation's inner pool at level 2, `srvRevokeBuilt_innerBorrow`, and
given back, `srvRevokeInnerLoan_giveBack`), `cancel()`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Put
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Requests
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackground

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- **A thread token lends its level 2** (the revocation's inner pool's loan level). -/
theorem threadTok_lend2 (HT : 3 ≤ threadBound GF) :
    threadTok (GF := GF) ⊢ levelTok 2 ∗ (levelTok 2 -∗ threadTok) := by
  iintro H
  icases (threadTok_level0 (GF := GF)).1 $$ H with ⟨H0, H⟩
  icases (threadTokFrom_succ (GF := GF) 1 (by omega)).1 $$ H with ⟨H1, H⟩
  icases (threadTokFrom_succ (GF := GF) 2 (by omega)).1 $$ H with ⟨H2, H⟩
  iframe H2
  iintro H2
  iapply (threadTok_level0 (GF := GF)).2
  iframe H0
  iapply (threadTokFrom_succ (GF := GF) 1 (by omega)).2
  iframe H1
  iapply (threadTokFrom_succ (GF := GF) 2 (by omega)).2
  iframe

/-- `key(i)`: `"k"` followed by the byte `i`. -/
theorem wp_key (i : Nat) (hi : i < 256) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.key))
        (Val #(W64 (i : Int))))
    {{ (sl : GoSlice), RET #sl; sl ↦* keyOf i }} := by
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iExactEq Hsl
  congr 1
  have h : W8 (sint.Z (W64 (i : Int))) = W8 (i : Int) := by word
  rw [h]
  have h1 : sint.nat (W64 (0 + 1)) = 1 := by word
  rw [h1]
  rfl

/-- `value(i)`: `"v"` followed by the byte `i`. -/
theorem wp_value (i : Nat) (hi : i < 256) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.value))
        (Val #(W64 (i : Int))))
    {{ (sl : GoSlice), RET #sl; sl ↦* valOf i }} := by
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iExactEq Hsl
  congr 1
  have h : W8 (sint.Z (W64 (i : Int))) = W8 (i : Int) := by word
  rw [h]
  have h1 : sint.nat (W64 (0 + 1)) = 1 := by word
  rw [h1]
  rfl

set_option maxHeartbeats 1000000 in
theorem put.wp_proof
    (wp_Put : EtcdServer.Put.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    put.spec (GF := GF) (hG := hG) := by
  intro s E ρ γc i hi hE hlv hrb
  wp_start as ⟨#Hreq, #Hb, Htok, #Hinv, Hd⟩
  have hi256 : i < 256 := by simp only [r1NPuts] at hi; omega
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Hcci : _root_.Perennial.context.isClosedchanInit (GF := GF) $$ []
  · iapply _root_.Perennial.context.isClosedchanInit_of_init
    iexact Pctx
  (try wp_auto)
  -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply hWT $$ [] as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hfrom⟩
  · iframe #
  ihave ⟨#Hlib, #Hspan, -⟩ := bgCtx_facts ctx $$ []
  · iframe #
  (try wp_auto)
  -- `key(i)`, `value(i)`
  wp_apply (wp_key i hi256) as %ks Hks
  wp_apply (lc := 1) (wp_value i hi256) as %vs Hvs
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  have hkl : sint.Z ks.len < 2 ^ 63 - 1 := by
    obtain ⟨h1, h2⟩ := Hkl
    have h3 : (keyOf i).length = 2 := rfl
    rw [h3] at h1
    have h4 : sint.Z ks.len = 2 := by unfold sint.nat at h1; unfold sint.Z; omega
    omega
  -- the request, read-only (`putRequestIs`)
  have Ha := putRequestIs_alloc (GF := GF) «$a1_ptr»
    { state' := zeroValDef, Key' := ks, Value' := vs, Lease' := W64 0, PrevKv' := false,
      IgnoreValue' := false, IgnoreLease' := false, unknownFields' := slice.nil,
      sizeCache' := W32 0 } (keyOf i) (valOf i) hkl
  imod Ha $$ [«$a1»] with #Hr
  · isplitl [«$a1»]
    · iExactEq «$a1»
      congr 1
    iframe #
  ihave #Hr' : txn.putRequestIs «$a1_ptr» (r1PutOp i) $$ []
  · iExactEq Hr
    rfl
  -- the call's `leadTimeMu` slot and `E.RD`, borrowed at level 2
  have h3 : 3 ≤ threadBound GF := by unfold srvLevels at hlv; unfold srvLevelK srvRevokeK at hlv; omega
  icases threadTok_lend2 h3 $$ Htok with ⟨H2, Hback⟩
  imod srvRevokeBuilt_innerBorrow s E ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 H2]
    with ⟨⟨Hlt, HRD⟩, Hloan⟩
  · iframe Hlc1 H2; iexact Hb
  -- the put's update (`r1PutAu`), carrying the driver's half of the counter
  ihave Hau := r1PutAu ρ.kv γc i hi $$ [Hd]
  · iframe Hd; iexact Hinv
  imod (show ⊢ |==> srvApi.kvLogLb (GF := GF) E.γs [] by
    unfold srvApi.kvLogLb; exact monoListLbOwn_nil _) with #HF0
  -- `s.Put(ctx, &pb.PutRequest{Key: key(i), Value: value(i)})`
  wp_apply (wp_Put s E ρ ctx cd «$a1_ptr» (r1PutOp i)
      (fun _ => monoNatAuthOwn γc (1 : Qp).half (i + 1)) []) $$ [Hlt HRD Hau]
    as %resp %err ⟨Hlt, HRD, Hout⟩
  · rw [hE]
    simp only [isServerReqM_false, putPermitM]
    iframe Hlt HRD
    iframe #
    isplitr
    · iunfold idCred; ipureintro; exact hrb
    iunfold putPermit
    isplitr; · ipureintro; rfl
    iexact Hau
  imod srvRevokeInnerLoan_giveBack s E ⊤ (fun _ _ => CoPset.mem_full) $$ [Hloan Hlt HRD] with H2
  · iframe
  ihave Htok := Hback $$ H2
  (try wp_auto)
  -- `cancel()`
  wp_apply Hcancel
  (try wp_auto)
  iapply HΦ
  iframe Htok
  icases Hout with (⟨%Herr, %hm, %x, %x', %o, %skip, %Hst, -, -, -, -, -, -, -, -, HQ, -, -⟩ |
    ⟨⟨-, %Herr⟩, -⟩)
  · ileft; iframe HQ; ipureintro; exact Herr
  · iright; ipureintro; exact Herr

end proof

end etcd_restart1
end EtcdGrove
end Perennial
