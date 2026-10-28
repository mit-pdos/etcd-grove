/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamWriter__closeUnlocked.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__closeUnlocked
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- A fresh `msgc`, not working, `true`. -/
local macro "close_fresh" : tactic => `(tactic| (
  wp_apply (chan.wp_make2 (V := Loc) (W64 4096))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %mc' %γm' ⟨#Hmcc, %Hcap, Hmo⟩
  simp only [show ¬ (W64 4096 = W64 0) by decide, ↓reduceIte]
  imod start_bag (swMsg Rh ty lid pid) _ mc' γm' (by trivial) $$ Hmcc Hmo with #Hbag'
  wp_auto
  iapply HΦ
  iframe HR
  isplitr
  · ipureintro; rfl
  iexists mc', γm'
  iframe; iframe #))

set_option hygiene false in
/-- After the close: the peer reported unreachable if messages were queued, a fresh `msgc`. -/
local macro "close_tail" : tactic => `(tactic| (
  wp_func_call
  wp_call
  (try wp_auto)
  wp_apply wp_Len mc γm $$ [] as %n %Hn
  · iapply is_bag_is_chan $$ Hbag
  (try wp_auto)
  subst Hri
  wp_if_destruct
  · wp_apply HRU
    (try wp_auto)
    close_fresh
  · close_fresh))

set_option maxHeartbeats 1000000 in
theorem rafthttp.streamWriter.closeUnlocked.wp_proof
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG)) :
    rafthttp.streamWriter.closeUnlocked.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid Rr cw mc γm wk cl Q
  wp_start as ⟨#Hf, Hmc, Hwk, Hcl, #Hbag, Hcls, HR⟩
  iunfold swFixed at Hf
  icases Hf with ⟨%lg, %ps, %fs, %r, %γd, %cc, %sc, %dc, %γc, %γs, %γdn, #Hlg, %Hlgnn, #Hlid,
    #Hpid, -, -, -, -, #Hr, #Hraft, -, -, -, -, -, -, -⟩
  iunfold netRaftOk at Hraft
  icases Hraft with ⟨%ri, %Hri, -, -, #HRU, -⟩
  wp_auto
  cases wk with
  | false =>
    wp_auto
    iapply HΦ
    iframe HR
    isplitr
    · ipureintro; rfl
    iexists mc, γm
    iframe; iframe #
  | true =>
    wp_auto
    simp only [↓reduceIte]
    icases Hcls with ⟨Hclose, HQ⟩
    iunfold closeRight at Hclose
    icases Hclose with ⟨%ci, %Hci, Hclose⟩
    subst Hci
    wp_auto
    wp_apply Hclose $$ [HQ] as %e
    · iexact HQ
    (try wp_auto)
    -- a failed close is logged
    cases e with
    | nil =>
      wp_auto
      close_tail
    | ok ei =>
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hlgnn
      wp_apply hIDStringPtr _ DFrac.discard pid $$ [$Hpid] as %ps' -
      wp_apply hZString as %f1 -
      wp_apply hZError as %f2 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply hWarn lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      close_tail

end proof

end EtcdGrove
end Perennial
