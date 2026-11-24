/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/Run.lean` (restart S7.5, step g,
2026-11-14). Lean-first (no Rocq counterpart). The ghost state of the cluster (`etcdstart.alloc1_false`)
and `restart1`'s KV invariant at its bootstrap state (`r1Inv_alloc`); the first start
(`startMember.spec`); the puts (`put.spec`, the counter's half passed from one to the next); the stop
(`stop.spec`, out of `memberUp_splitStop`); the restart (`startMember.specRestart`, with the cluster's
persistent facts kept from the first start's boot bundle, `memberBoot_restartFacts`, and `ETCD_VERIFY`
off from the fresh bundle); and the check (`check.spec`, under the invariant at the restarted names,
`r1Inv_st`). No restart-only row is a premise: `startMember.wp_proofRestart` discharges them.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.put
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc

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

/-- `put(s, j)` at a `w64` argument. -/
theorem wp_put' (wp_put : put.spec (GF := GF) (hG := hG)) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γc : GName) (j : w64) (h0 : 0 ≤ sint.Z j) (hj : sint.Z j < r1NPuts)
    [ReceiptBoundLe GF (2 ^ 48)] (hE : E.authOn = false) (hlv : srvLevels (GF := GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
        isServerReq s E ρ ∗ srvRevokeBuilt s E ∗ threadTok ∗
        r1Inv ρ.kv γc ∗ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.put))
        (Val #s)) (Val #j))
    {{ (err : GoInterface), RET #err; threadTok ∗
        ((⌜err = GoInterface.nil⌝ ∗ monoNatAuthOwn γc (1 : Qp).half (sint.nat j + 1)) ∨
          ⌜err ≠ GoInterface.nil⌝) }} := by
  have hw := wp_put s E ρ γc (sint.nat j) (by unfold sint.nat; unfold sint.Z at h0 hj; omega)
    hE hlv
  rwa [show W64 ((sint.nat j : Nat) : Int) = j by unfold sint.nat; word] at hw

set_option maxHeartbeats 2000000 in
theorem Run.wp_proof
    (wp_startMember : startMember.spec (GF := GF) (hG := hG))
    (wp_startMemberR : startMember.specRestart (GF := GF) (hG := hG))
    (wp_put : put.spec (GF := GF) (hG := hG))
    (wp_stop : stop.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro CS lg N id ctxs boot ThB RcB RcN Hbf hlv HwbN Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Hstart, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#HpremF, #HbR⟩
  iunfold etcdstart.premises at HpremF
  icases HpremF with ⟨#Hboot, #Hmarsh, #Hzap, #Htd⟩
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (dir id)
      name name urlsOk id (etcdstart.cfgOk name name) urlsOk (fun _ h => h) (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false hne id ctxs boot Hbf (dir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, hcmp, -⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  have Hdirok : netDirOk (dir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- `restart1`'s KV invariant, at the bootstrap state (no key in the range)
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
    etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
  imod (r1Inv_alloc ρ.rd.kv _ (by rw [kvStateOf_kvs (lt := [])]; simp [mvcc.stateAfter, mvcc.stateAt, mvcc.applyChanges])
      (by rw [kvStateOf_rev]; rfl) ⊤) $$ Hetcd with ⟨%γc, #Hinv, Hd⟩
  -- the cluster's persistent facts, kept for the restart; `ETCD_VERIFY` off, kept likewise
  icases etcdstart.memberBoot_restartFacts γ ctxs ρ E₀ Φs id $$ Hmb with ⟨#Hrfs, Hmb⟩
  icases etcdstart.memberBoot_cmp γ ctxs ρ E₀ Φs id false $$ Hmb with ⟨%HE0cmp, Hmb⟩
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  icases etcdstart.memberFreshRes_verify _ _ γn $$ Hfresh with ⟨#Hvoff, Hfresh⟩
  (try wp_auto)
  -- `s, err := startMember(lg)`
  wp_apply (wp_startMember N lg (LogEntry.toEntries boot 0) ctxs id γ ρ E₀ Φs γn HwbN hvs hrule
      hboot hblen hγn1 hγn2 Hdirok Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh] as %s %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, #Hdd⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  icases memberUp_splitStop hRS s ρ E₀ lg γn id .none $$ Hup with
    ⟨%E, %γw, %dd, %HE, #Hreq, #Hrd, #Hrvb, Hgo, Hsr, Hrds⟩
  ihave #Hai := isServerRead_applied s E ρ.rd $$ Hrd
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨-, Htok⟩
  -- the puts of `key(i) ↦ value(i)`, `i < NPuts`, the counter's half passed along
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 11⌝ ∗
      "Htok" ∷ threadTok ∗ "Hd" ∷ monoNatAuthOwn γc (1 : Qp).half (sint.nat j) : IProp GF)
      $$ [i Htok Hd]
  · iexists W64 0; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_put' wp_put s E { ρ with wait := γw } γc j Hj.1
        (by have := Hif; simp only [show sint.Z (W64 11) = 11 by rfl] at this; simp only [r1NPuts]; omega)
        HE.2 hlv) $$ [Htok Hd] as %perr ⟨Htok, Hput⟩
    · iframe; iframe #
    icases Hput with (⟨%Hperr, Hd⟩ | %Hperr)
    rotate_left
    · cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      wp_auto
      wp_for_post
      iapply HΦ; itrivial
    subst Hperr
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hif; simp only [show sint.Z (W64 11) = 11 by rfl] at this
      unfold sint.nat; word
    rw [hj1]
    iframe
    ipureintro; constructor <;> word
  have hj11 : sint.nat j = r1NPuts := by
    have := Hif; simp only [show sint.Z (W64 11) = 11 by rfl] at this
    simp only [r1NPuts]; unfold sint.nat; word
  rw [hj11]
  ihave #Hlb := monoNatLbOwn_get γc _ r1NPuts $$ Hd
  -- `stop(s)`
  ihave %Hρr : ⌜ρ.rd.raft.raft = γ⌝ $$ []
  · ihave #Hf := Hrfs
    iunfold etcdstart.memberRestartFacts at Hf
    icases Hf with ⟨%Hρ, -⟩
    ipureintro; rw [Hρ.1]
  have Hb1 : ρ.rd.raft.raft.boot.length ≤ 1 := by rw [Hρr, hboot]; simp [LogEntry.toEntries, hblen0]
  have Hsc : srvStop.scope E := ⟨HE.2, by rw [HE.1.2.2.2, HE0cmp]⟩
  wp_apply (wp_stop s E E ρ id dd γn Hb1 Hsc) $$ [Hsr Hrds] as Hrr
  · iframe; iframe #
  rw [Hρr]
  (try wp_auto)
  -- `sR, err := startMember(lg)`: the restart
  wp_apply (wp_startMemberR N lg (LogEntry.toEntries boot 0) ctxs id γ ρ γn HwbN hvs hrule
      hboot hblen hγn1 hγn2 Hdirok Haf Hbuq Hdbo) $$ [Htok Hrr] as %sR %err2 Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %ρ', %E₀', %Hρ', HupR, -⟩)
  · cases err2 with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  -- `check(sR)`, under the invariant at the restarted names
  ihave #HinvR : r1Inv ρ'.rd.kv γc $$ []
  · rw [← r1Inv_st ρ.rd.kv ρ'.rd.kv (restartNames_st Hρ').symm γc]
    iexact Hinv
  wp_apply (wp_check sR ρ' E₀' lg γn id γc hlv) $$ [HupR] as %b -
  · iframe; iframe #
  iapply HΦ; itrivial

end proof

end etcd_restart1
end EtcdGrove
end Perennial
