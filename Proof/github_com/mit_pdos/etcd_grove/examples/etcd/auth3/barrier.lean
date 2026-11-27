/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth3/barrier.lean` (the auth3 Scope's A2,
2026-11-14). Lean-first (no Rocq counterpart). Root's client of the member (`newUserClient`, over
`Authenticate`'s registration, `authTokReg_of`); a timeout context; `root.Get(ctx, "z/barrier")`
(`client_Get_on`), linearizable, at the bound `ai0 + |Lc|` the set-up's committed log gives
(`committedAtLeast_of_rlog`, L2), its check's facts (`rangeAuthed`, with L1's published index) turned
into `akAuthFixed` at the member (`akAuthFixed_barrier`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.barrier
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.newUserClient
public import Spec.context.ErrAny
public import Spec.context.WithTimeoutBackground
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.CallLaws
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.ServeLaws

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section pure
variable [GooseExts]

/-- A log with consecutive indices after `ai₀` ends at an index that fits in a word. -/
theorem srvIdxOkW_end (ai₀ : w64) (L : List EntryModel) (h : srvIdxOkW ai₀ L) :
    uint.Z ai₀ + L.length < 2 ^ 64 := by
  cases hL : L.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hL; subst hL
    have := (uint_Z_lt ai₀); simp; omega
  | some m =>
    have hm : L[L.length - 1]? = some m := by rw [← List.getLast?_eq_getElem?]; exact hL
    have h1 := (h (L.length - 1) m hm).1
    have := uint_Z_lt m.index
    omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

set_option maxHeartbeats 800000 in
theorem barrier.wp_proof
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (h_client_Get_on : etcd_auth.client_Get_on.law (GF := GF) (hG := hG))
    (h_authTokReg_of : client.authTokReg_of.law (GF := GF) (hG := hG)) :
    barrier.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS addr lg V s E ρ cid mid γa γz hs Lset Lc r Hpe Htb HEo hAs
  wp_start as ⟨Hlt, #Hlgz, #HAu, #HKV, #Hrd, #Hfz, #HLs, %Hh, #HLc, %HLcst⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hall : client.ctxErrClientAll (GF := GF) $$ []
  · ihave #Hw := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hw
    iunfold client.ctxErrClientAll
    iexact Hw
  (try wp_auto)
  -- `root, err := newUserClient(addr, "root", rootPw, lg)`
  wp_apply (wp_newUserClient addr go!"root" go!"root-pw" lg V
      (fun t => auth.tokIssued γa t go!"root") Hpe Htb (by unfold strsSizeOk; decide))
    $$ [$Hlt] as %rcl %rerr ⟨Hlt, Hrc⟩
  · iframe #
    iapply (h_authTokReg_of _ _ _ γa)
    iexact HAu
  icases Hrc with (⟨%Hrerr, #Hrnc, #Hrtk⟩ | %Hrfail)
  rotate_left
  · obtain ⟨Hrerr, -⟩ := Hrfail
    cases rerr with
    | nil => exact absurd rfl Hrerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
  subst Hrerr
  wp_auto
  ihave #Hrtk0 := Hrtk
  iunfold clientTokAt at Hrtk0
  icases Hrtk0 with ⟨%rapi, %rconn, #Hrkvf, #Hrobj, -, -, -⟩
  -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg wp_WithTimeout wp_ErrAny hAs _)
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -, #HeO⟩
  iunfold metadata.outgoingCtxOkC at HeO
  icases HeO with ⟨%eom, #Heom⟩
  (try wp_auto)
  -- `root.Get(ctx, "z/barrier")`, at the bound `ai0 + |Lc|`
  ihave %HLcI := srvRLogLb_idx ρ.raft Lc $$ HLc
  have hend := srvIdxOkW_end ρ.raft.ai0 Lc HLcI
  have hc : uint.Z (W64 (uint.Z ρ.raft.ai0 + Lc.length)) = uint.Z ρ.raft.ai0 + Lc.length := by
    have := uint_Z_nonneg ρ.raft.ai0
    exact uint_Z_W64 _ (by omega) hend
  ihave #Hc : committedAtLeast ρ.rd (W64 (uint.Z ρ.raft.ai0 + Lc.length)) $$ []
  · iapply committedAtLeast_of_rlog ρ.rd _ Lc (Int.le_of_eq hc)
    iexact HLc
  imod v3rpc.kvLogLb_nil (GF := GF) E.γs with #HF0
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn0
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave Hres := optsAt_res slice.nil [] iprop(True) $$ Hnil
  iunfold akKVOn at HKV
  icases HKV with ⟨-, #Hrange, -, -⟩
  iapply wp_fupd
  wp_apply (h_client_Get_on rcl rapi rconn addr s E ρ.rd cid mid
      (W64 (uint.Z ρ.raft.ai0 + Lc.length)) 0 ectx eom ecd go!"z/barrier" slice.nil []
      iprop(True) (fun _ => iprop(True)) []
      (opSizeOk_opGetModel (K := 16) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide)
        (by decide))) $$ [$Hlt Hres] as %resp %err ⟨Hlt, Hout⟩
  · iframe #
    isplitl []
    · itrivial
    rw [show (opGetModel go!"z/barrier" []).base.sortSet = false from rfl]
    isplitl []
    · unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    isplitl []
    · ipureintro; exact ⟨by simp [opGetPanics, opFold, OpFull.newOp, OpModel.zero], rfl⟩
    iintro !>
    ileft
    ipureintro; rfl
  icases Hout with ⟨-, (⟨%Herr, %m, #Hm, #Hok, %md, #Hmd, #Hauth⟩ | ⟨%Herr, -⟩)⟩
  · imod (akAuthFixed_barrier s E γa ρ γz hs Lset Lc r 0 _ _
      (rangeWireOf (opGetModel go!"z/barrier" [])) HEo rfl hc)
      $$ [Hrd Hfz HLs HLc Hauth] with ⟨%i, #Hfix⟩
    · iframe #; ipureintro; exact ⟨Hh, HLcst⟩
    (try wp_auto)
    wp_apply Hecancel
    subst Herr
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; rfl
    iexists i
    iexact Hfix
  · (try wp_auto)
    wp_apply Hecancel
    cases err with
    | nil => exact absurd rfl Herr.1
    | ok e =>
      (try wp_auto)
      iapply HΦ
      iframe Hlt
      ileft
      ipureintro; rfl

end proof

end etcd_auth3
end EtcdGrove
end Perennial
