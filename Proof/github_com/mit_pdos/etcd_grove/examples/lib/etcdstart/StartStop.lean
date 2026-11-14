/-
**`s.Start()` of a restarted member** (the restart plan's R2a and R2b-2, 2026-11-02; restart S7.2',
2026-11-14: proved). Lean-first (no Rocq counterpart).

`wp_Start_builtR`: `EtcdServer.Start.spec` at a restarted member's built state (`memberBuiltR`) and
the thread token: the member started (`memberUp`), as `wp_Start_built` (`Start.lean`) at a first
start's. `NewServer.specR` builds the restart at `ai₀ = c₀ = 0` (the restart point is the raft
wrapper's `γn.a0`), so `Start.spec`'s premise `ai₀ = W64 0` holds, and its construction premise is
`srvBuiltR_C` of the restart's built part with the stop's slot from `srvStop.keep`
(`notes/restart-s7-probe.md`, P3). (Until S7.2' the statement `Start_builtR_spec`, a hypothesis of the
restart's proofs, on the belief that `Start.spec` needed a restart index: deleted.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Restart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
theorem wp_Start_builtR (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) (Hrb48 : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuiltR s ρ E₀ lg γn id N sv ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); memberUp s ρ E₀ lg γn id }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuiltR at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %at₀, %A, %HE, Hstk, #Hwb, Hsb,
    Hserve, Hsv, #Hoff, Hlgm, Hrc, #Hnm, Htokp, -, #Hlr, Hkeep⟩
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlg1, Hlg2⟩
  -- `Start.spec`'s construction premise: the restart's built part and the stop's slot
  ihave Hsb := srvBuiltR_C s γA ci TM E ρ ρ.rd
    (srvEr ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) at₀ (W64 0) (restartKV ρ.rd.kv A) N $$ [Hsb Hkeep]
  · iframe Hsb
    iapply (srvStop.slot_intro s cfg E γrn γk
      (srvEr ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk) (srvTrStopK γk))
      rfl) $$ Hkeep
  have h' := wp_Start s γA ci TM .off E ρ ρ.rd
    (srvEr ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) at₀ (W64 0) (restartKV ρ.rd.kv A) N
  simp only [AuthC.isOn, isServerReqM_false, isServerReadM_false] at h'
  -- the server's member id is the member's (`srvNetMember`'s)
  icases isServerBuiltC_mid .off s γA ci TM E ρ ρ.rd
    (srvEr ρ E₀ (W64 0) (W64 0) (restartKV ρ.rd.kv A) id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) at₀ (W64 0) (restartKV ρ.rd.kv A) N $$ Hsb with ⟨Hsb, #HmidS, -⟩
  ihave #Hnm' := Hnm
  iunfold srvNetMember at Hnm'
  icases Hnm' with ⟨⟨%γdp, #Hpok⟩, -⟩
  iunfold srvProcOk at Hpok
  icases Hpok with ⟨%lp, %cp, %stp, %γrp, -, -, #Hmidp, -⟩
  icombine HmidS Hmidp gives %Hideq
  subst Hideq
  have hm : E.authMode = AuthC.off.mode := authMode_off_of E HE.2.1
  wp_apply h' $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, -, Hgo, Hlg3, Hsr, -, Hright⟩
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨hm, Hrb48, HrbN, by trivial⟩
    iapply acLessor_off
  iunfold srvStartReaders at Hsr
  icases Hsr with ⟨Hrslots, -⟩
  -- (per-type stage B2) the run pool's share of the read loop's slots
  icases srvStartReaders_split s ρ.rd $$ Hrslots with ⟨Hrslots, Hrun⟩
  iapply HΦ
  iunfold memberUp
  iexists E, cfg, γw
  -- (the raw run-pool stocks first, framed explicitly: no bare `iframe` meets their
  -- `srvRevokePoolN`-long lists)
  isplitr
  · ipureintro; exact HE
  isplitl [Hstk]
  · iexact Hstk
  isplitl [Hrun]
  · iexact Hrun
  iframe
  iframe #
  iunfold srvPeerCtl
  iexists τ
  iframe Hnm Htokp

end proof

end etcdstart
end EtcdGrove
end Perennial
