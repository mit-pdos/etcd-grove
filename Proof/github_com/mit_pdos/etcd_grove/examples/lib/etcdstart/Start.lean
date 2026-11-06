/-
**`s.Start()` of a built member** (2026-10-22, D33). Lean-first (no Rocq counterpart).

`wp_Start_built`: `EtcdServer.Start.spec` at the auth slot's `off` (`isServerBuilt_offC`) at what `newServer` returns (`memberBuilt`) and the
thread token: the member started (`memberUp`). Two of `srvServeBuilt`'s `lgMu` reader slots and
the downgrade monitor's go to `Start`. The step every example's member start took after
`NewServer` (putget's `Main`, putget3's and linkv3p's `startMember`), once; `StartServer` and
`StartMember` use it, with `Start`'s result as a hypothesis.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs

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
theorem wp_Start_built (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) (m : lease.Mode := .none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuilt s ρ E₀ lg γn id N sv (m := m) ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); memberUp s ρ E₀ lg γn id m }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuilt at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, -, HWR, #Hlr, Hkeep⟩
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  -- `Start.spec` at the slot's `off`
  imod isServerBuilt_offC s γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) (W64 0) (W64 0) bootKV N $$ [Hsb Hkeep] with ⟨%hm, Hsb, Hl⟩
  · iframe Hsb
    iapply (srvStop.slot_intro s cfg E γrn γk
      (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk)) rfl) $$ Hkeep
  have h' := wp_Start s γA ci TM .off E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) (W64 0) (W64 0) bootKV N
  simp only [AuthC.isOn, isServerReqM_false, isServerReadM_false] at h'
  -- the server's member id is the member's (`srvNetMember`'s)
  icases isServerBuiltC_mid .off s γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) (W64 0) (W64 0) bootKV N $$ Hsb with ⟨Hsb, #HmidS, -⟩
  ihave #Hnm' := Hnm
  iunfold srvNetMember at Hnm'
  icases Hnm' with ⟨⟨%γdp, #Hpok⟩, -⟩
  iunfold srvProcOk at Hpok
  icases Hpok with ⟨%lp, %cp, %stp, %γrp, -, -, #Hmidp, -⟩
  icombine HmidS Hmidp gives %Hideq
  subst Hideq
  wp_apply h' $$ [Hsb Hl Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, -, Hgo, Hlg3, Hsr, -, Hright⟩
  · iframe; iframe #
    ipureintro; exact ⟨hm, trivial, HrbN, by trivial⟩
  iunfold srvStartReaders at Hsr
  icases Hsr with ⟨Hrslots, -⟩
  iapply HΦ
  iunfold memberUp
  iexists E, cfg, γw
  iframe
  iframe #
  isplitr
  · ipureintro; exact HE
  iunfold srvPeerCtl
  iexists τ
  iframe Hnm Htokp

end proof

end etcdstart
end EtcdGrove
end Perennial
