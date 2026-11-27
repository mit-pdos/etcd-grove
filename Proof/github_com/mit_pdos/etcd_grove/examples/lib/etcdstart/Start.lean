/-
**`s.Start()` of a built member** (2026-10-22, D33). Lean-first (no Rocq counterpart).

`wp_Start_built`: `EtcdServer.Start.spec` at the auth slot's `off` (`isServerBuilt_offC`) at what `newServer` returns (`memberBuilt`) and the
thread token: the member started (`memberUp`). `srvServeBuilt`'s two `lgMu` reader slots and
the downgrade monitor's go to `Start`; (per-type stage B2) `NewServer`'s raw stocks
(`srvServeStock`) and the run pool's share of `Start`'s read-loop slots (`srvRunReadStock`) go to
`memberUp`. The step every example's member start took after
`NewServer` (putget's `Main`, putget3's and linkv3p's `startMember`), once; `StartServer` and
`StartMember` use it, with `Start`'s result as a hypothesis.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor

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
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) (m : lease.Mode := .none)
    (Hrb48 : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuilt s ρ E₀ lg γn id N sv (m := m) ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); memberUp s ρ E₀ lg γn id m }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuilt at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, -, #Hlr, Hkeep⟩
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlg1, Hlg2⟩
  -- `Start.spec` at the slot's `off`
  imod isServerBuilt_offC s γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) (W64 0) (W64 0) bootKV N $$ [Hsb Hkeep] with ⟨%hm, Hsb⟩
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
  wp_apply h' $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, -, Hgo, Hlg3, Hsr, -, Hright⟩
  · iframe; iframe #
    ipureintro; exact ⟨hm, Hrb48, HrbN, by trivial⟩
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

/-- `wp_Start_built` with the lessor at `γl` (F7 step 2): from `memberBuiltL`, `memberUpL`. -/
theorem wp_Start_builtL (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) (m : lease.Mode) (γl : GName)
    (Hrb48 : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuiltL s ρ E₀ lg γn id N sv m γl ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); memberUpL s ρ E₀ lg γn id m γl }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuiltL at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, -, #Hlr, Hkeep⟩
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlg1, Hlg2⟩
  -- `Start.spec` at the slot's `off`
  imod isServerBuilt_offC s γA ci TM E ρ ρ.rd (srvEr ρ E₀ (W64 0) (W64 0) bootKV id (srvTrKey γn γk) (srvTrStopK γk))
    γrn b (W64 0) (W64 0) (W64 0) bootKV N $$ [Hsb Hkeep] with ⟨%hm, Hsb⟩
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
  wp_apply h' $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, -, Hgo, Hlg3, Hsr, -, Hright⟩
  · iframe; iframe #
    ipureintro; exact ⟨hm, Hrb48, HrbN, by trivial⟩
  iunfold srvStartReaders at Hsr
  icases Hsr with ⟨Hrslots, -⟩
  -- (per-type stage B2) the run pool's share of the read loop's slots
  icases srvStartReaders_split s ρ.rd $$ Hrslots with ⟨Hrslots, Hrun⟩
  iapply HΦ
  iunfold memberUpL
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

/-! ## The auth-on chain with the lessor at `γl` (#50 F7 S2 step 4) -/

/-- **`memberBuiltL` with auth on, at the auth names `γa`** (#50 F7 S2 step 4): `memberBuiltL`'s body with
`E.authMode = .on γa` for `E.authOn = false`, the built part in the mode of the auth slot `AuthC.on γa`
(`isServerBuiltM (AuthC.on γa).isOn`, at the boot state `bootKVOf (AuthC.on γa).isOn`: the auth-on mode, as
`isServerBuiltM_C` takes it), and what `memberUpOnL` takes besides: the TLS fallback off and the auth store's
`Authenticate` side. `Start` turns it into `memberUpOnL` (`wp_Start_builtOnL`). -/
def memberBuiltOnL (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (N : Nat) (served : Bool) (γa : auth.AuthNames) (m : lease.Mode) (γl : GName) : IProp GF :=
  iprop(∃ (γA : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
      (γrn : RNNames GF) (b : GoInterface) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
      (γk : GName) (τ : SrvTr GF),
    ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
    srvServeStock s E ∗
    srvWatchBuilt s E ∗
    isServerBuiltM (AuthC.on γa).isOn s γA ci TM E ρ ρ.rd
      (srvErM (AuthC.on γa).isOn ρ E₀ (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) id (srvTrKey γn γk)
        (srvTrStopK γk))
      γrn b (W64 0) (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) N ∗
    srvServeBuilt s E cfg ∗ srvSVRes s E ∗ srvMonitorsOff s ∗ srvMonitorRes s ∗
    srvReadyCloser s E ∗ srvNetMember γn s id τ ∗ srvTrTok γn τ ∗
    memberPeerServeRes γn τ served ∗
    srvLeaseRd s E m ∗ srvStop.keep s cfg E γrn γk ∗
    □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD)

/-- **A member started with auth on, with the lessor at `γl`, from its parts** (`memberUpOn_intro`'s, for
`memberUpOnL`): its conjuncts, the views at the slot `AuthC.on γa`'s mode, and the lessor's name. -/
theorem memberUpOnL_intro (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc)
    (γn : NetNames GF) (id : w64) (γa : auth.AuthNames) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName) (m : lease.Mode) (γl : GName) :
    ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
        cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
      srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
      isServerReqM (AuthC.on γa).isOn s E { ρ with wait := γw } ∗ isServerReadM (AuthC.on γa).isOn s E ρ.rd ∗
      srvAuthLb s E ∗ srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
      srvGoRes s ∗ srvLgReader s ∗ srvBemuReader s ∗
      ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
      srvPeerCtl γn s id ∗ □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD ∗ srvLeaseRd s E m ⊢
    memberUpOnL (GF := GF) s ρ E₀ lg γn id γa m γl := by
  iintro ⟨%HEc, Hstk, Hrun, #Hreq, #Hrd, #Hlb, #Hwb, #Hsf, Hgo, Hlg3, Hbemu, Hrslots, Hctl, #Htls, #HBF, #Hlrd⟩
  iunfold memberUpOnL
  iexists E, cfg, γw
  isplitr; · ipureintro; exact HEc
  isplitl [Hstk]; · iexact Hstk
  isplitl [Hrun]; · iexact Hrun
  iframe Hreq Hrd Hlb Hwb Hsf Htls HBF Hlrd
  iframe

/-- `wp_Start_builtL` with auth on (#50 F7 S2 step 4): from `memberBuiltOnL`, `memberUpOnL` (`Start` at the auth
slot's `on γa`, as `StartMemberAuth`). -/
theorem wp_Start_builtOnL (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) (γa : auth.AuthNames) (m : lease.Mode) (γl : GName)
    (Hrb48 : receiptBound GF ≤ 2 ^ 48) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuiltOnL s ρ E₀ lg γn id N sv γa m γl ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); memberUpOnL s ρ E₀ lg γn id γa m γl }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuiltOnL at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, -, #Hlr, Hkeep, #Htls, #HBF⟩
  obtain ⟨hagree, hγa, hcl, hct, hcw, hγl⟩ := HE
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlg1, Hlg2⟩
  -- `Start.spec` at the slot's `on γa`: the built part as the slot's row
  have hB := isServerBuiltM_C (GF := GF) (.on γa) s γA ci TM E ρ ρ.rd
    (srvErM (AuthC.on γa).isOn ρ E₀ (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) id (srvTrKey γn γk)
      (srvTrStopK γk)) γrn b (W64 0) (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) N hγa
  ihave Hsb := hB $$ [Hsb Hkeep]
  · iframe Hsb
    iapply (srvStop.slot_intro (γk := γk)
      (Er := srvErM (AuthC.on γa).isOn ρ E₀ (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) id (srvTrKey γn γk)
        (srvTrStopK γk))
      (h := by rfl)) $$ Hkeep
  have h' := wp_Start s γA ci TM (.on γa) E ρ ρ.rd
    (srvErM (AuthC.on γa).isOn ρ E₀ (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) id (srvTrKey γn γk)
      (srvTrStopK γk)) γrn b (W64 0) (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) N
  -- the server's member id is the member's (`srvNetMember`'s)
  icases isServerBuiltC_mid (.on γa) s γA ci TM E ρ ρ.rd
    (srvErM (AuthC.on γa).isOn ρ E₀ (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) id (srvTrKey γn γk)
      (srvTrStopK γk)) γrn b (W64 0) (W64 0) (W64 0) (bootKVOf (AuthC.on γa).isOn) N $$ Hsb
    with ⟨Hsb, #HmidS, -⟩
  ihave #Hnm' := Hnm
  iunfold srvNetMember at Hnm'
  icases Hnm' with ⟨⟨%γdp, #Hpok⟩, -⟩
  iunfold srvProcOk at Hpok
  icases Hpok with ⟨%lp, %cp, %stp, %γrp, -, -, #Hmidp, -⟩
  icombine HmidS Hmidp gives %Hideq
  subst Hideq
  wp_apply h' $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%γw, #Hreq, #Hrd, #Hlb, Hgo, Hlg3, Hsr, -⟩
  · iframe; iframe #
    ipureintro; exact ⟨hγa, Hrb48, HrbN, by trivial⟩
  iunfold srvStartReaders at Hsr
  icases Hsr with ⟨Hrslots, -⟩
  icases srvStartReaders_split s ρ.rd $$ Hrslots with ⟨Hrslots, Hrun⟩
  iapply HΦ
  iapply memberUpOnL_intro _ _ _ _ _ _ _ E cfg γw m γl
  isplitr
  rotate_left
  · isplitl [Hstk]
    · iexact Hstk
    isplitl [Hrun]
    · iexact Hrun
    iframe Hreq Hrd Hlb Hwb Hsf Htls HBF Hlr
    iframe
    iunfold srvPeerCtl
    iexists τ
    iframe Hnm Htokp
  ipureintro; exact ⟨hagree, hγa, hcl, hct, hcw, hγl⟩

end proof

end etcdstart
end EtcdGrove
end Perennial
