/-
**`s.Start()` of a member that may be stopped and restarted** (the restart plan's R2a, 2026-11-02;
DRAFT callee: `EtcdServer.Start.specStop`). Lean-first (no Rocq counterpart).

`wp_Start_builtStop`: `wp_Start_built`'s (`Start.lean`) over `Start.specStop`, which also returns
`srvStartRet s` (what `HardStop` takes). `wp_Start_builtR`: the same from a restart's built member
(`memberBuiltR`, at its image's starting index).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Restart
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
theorem wp_Start_builtStop (wp_Start : EtcdServer.Start.specStop (GF := GF) (hG := hG))
    (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuilt s ρ E₀ lg γn id N sv ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); ⌜srvStartRet s⌝ ∗ memberUp s ρ E₀ lg γn id }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuilt at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, -, HWR⟩
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  wp_apply (wp_Start s γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV N HrbN)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%Hret, %γw, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  iapply HΦ
  isplitr
  · ipureintro; exact Hret
  iunfold memberUp
  iexists E, cfg, γw
  iframe
  iframe #
  isplitr
  · ipureintro; exact HE
  iunfold srvPeerCtl
  iexists τ
  iframe Hnm Htokp

/-- See the file header. -/
theorem wp_Start_builtR (wp_Start : EtcdServer.Start.specStop (GF := GF) (hG := hG))
    (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF) (id : w64)
    (N : Nat) (sv : Bool) (HrbN : receiptBound GF ≤ N + 1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        memberBuiltR s ρ E₀ lg γn id N sv ∗ threadTok }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Start")) (Val #()))
    {{ RET #(); ⌜srvStartRet s⌝ ∗ memberUp s ρ E₀ lg γn id }} := by
  iintro %Φ ⟨#Psrv, Hmb, Htok⟩ HΦ
  iunfold memberBuiltR at Hmb
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %ai₀, %at₀, %c₀, %x₀, %HE, #Hwb,
    Hsb, Hserve, Hsv, #Hoff, Hlgm, Hrc, #Hnm, Htokp, -, HWR⟩
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  wp_apply (wp_Start s γA ci TM E ρ ρ.rd _ γrn b ai₀ at₀ c₀ x₀ N HrbN)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm Hrc] as ⟨%Hret, %γw, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  iapply HΦ
  isplitr
  · ipureintro; exact Hret
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

end common
end EtcdGrove
end Perennial
