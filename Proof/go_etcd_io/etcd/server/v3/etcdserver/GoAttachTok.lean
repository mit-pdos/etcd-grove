/-
**`GoAttach` with a whole thread token** (revoke-open Q4 (i), 2026-11-06;
`notes/revoke-open-plan.md`, "Draft pass 1", D.4). Lean-first.

`GoAttach.spec` takes one level of a thread token (`levelTok 1`) and runs its closure on
`threadTokFrom 1`; the callers that hold a whole token (`Start`, `sendMergedSnap`, v3rpc's
`monitorLeader`) apply this lemma, today's triple: the token split `levelTok 0 ∗ levelTok 1 ∗
threadTokFrom 2`, level 1 lent, the rest framed, `threadTokFrom 1` framed through `f`. One spec of
`GoAttach`, one lemma about it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`GoAttach` with a whole thread token** (see the file header): today's triple, from
`GoAttach.spec`. (Review round 1, NIT 3.1, 2026-11-06: no `srvLgReader s`, which until then it took
and returned untouched.) -/
theorem wp_GoAttach_tok (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : GoNames) (f : GoFunc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvGoResAt s γ ∗ P ∗
        {{ P ∗ goRunning γ }} (App (Val #f) (Val #())) {{ RET #(); goRunning γ }} }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
    {{ RET #(); srvGoResAt s γ }} := by
  iintro %Φ ⟨#Hinit, Hgr, HP, #Hf⟩ HΦ
  iunfold srvGoResAt at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨H0, Ht1⟩
  icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Ht1 with ⟨H1, H2⟩
  iapply hGA s γ f P $$ [Hwr H1 HP] [HΦ H0 H2]
  · iframe Hinit Hwr H1 HP
    imodintro
    iintro %Ψ ⟨HP, Hrun, Hfr⟩ HΨ
    iapply Hf $$ [HP Hrun] [HΨ Hfr]
    · iframe
    inext
    iintro Hrun
    iapply HΨ
    iframe
  inext
  iintro ⟨Hwr, H1⟩
  iapply HΦ
  iunfold srvGoResAt
  iframe Hwr
  iapply (threadTok_level0 (GF := GF)).2
  iframe H0
  iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
  iframe

end lemmas

end EtcdGrove
end Perennial
