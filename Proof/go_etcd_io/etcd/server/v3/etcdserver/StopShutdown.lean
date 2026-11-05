/-
**`run`'s deferred shutdown: the apply thread's resources at the stop, `Cleanup` and the image**
(the restart plan's R2b-3d stage 5c/5d, 2026-11-05; `notes/restart-plan.md`, "R2b-3d stage 5").
Lean-first (no Rocq counterpart).

`run.specStop`'s proof (`EtcdServer__run.lean`, `wp_proofG` at `stp = true`) runs the deferred
shutdown: `close(stopping)` under `wgMu`, `cancel()`, `sched.Stop()` (the apply thread's resources
at the handed log `A` back, `applyResC`), `s.wg.Wait()`, `s.r.stop()` (`raftNode.stop.specStop`),
`s.Cleanup()`, `close(done)` with the image escrowed. This file has the two steps that are about the
apply thread's resources rather than the control flow:
* `stop_split`: what `raftNode.stop` takes out of `applyResC` (the WAL's apply half, the live
  transport for `Er.ST`), the rest kept as `applyResStop`;
* `stop_cleanup_image`: `s.Cleanup()` from the rest, the stop's slot (`srvShutdownPre`) and what
  `raftNode.stop` returned, giving the stopped member's image (`srvDiskImage`): `Cleanup`'s
  precondition by gap 4's census (every store reader retired, the backend's whole open token) and
  the stop commit's request (`commitReq_freeze`), then the image from `Cleanup`'s post
  (`StopImage.stop_mergedObs`, `merged_imageAt`, `RestConf.restModel_confState`, `srvFiles`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestConf
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cleanup
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The close of a stop channel at its internal names** (`wp_stop_chan_close` with the closer's
half of the flag and the channel's names given, not existential: the shutdown closes `s.stopping`
from `wgMu`'s resource, `stopPart`, and gives the lock back the flag discarded, at the same names). -/
theorem wp_stop_chan_close_at {ty : go.GoType} {dir : go.ChanDir}
    [ty ↓u go.ChannelType dir (go.StructType [])] (ch : GoChan) (γch : ChanNames)
    (γi : BroadcastInternalNames) (Q : IProp GF) :
    {{ isStopChanInternal ch γch γi Q ∗ dghostVar γi.doneGn (.own (1 : Qp).half) false ∗ □ Q }}
      (App (Val #(functions go.close [ty])) (Val #ch))
    {{ RET #(); dghostVar γi.doneGn .discard true }} := by
  iintro %Φ ⟨#Hint, Hown, #HQ⟩ HΦ
  ihave #Hint' := Hint
  unfold isStopChanInternal
  icases Hint' with ⟨#His_ch, #Hinv⟩
  iapply chan.wp_close (ct := ty) (V := Unit) ch γch $$ His_ch
  iintro _
  unfold closeAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopChanInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.nil =>
    iintro Hch
    imod Hmask with -
    imod dghostVar_update_halves true _ _ _ $$ Hown Hs with ⟨Hown, -⟩
    imod dghostVar_persist _ _ _ $$ Hown with #Hown
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hown
    imodintro
    iapply HΦ
    iexact Hown
  case Closed.nil =>
    icases Hs with ⟨-, #Hs⟩
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  all_goals first | itrivial | (iexfalso; iexact Hs)

/-- **The apply thread's resources at the stop, but what `raftNode.stop` takes**: `applyResC`'s
without the WAL's apply half (`rnWalTokA`) and the membership resource (`srvApRes`, whose live
transport goes to `Er.ST`, `srvApRes_trStop`; the rest is not needed by the shutdown). -/
def applyResStop (K : AuthC) (C : ApplyCtx GF) (A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV)
      (sa : auth.AuthState),
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServerC K C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗ epCsAt C.ρ.raft A cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ srvApplyKVC K C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr ai ∗ appliedLogAt C.γr ai x.log ∗ kvRunM K.isOn C.γr C.ai₀ C.c₀ A x sa ∗
    srvRest B.E C.γr A ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv B.E.s B.E.γ) ∗
    (∃ w : Nat, srvWTTaken C.wt w) ∗ acTok K (ciEff B.γ st.k) ∗
    srvSnapOwn C.s C.ci B.E C.γr B.γ ai ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff B.γ st.k) C.c₀ ai ∧
      uint.Z ai ≤ uint.Z (ciEff B.γ st.k) ∧
      lastTermIs A at'⌝)

/-- **What `raftNode.stop` takes of the apply thread's resources**: the WAL's apply half and the live
transport (for `Er.ST`, `srvStop.raft_stop`). -/
theorem stop_split (K : AuthC) (C : ApplyCtx GF) (A : List EntryModel) :
    applyResC K C A ⊢
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ srvTrStop C.s ∗ applyResStop K C A := by
  unfold applyResC applyResStop
  iintro ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %hB, H1, H2, H3, H4, H5, H6, H7, H8, H9,
    H10, H11, H12, H13, H14, H15, H16, H17, Hap, H18, Hwt, H19, H20, H21, %hp⟩
  iframe Hwt
  isplitl [Hap]
  · iapply srvApRes_trStop $$ Hap
  iexists B, st, ai, at', a, t, cs, x, sa
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21
  ipureintro; exact ⟨hB, hp⟩

/-- **`s.Cleanup()` at the stop, and the image** (see the file header): from the apply thread's
resources at the handed log `A` (`applyResStop`), the stop's slot but its raft part, the data
directory and the caller's unused serving readers (`srvShutdownPre`'s), the stop request's evidence
(`srvBootApplied`), and what `raftNode.stop` returned (`raftNode.stop.specStop`'s post), the
member's image at the stopped incarnation's names. Scope (`run.specStop`'s): a first start
(`ai₀ = 0`, `pre = []`), auth off, no compactor. -/
theorem stop_cleanup_image (hCl : EtcdServer.Cleanup.spec (GF := GF) (hG := hG))
    (K : AuthC) (C : ApplyCtx GF) (A : List EntryModel) (Er : RNEnv GF)
    (γg : GoNames) (γcx : context.ContextNames) (v : RunFields) (SP : IProp GF)
    (TM : MetaCI → IProp GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (dd : GoString)
    (hM : C.E.authMode = K.mode) (hoff : C.E.authOn = false)
    (hcp : v.compactor = GoInterface.nil)
    (hEr : Er.C = srvCM K.isOn C.ρ C.E C.ai₀ C.c₀ C.x₀ ∧ Er.γr = C.γr ∧
      (uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧ C.rn.pre = [] ∧ C.ai₀ = W64 0))
    (hdisk : storage.diskOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerC K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
        isRaftNode Er C.rn (srvRAddr C.s) ∗
        srvRunFieldsAt C.s C.γr γg γcx v SP ∗
        applyResStop K C A ∗
        srvStop.cleanupPart C.s C.E ∗ srvStop.censusPart C.s C.E ∗ srvStop.imagePart C.s cfg C.rn ∗
        srvDataDir C.s dd ∗ ([∗list] _x ∈ List.replicate (64 + 64) (), mvcc.storeReader C.E.s C.E.γ) ∗
        srvBootApplied C.ρ ∗
        nodeVacant C.rn.node.cl C.rn.id ∗
        (∃ (S : RaftState) (σ : StorContents), raftState C.rn.node.cl C.rn.id S ∗
          rnWalClosed C.rn (srvRAddr C.s) σ ∗
          ⌜StorageHolds S σ ∧ σ.b ≤ (C.rn.pre ++ A).length ∧
            (C.rn.pre ++ A).length ≤ σ.commit⌝) }}
      (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
    {{ RET #(); srvDiskImage C.ρ.rd.raft.raft C.ρ C.rn.id dd }} := by
  sorry

end proof

end EtcdGrove
end Perennial
