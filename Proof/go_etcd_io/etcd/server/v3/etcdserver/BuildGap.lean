/-
**The server's construction: the raft environment and the residual** (unit N2 of the
server-construction unit; statements placed at stage N0, 2026-10-16; D13 and D13a-d,
`notes/decisions.md`). Lean-first (no Rocq counterpart). The statements are the interface
`NewServer`'s proof (unit N1) and the composition with `start` use; their proofs are unit N2's.

* `rnEnvOk_of_cluster`: the raft wrapper's discharge facts (`rnEnvOk`) of the server's raft
  environment `srvEr`, from the KV invariant (the committed logs' indices, `srvIdxOkW`), raft's
  committed log and the cluster's workload (`clusterWorkloadOk`, D13c): what `NewServer`'s raft
  installer takes at `srv.r.transport = tr`.
* `isServerBuilt_of_gap`: `NewServer`'s built part and the residual give `start`'s construction
  premise.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section gap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's raft environment meets the wrapper's discharge** (`rnEnvOk`), for wrapper
names `γw` over the server's raft names (raft's, the start log and index the server's), in the
static mode over the `MemoryStorage`, with the budget `bud`: the tick's resource and the read
registrations by `srvEr`'s definition, every message admitted, a committed log's `E.C` from the
KV invariant's indices (a committed log is a prefix of the KV invariant's, `srvIdxOkW`, and its
next index fits), the workload clause's `entriesOk` and `batchWaitOk`, and back from `srvC`. -/
theorem rnEnvOk_of_cluster (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (bud : BudgetNames) (γw : RNNames)
    (hraft : γw.node.raft = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    (hmode : γw.node.mode = RNMode.static) (hstor : γw.node.stor = memStorIface γw.ms)
    (hbud : γw.node.bud = bud) :
    kvInv (GF := GF) ρ.raft ρ.kv ∗ srvRaftLogInv ρ.raft ∗ clusterWorkloadOk ρ E c₀ x₀ ⊢
      rnEnvOk (srvEr ρ E ai₀ c₀ x₀ bud) γw := by
  iintro ⟨#Hkv, #Hr, #Hwl⟩
  unfold rnEnvOk srvEr
  simp only
  isplitr
  · ipureintro; rw [hbud]
  isplitr
  · ipureintro; exact ⟨hraft.symm, hpre.symm, hai⟩
  isplitr
  · ipureintro; exact ⟨hmode, hstor⟩
  isplitr
  · iintro !> %m %st -; ipureintro; trivial
  isplitr
  · iintro !> %L #HL %Hfit
    iunfold clusterWorkloadOk at Hwl
    icases Hwl $$ HL with ⟨%Hent, #Hbw⟩
    iunfold kvInv at Hkv
    iinv Hkv with >Hi Hclose
    icases Hi with ⟨%L', HL', Hσ, %Hok⟩
    imod srvRLog_lb ρ.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
      L' L $$ Hr HL' HL with ⟨HL', -, %Hp⟩
    imod Hclose $$ [HL' Hσ] with -
    · inext; iexists L'; iframe HL' Hσ; ipureintro; exact Hok
    imodintro
    imodintro
    unfold srvC
    iframe Hbw HL
    ipureintro
    refine ⟨?_, Hent⟩
    rw [← hai0]
    exact srvIdxOk_of_W _ _ (srvIdxOkW_prefix _ _ _ Hok.2.1 Hp) Hfit
  isplitr
  · iintro !> %L #HC
    unfold srvC
    icases HC with ⟨%Hc, -, #HL⟩
    iframe HL
    ipureintro
    rw [hai0]; exact Hc.1
  · ipureintro; trivial

/-- **`start`'s construction premise from `NewServer`'s built part and the residual**
(`srvBuilt`, `srvBuildGap`, `InvBuild.lean`): the rows the built part has without their KV parts
completed with the residual's (the uber-applier's field and contracts into `#Hfb` and `Happ`,
`srv.kv` and its read view and `storeSmall` into `#Hrdb`), and the residual's other rows. -/
theorem isServerBuilt_of_gap (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuilt s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ ∗ srvBuildGap s E ρ ai₀ at₀ x₀ N ⊢
      isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  unfold srvBuilt srvBuildGap isServerBuilt
  iintro ⟨⟨#Hci, ⟨%v, #Hfb⟩, #Hreqb, ⟨%vr, #Hrdb⟩, #Hrunb, #Hsab, #Hai, #Hkvi, #Hti, #Hci',
      #Hrn, %HEr, %Hρrd, Hloop, Happly, Hrdone, #Hcci, #Hwci, Hw, Haw, Hdone, Hstop, Hstopping,
      Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr⟩,
    ⟨⟨%ua, #Hua, #Hfor, Hakv⟩, ⟨%kv, %rv, #Hkv, #HisKV, #Hrv, #HisRV⟩, #Hsmall, HWB, Hsnap,
      #HNR, #Hcv, %Hbound⟩⟩
  iframe Hci Hreqb Hrunb Hsab Hai Hkvi Hti Hci' Hrn HNR Hcv Hcci Hwci
  iframe Hloop Happly Hrdone Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg
  iframe HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hsnap
  isplitr
  · unfold srvFieldsBuiltNA
    iexists { v with ua := ua }
    unfold srvFieldsBuilt
    iframe Hua Hfor Hfb
  isplitr
  · unfold srvReadBuiltNK
    iexists { vr with kv := kv, rv := rv }
    unfold srvReadBuilt
    iframe Hkv HisKV Hrv HisRV Hsmall Hrdb
  isplitr
  · ipureintro; exact HEr
  isplitr
  · ipureintro; exact Hρrd
  isplitr
  · ipureintro; exact Hbound
  unfold applyBuiltNA applyBuilt
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hra, Hao, Hal, Hkr, Hfs⟩
  iexists st₀, a, t, f
  iframe Hth Hbe Hca Hlg Hbm Hra Hao Hal Hkr Hfs
  isplitr
  · ipureintro; exact Hok
  iexists ua
  iframe Hua Hakv

end gap

end EtcdGrove
end Perennial
