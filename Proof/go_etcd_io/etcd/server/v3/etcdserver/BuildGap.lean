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
* `clusterWorkloadOk_of` (D19c, 2026-10-18): the workload clause from the KV invariant's workload
  facts (`kvWork`) and the reserved id `0` (`idNoZero`) (until D19c's move, also the residual
  size bound `clusterLogBound`, gone: the apply thread checks the size clauses at execution).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBuild
public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Lemmas

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

/-- **The workload facts' claims give a batch's ids** (D19c): every entry of a committed log of
good shapes whose ids are claimed meets `entryWaitOk` (a normal entry's request's id claimed for
its data; a conf change's id `0`, which no request claims). -/
theorem batchWaitOk_of_work (ρ : ReqNames) (E : apply.AEnv GF) (L : List EntryModel)
    (hs : logShape L) (hcl : ccLogOk ρ.raft.raft.reCfg L) :
    ⊢ ([∗list] m ∈ L, entryClaim ρ.ids m) -∗ idNoZero ρ.ids -∗ srvRLogLb ρ.raft L -∗
      batchWaitOk ρ E L := by
  iintro #Hcl #HNZ #HL
  iunfold batchWaitOk
  iintro !> %m %hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ m => entryClaim (GF := GF) ρ.ids m) hn) $$ Hcl
  have hsh := hs m hm
  unfold entryWaitOk
  split
  · rename_i ht
    isplitr
    · iintro %rq %id %hrq
      obtain ⟨hd, hdec, hid⟩ := hrq
      iunfold entryClaim at Hc
      icases Hc with (%hc | ⟨%rq', %id', %γf, %hrq', #Hcl'⟩)
      · exfalso; rcases hc with hc | hc
        · exact hc ht
        · exact hd hc
      · obtain ⟨hdec', hid'⟩ := hrq'
        rw [hdec] at hdec'
        cases hdec'
        rw [hid] at hid'
        cases hid'
        iexists γf
        iexact Hcl'
    · iexists L
      iframe HL
      ipureintro; exact hm
  · rename_i ht
    have h0 := hsh.2 ht
    rw [h0]
    isplitr
    rotate_left
    · ipureintro; exact hcl m hm ht
    iintro !> %Ψ HR
    iunfold reqWaitR at HR
    icases HR with ⟨%d, %rq, %γf, %F, #Hc0, -, -⟩
    iapply idClaim_noZero ρ.ids d γf $$ HNZ Hc0

/-- **The workload clause, proved** (D19c, 2026-10-18; until then a premise of `NewServer.spec`):
a committed log is a prefix of the KV invariant's, whose entries have good shapes and claimed ids
(`kvWork`); with the reserved id `0` the claims give the ids (`batchWaitOk_of_work`). -/
theorem clusterWorkloadOk_of (ρ : ReqNames) (E : apply.AEnv GF) :
    kvInv (GF := GF) ρ.raft ρ.kv ∗ srvRaftLogInv ρ.raft ∗ idNoZero ρ.ids ⊢
      clusterWorkloadOk ρ E := by
  iintro ⟨#Hkv, #Hr, #HNZ⟩
  iunfold clusterWorkloadOk
  iintro !> %L #HL
  iunfold kvInv at Hkv
  iinv Hkv with >Hi Hclose
  icases Hi with ⟨%L', HL', Hσ, %Hok, #Hw⟩
  imod srvRLog_lb ρ.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L' L $$ Hr HL' HL with ⟨HL', -, %Hp⟩
  imod Hclose $$ [HL' Hσ] with -
  · inext; iexists L'; iframe HL' Hσ Hw; ipureintro; exact Hok
  iunfold kvWork at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  obtain ⟨Hsh, Hccl⟩ := Hsh
  obtain ⟨R, rfl⟩ := Hp
  rw [logShape_append] at Hsh
  icases BigSepL.bigSepL_append.1 $$ Hcl with ⟨#HclL, -⟩
  imodintro
  isplitr
  · ipureintro; exact Hsh.1
  iapply batchWaitOk_of_work ρ E L Hsh.1 (fun m hm => Hccl m (List.mem_append_left _ hm))
    $$ HclL HNZ HL

/-- **The server's raft environment meets the wrapper's discharge** (`rnEnvOk`), for wrapper
names `γw` over the server's raft names (raft's, the start log and index the server's), in the
static mode over the `MemoryStorage`, with the budget `bud`: the tick's resource and the read
registrations by `srvEr`'s definition, every message but a snapshot admitted (D19p: a one-member cluster), with
its bundle (`srvMsgNet`, D21 stage M1), a committed log's `E.C` from the
KV invariant's indices (a committed log is a prefix of the KV invariant's, `srvIdxOkW`, and its
next index fits), the workload clause's `logShape` and `batchWaitOk`, and back from `srvC`. -/
theorem rnEnvOk_of_cluster (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (bud : BudgetNames) (γw : RNNames)
    (hraft : γw.node.raft = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    (hmode : γw.node.mode = RNMode.static) (hstor : γw.node.stor = memStorIface γw.ms)
    (hbud : γw.node.bud = bud)
    -- (D19p, 2026-10-18) a one-member cluster: raft's tracked bound one node
    (k : w64) (htrk : ρ.raft.raft.reTracked = some (GMap.listToSet [k])) :
    kvInv (GF := GF) ρ.raft ρ.kv ∗ srvRaftLogInv ρ.raft ∗ clusterWorkloadOk ρ E ⊢
      rnEnvOk (srvEr ρ E ai₀ c₀ x₀ bud) γw := by
  iintro ⟨#Hkv, #Hr, #Hwl⟩
  unfold rnEnvOk srvEr
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · ipureintro; exact ⟨hraft.symm, hpre.symm, hai⟩
  isplitr
  · ipureintro; exact ⟨hmode, hstor⟩
  isplitr
  · iintro !> %m %st ⟨#Hmo, #Hrm, #Htl, Hc⟩
    rw [hraft, hbud] at *
    isplitl [Hc]
    · -- (D21 stage M1) the bundle a receiver's `Step` takes
      iunfold srvMsgNet
      iexists st
      iframe Hmo Hrm Htl Hc
    iunfold srvMsgNoSnap
    iexists st
    iframe Hmo
    iapply isRaftMsg_not_snap ρ.raft.raft k htrk st $$ Hrm
  isplitr
  · iintro !> %L #HL %Hfit
    iunfold clusterWorkloadOk at Hwl
    imod Hwl $$ HL with ⟨%Hent, #Hbw⟩
    iunfold kvInv at Hkv
    iinv Hkv with >Hi Hclose
    icases Hi with ⟨%L', HL', Hσ, %Hok, #Hw⟩
    imod srvRLog_lb ρ.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
      L' L $$ Hr HL' HL with ⟨HL', -, %Hp⟩
    imod Hclose $$ [HL' Hσ] with -
    · inext; iexists L'; iframe HL' Hσ Hw; ipureintro; exact Hok
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
completed with its own (the uber-applier's field and contracts into `#Hfb` and `Happ`, `srv.kv`
and its read view and `storeSmall` into `#Hrdb`), and the residual's snapshot contract. -/
theorem isServerBuilt_of_gap (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuilt s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N ∗ srvBuildGap s γn ai₀ at₀ ⊢
      isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  unfold srvBuilt srvBuildGap isServerBuilt
  iintro ⟨⟨#Hci, ⟨%v, #Hfb⟩, #Hreqb, ⟨%vr, #Hrdb⟩, #Hrunb, #Hsab, #Hai, #Hkvi, #Hti, #Hci',
      #Hrn, %HEr, %Hρrd, Hloop, Happly, Hrdone, #Hcci, #Hwci, Hw, Haw, Hdone, Hstop, Hstopping,
      Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr,
      ⟨%kv, %rv, #Hkv, #HisKV, #Hrv, #HisRV⟩, HWB, #Hsmall, #HNR, #Hcv, %Hbound,
      ⟨%ua, #Hua, #Hfor, Hakv⟩⟩, Hsnap⟩
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
