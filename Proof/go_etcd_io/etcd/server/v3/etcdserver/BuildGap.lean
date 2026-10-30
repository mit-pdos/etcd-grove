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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The workload facts' claims give a batch's ids** (D19c): every entry of a committed log of
good shapes whose ids are claimed meets `entryWaitOk` (a normal entry's request's id claimed for
its data; a conf change's id `0`, which no request claims). -/
theorem batchWaitOk_of_work (ρ : ReqNames) (E : apply.AEnv GF) (L : List EntryModel)
    (hs : logShape L) (hcl : ccLogOk ρ.raft.raft L) :
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
      icases Hc with (%hc | ⟨%rq', %id', %γf, %hrq', #Hcl', #Hreg⟩)
      · exfalso; rcases hc with hc | hc
        · exact hc ht
        · exact hd hc
      · obtain ⟨hdec', hid'⟩ := hrq'
        rw [hdec] at hdec'
        cases hdec'
        rw [hid] at hid'
        cases hid'
        iframe Hreg
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

/-- **The claims of a committed log** (2026-10-27): those of the server's log of requested
entries, every entry of a committed log `A` being a filler (which claims nothing) or of the same
type and data as one of the server's log. -/
theorem entryClaims_transfer (γi : IdNames) (ai₀ : w64) (A L : List EntryModel)
    (hA : srvIdxOkW ai₀ A) (h : opsOf (A.map EntryModel.toLE) <+: L.map EntryModel.toLE) :
    ([∗list] m ∈ L, entryClaim (GF := GF) γi m) ⊢ [∗list] m ∈ A, entryClaim γi m := by
  have key : ∀ (k : Nat) (m : EntryModel), A[k]? = some m →
      iprop(□ [∗list] m ∈ L, entryClaim (GF := GF) γi m) ⊢ entryClaim γi m := by
    intro k m hk
    rcases srv_entry_src ai₀ A L hA h m (List.mem_of_getElem? hk) with ⟨ht, hd⟩ | ⟨m', hm', he⟩
    · iintro -
      iunfold entryClaim
      ileft; ipureintro; exact .inr hd
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hm'
      have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      iintro #HL
      ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ m => entryClaim (GF := GF) γi m) hj) $$ HL
      unfold entryClaim
      rw [← h1, ← h2]
      iexact Hc
  iintro #HL
  iapply (BigSepL.bigSepL_intro (Φ := fun _ m => entryClaim (GF := GF) γi m) key)
  imodintro
  iexact HL

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
    L' L $$ Hr HL' HL with ⟨HL', %Hp⟩
  ihave %HLi := srvRLogLb_idx ρ.raft L $$ HL
  imod Hclose $$ [HL' Hσ] with -
  · inext; iexists L'; iframe HL' Hσ Hw; ipureintro; exact Hok
  iunfold kvWork at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  obtain ⟨Hsh, Hccl⟩ := Hsh
  -- (2026-10-27) the committed log's entries are the server's log's or fillers
  have hshL : logShape L := by
    intro m hm
    rcases srv_entry_src _ L L' HLi Hp.2.2 m hm with ⟨ht, hd⟩ | ⟨m', hm', he⟩
    · exact ⟨fun _ => .inl hd, fun h => absurd ht h⟩
    · have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      have := Hsh m' hm'
      unfold entryShape at this ⊢
      rw [← h1, ← h2]; exact this
  have hcclL : ccLogOk ρ.raft.raft L := by
    intro m hm
    rcases srv_entry_src _ L L' HLi Hp.2.2 m hm with ⟨ht, hd⟩ | ⟨m', hm', he⟩
    · intro h; exact absurd ht h
    · have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      rw [← h1, ← h2]; exact Hccl m' hm'
  ihave #HclL := entryClaims_transfer ρ.ids _ L L' HLi Hp.2.2 $$ Hcl
  imodintro
  isplitr
  · ipureintro; exact hshL
  iapply batchWaitOk_of_work ρ E L hshL hcclL $$ HclL HNZ HL

/-- **The server's raft environment meets the wrapper's discharge** (`rnEnvOk`), for wrapper
names `γw` over the server's raft names (the cluster the server's, the start log and index the
server's), in a dynamic cluster at the server's decoder, the storage's cap at least `1`: the tick's
resource and the read registrations by `srvEr`'s definition, every message the node sends
admitted with its bundle (`srvMsgNet`, D21 stage M1) and no snapshot (`srv_sentMsg_notSnap`), a
committed log's `E.C` from the KV invariant's indices (a committed log's requested entries are a
prefix of the KV invariant's, whose indices its own are, `srvRLogLb_idx`, and its next index fits),
the workload clause's `logShape` and `batchWaitOk`, and back from `srvC`. (2026-10-27: over the node
API; no budget names, no raft modes.) -/
theorem rnEnvOk_of_cluster (ρ : ReqNames) (E : apply.AEnv GF) (ai₀ c₀ : w64)
    (x₀ : apply.ApplyKV) (γw : RNNames)
    (hraft : γw.node = ρ.raft.raft) (hpre : γw.pre = ρ.raft.pre)
    (hai : uint.Z ρ.raft.ai0 = γw.pre.length) (hai0 : ρ.raft.ai0 = ai₀)
    -- (D43 M3, 2026-10-25) in a dynamic cluster at the server's decoder
    (hdec : γw.node.dyn = true → γw.node.dec = srvDec ρ.rd.kv.c0 γw.node.boot)
    -- (D21 M3) the storage's cap at least `1`
    (hcap : 1 ≤ γw.γs.cap)
    -- (2026-10-24, rafthttp stage 6d) the member's id, its messages' sender, and the transport's
    -- `Send`'s borrow
    (id : w64) (S : IProp GF) (hid : γw.id = id) :
    kvInv (GF := GF) ρ.raft ρ.kv ∗ srvRaftLogInv ρ.raft ∗ clusterWorkloadOk ρ E ⊢
      rnEnvOk (srvEr ρ E ai₀ c₀ x₀ id S) γw := by
  iintro ⟨#Hkv, #Hr, #Hwl⟩
  unfold rnEnvOk srvEr
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · ipureintro; exact ⟨hraft.symm, hpre.symm, hai⟩
  isplitr
  · ipureintro; exact hdec
  isplitr
  · ipureintro; exact hcap
  isplitr
  · iexact Hr
  isplitr
  · iintro !> %m %st ⟨#Hmo, #Hrm, Hc⟩
    ihave #Hcl : srvClusterOk ρ.raft $$ []
    · iunfold srvRaftLogInv at Hr; icases Hr with ⟨-, #H, -⟩; iexact H
    rw [hraft, hid] at *
    ihave %Hns := srv_sentMsg_notSnap ρ.raft id st $$ [Hcl Hrm]
    · iframe Hcl Hrm
    isplitl [Hc]
    · -- (D21 stage M1) the bundle a receiver's `Step` takes
      iunfold srvMsgNet
      iexists st
      iframe Hmo Hrm Hc
    iunfold srvMsgNoSnap
    iexists st
    iframe Hmo
    ipureintro; exact Hns
  isplitr
  · iintro !> %L #HL %Hfit
    iunfold clusterWorkloadOk at Hwl
    imod Hwl $$ HL with ⟨%Hent, #Hbw⟩
    ihave %HLi := srvRLogLb_idx ρ.raft L $$ HL
    imodintro
    imodintro
    unfold srvC
    iframe Hbw HL
    ipureintro
    refine ⟨?_, Hent⟩
    rw [← hai0]
    exact srvIdxOk_of_W _ _ HLi Hfit
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
  iintro ⟨⟨#Hci, ⟨%v, #Hfb⟩, #Hreqb, ⟨%vr, #Hrdb⟩, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci',
      #Hrn, %HEr, %Hρrd, Hloop, Hsend, Happly, Hrdone, #Hcci, #Hwci, Hw, Haw, Hdone, Hstop, Hstopping,
      Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr,
      ⟨%kv, %rv, #Hkv, #HisKV, #Hrv, #HisRV⟩, HWB, #Hsmall, #HNR, #Hcv, %Hbound,
      ⟨%ua, Hua, #Hfor, Hakv⟩, Hwtok, Hsnapb⟩, Hsnap⟩
  iframe Hci Hreqb Hrunb Hsab Hai Hkvi Hti Hci' Hrn HNR Hcv Hcci Hwci
  iframe Hloop Hsend Happly Hrdone Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg
  iframe HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hsnap Hwtok Hsnapb Hcrun
  isplitr
  · unfold srvFieldsBuiltNA
    iexists v
    unfold srvFieldsBuilt
    iframe Hfb
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
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, Hra, Har, Hao, Hal, Hkr, Hfs⟩
  iexists st₀, a, t, f
  iframe Hth Hbe Hca Hlg Hbm Hbo Hra Har Hao Hal Hkr Hfs
  isplitr
  · ipureintro; exact Hok
  iexists ua
  iframe Hua Hfor Hakv

end gap

end EtcdGrove
end Perennial
