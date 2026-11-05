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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderRetire

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


/-! ## The census (gap 4): every reader of the store retired, the backend's whole open token -/

/-- `a` and `b` copies of `P` are `a + b`. -/
theorem stop_rep_join (P : IProp GF) (a b : Nat) :
    ⊢ ([∗list] _x ∈ List.replicate a (), P) -∗ ([∗list] _x ∈ List.replicate b (), P) -∗
      [∗list] _x ∈ List.replicate (a + b) (), P := by
  iintro Ha Hb
  rw [← List.replicate_append_replicate]
  iapply BigSepL.bigSepL_append.2
  iframe Ha Hb

/-- `a` copies of `P` and one more are `a + 1`. -/
theorem stop_rep_cons1 (P : IProp GF) (a : Nat) :
    ⊢ ([∗list] _x ∈ List.replicate a (), P) -∗ P -∗ [∗list] _x ∈ List.replicate (a + 1) (), P := by
  iintro Ha H
  rw [List.replicate_succ]
  iapply BigSepL.bigSepL_cons.2
  iframe H Ha

/-- `a` copies of `P` are `b`, at `a = b`. -/
theorem stop_rep_cast (P : IProp GF) (a b : Nat) (h : a = b) :
    ([∗list] _x ∈ List.replicate a (), P) ⊢ [∗list] _x ∈ List.replicate b (), P := by
  subst h; exact .rfl

/-- **The storage-version monitor's read token of the current backend `d`, at the stop** (hard stop
H2, `questions.md`): `srvWTPool`'s invariant holds the monitor's read token of the backend its
quarter of `E.γbe` names, or, while the monitor's session has it checked out, a part of `E.γbe` in
its place. The stop's census needs the token (its share of the backend's open token, for `Close`);
nothing yet says the monitor's session is over when `s.wg.Wait()` returns. Stated at the apply
thread's quarter of `E.γbe` at `d` (which fixes the backend) and one later credit (the invariant's
opening). -/
theorem stop_monitorRT (E : apply.AEnv GF) (γp : GName) (d : mvcc.KBReal) :
    £ 1 ∗ srvWTPool (GF := GF) E γp ∗ dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ⊢
      |={⊤}=> dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d ∗ mvcc.bkRTx d.γB d.P d.be := by
  -- H2 (questions.md): the monitor's session may hold it; hard stop pending
  sorry

/-- **The census** (gap 4, as `NewServer`'s error path R-D1): `m` idle readers of the store, the
writer's fragment (the pin `storeReaders_retire` needs), the writer's retired count with its own
retired token, the monitor's retired token, the constructors' half and the pool's shares of the
backend's open token make, with what `kv.Close` gives back (the loops' readers, the compaction
job's resource: `wsCloseRes`), the whole open token, when `m` with the loops' and the two retired
ones is the whole stock. -/
theorem stop_census (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d)
    (m : Nat) (hm : m + mvcc.wsLoopN + 2 = backend.rdStockN - mvcc.nJobRd γ.kb) :
    £ 1 ∗ mvcc.isStore (GF := GF) s γ ∗ mvcc.writerFrag γ ∗
      ([∗list] _x ∈ List.replicate m (), mvcc.storeReader s γ) ∗
      mvcc.retiredAt γ (2 + mvcc.nJobRd γ.kb) ∗ mvcc.storeRT γ ∗ mvcc.bkRTx d.γB d.P d.be ∗
      backend.bOpen d.γB (1 : Qp).half ∗
      ([∗list] _x ∈ List.replicate (backend.rdPoolN + backend.authRdN) (),
        backend.bOpen d.γB backend.rdOpen) ⊢
    (mvcc.wsCloseRes s γ ={⊤}=∗ backend.bOpen d.γB 1) := by
  iintro ⟨Hlc, #Hs, Hfrag, Hrs, Hret, HrtA, HrtM, Hhalf, Hpool⟩ Hcr
  iunfold mvcc.wsCloseRes at Hcr
  icases Hcr with ⟨Hlrs, Hjob⟩
  ihave Hrs := stop_rep_join _ _ _ $$ Hrs Hlrs
  imod mvcc.storeReaders_retire s γ _ _ $$ Hlc Hs Hfrag Hrs Hret with ⟨Hrts, -, -⟩
  have hRT : mvcc.storeRT (GF := GF) γ = mvcc.bkRTx d.γB d.P d.be := by
    show mvcc.kbRT γ.kb = _
    rw [hk]; rfl
  rw [hRT]
  ihave Hrts := stop_rep_cons1 _ _ $$ Hrts HrtA
  ihave Hrts := stop_rep_cons1 _ _ $$ Hrts HrtM
  ihave Hrts := stop_rep_cast _ _ (backend.rdStockN - mvcc.nJobRd γ.kb) (by omega) $$ Hrts
  rw [← hRT]
  ihave Hstock := mvcc.storeRTs_shares γ d hk $$ [$Hrts $Hjob]
  imodintro
  iapply (backend.bOpen_one_pool d.γB).2
  iframe Hhalf Hpool Hstock

/-! ## The stopped backend's data, observed (`StopImage.stop_mergedObs` at the writer's pin) -/

/-- **`StopImage.stop_mergedObs` with the writer's pin in place of the whole writer**, in a store
that does not compact: the census spends the writer's fragment (`writerFrag`, the pin its
retirement needs) inside `Cleanup`, so after `Cleanup` the writer's pin (`wlogOwn`'s) is what is
left of `txn.kvWriter`; the observation needs no more (`writerPin_keyObs`, `writerPin_noCmp`). -/
theorem stop_mergedObsP (γA : ApplyNames) (E : apply.AEnv GF) (γr : ReadNames) (ai : w64)
    (A : List EntryModel) (x : apply.ApplyKV) (d : mvcc.KBReal) (f : w64 → w64) (st : ApplyState)
    (D : backend.Data) (hkb : E.γ.kb = some d) (hcK : ciKeys d.P)
    (hRB : ∀ n ∈ restBuckets, d.P.RB n = true) (hcm : d.cm = E.cmp) (hoffc : d.cm = false)
    (hci : ciEff γA st.k = ai) (Hwf : mvcc.IdxWf x.log []) :
    freezeY (GF := GF) γA st ∗
      backend.rbOwnIn d.γB membership.clusterBkts
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
      backend.rbPart d.γB (restSet E.authMode)
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
      mvcc.writerPin (GF := GF) E.γ x.log ∗
      backend.bStopView d.γB d.P (mvcc.lateWD (GF := GF) d)
        (batchLockInv γA (metaTM d.γB d.P)) D ⊢
    ⌜mergedObsM E.authMode γr E.cmp E.lg ai A x.log x.crev D⌝ := by
  iintro ⟨HY, Hrc, Hrn, Hkw, Hsv⟩
  iunfold backend.bStopView at Hsv
  icases Hsv with ⟨HW, HPk, Hv, Hpv, Hhk, Hr, Hck, %R, #Hfk⟩
  -- no compaction key in a store that does not compact
  ihave ⟨%hnc0, Hkw⟩ := mvcc.writerPin_noCmp E.γ d hkb x.log (D, R) $$ [Hkw Hfk]
  · iframe Hkw Hfk
  have hnc : d.cm = false → backend.fkAbsD D := fun h => (hnc0 h).1
  -- the window's observation, at the stopped lock's pieces
  ihave #Hobs := snapObs_window γA d.γB d.P hcK (mvcc.lateWD d)
    iprop(mvcc.writerPin E.γ x.log) st (restSet E.authMode)
    (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk (fun _ => False) ∅
    (fun vd v => ((∀ k v, vd.lookup (mvcc.keyName, k) = some v →
        (mvcc.bucketMap x.log).lookup k = some v) ∧
      (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap x.log).lookup k)) ∧
      apply.windowObs d x.log x.crev vd v) $$ []
  · iintro !> %vd %v Hkw HW Hv Hp Hc
    ihave %hk := mvcc.writerPin_keyObs E.γ d hkb x.log vd $$ [Hkw Hv]
    · iframe
    ipureintro
    exact ⟨hk, fun h => by rw [hoffc] at h; cases h⟩
  ihave Hnone := backend.rbPart_none (GF := GF) d.γB (∅ : GMap GoString backend.BktData)
  ihave %h := Hobs $$ %(backend.sData d.P D) %(backend.hkData d.P D) %(backend.rbData d.P D)
    %(backend.fkVals D) [HY Hrc Hrn Hnone Hkw] HW HPk Hv Hpv Hhk Hr Hck
  · iframe HY Hkw
    iframe Hrc Hrn Hnone
  ipureintro
  obtain ⟨⟨hciO, hrbD, -⟩, ⟨-, hex⟩, hwo⟩ := h
  exact mergedObsM_of_obs E γr ai A x d f D hcK hRB hcm (hci ▸ hciO) hrbD hex hwo hnc Hwf

/-! ## The image's configuration point -/

/-- **The stopped member's configuration point** (`srvDiskImage`'s): at the applied index `i` of
the server's log `A` (a first start: `pre = []`, `ai0 = 0`), past the bootstrap log, raft's
membership is the voters' simple one (`srv_confAt_simple`), and every conf state a restart can
build from the image's `members` bucket is it (`RestConf.restModel_confState`, its premises from
`srvRaftLogInv` and the committed log's conf changes, `srv_committed_ccBoot`), given that the
voters are the bootstrap log's members, distinct (`bootOk`'s, `hvs`). -/
theorem stop_imageConf (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (D : backend.Data) (i : w64) (hpre : γ.pre = []) (hi : uint.nat i = A.length)
    (hvs : γ.raft.vs.Nodup ∧ srvBootLogOk γ.raft.vs γ.raft.boot) (hc0 : γk.c0 = W64 0)
    (hboot : γ.raft.boot.length ≤ A.length)
    (himg : imageAt γk γ.raft.boot i (γ.pre ++ A) A D) :
    srvRaftLogInv (GF := GF) γ ∗ srvRLogLb γ A ⊢
      |={⊤}=> confAt γ.raft.cl (uint.nat i) (Membership.simple γ.raft.cfg) ∗
        ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs (Membership.simple γ.raft.cfg)⌝ := by
  iintro ⟨#Hinv, #HA⟩
  ihave #Hinv' := Hinv
  iunfold srvRaftLogInv at Hinv'
  icases Hinv' with ⟨-, #Hcl, -, -, -, #Hb, -⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, -, %Hurl⟩
  ihave %Hpfx := srvRLogLb_prefix γ _ A $$ [Hb HA]
  · iframe Hb HA
  ihave #HA' := HA
  iunfold srvRLogLb at HA'
  icases HA' with ⟨#Hl, %Hidx⟩
  have hlen : uint.nat i ≤ (srvLE γ A).length := by simp [srvLE, hpre, hi]
  imod srv_confAt_simple γ (srvLE γ A) (uint.nat i) hlen ⊤ (fun _ _ => CoPset.mem_full)
    (fun _ _ => CoPset.mem_full) $$ [Hinv Hl] with #Hc
  · iframe Hinv Hl
  imod srv_committed_ccBoot γ (srvLE γ A) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hinv Hl] with %Hcc
  · iframe Hinv Hl
  imodintro
  iframe Hc
  ipureintro
  -- the log is the bootstrap log and the rest `R`
  obtain ⟨R, hR⟩ : (γ.raft.boot.map EntryModel.ofM) <+: A := by
    rcases Hpfx with h | h
    · exact h
    · have hl := h.length_le
      simp only [List.length_map] at hl
      have : A = γ.raft.boot.map EntryModel.ofM :=
        h.eq_of_length (by simp only [List.length_map]; omega)
      rw [this]; exact List.prefix_refl _
  -- a committed entry's conf change is `ccApplyOk`'s
  have hcfg : γ.raft.cfg = GMap.listToSet γ.raft.vs := rfl
  have hmem : ∀ m ∈ A, m.typ = W32 1 → ccBootOk γ.raft.cfg m.data := fun m hm ht =>
    Hcc m.toLE (by simp only [srvLE, hpre, List.nil_append]; exact List.mem_map_of_mem hm) ht
  have hbcc : ∀ e ∈ γ.raft.boot, ∀ cc, ccDecodeV1 e.Data' = some cc →
      ccApplyOk (GMap.listToSet γ.raft.vs) cc := by
    intro e he cc hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨-, -, hkk⟩ := hvs.2
    obtain ⟨-, -, hty, -⟩ := hkk k _ (List.getElem?_eq_getElem hk)
    have hin : EntryModel.ofM γ.raft.boot[k] ∈ A := by
      rw [← hR]; exact List.mem_append_left _ (List.mem_map_of_mem (List.getElem_mem hk))
    exact hmem _ hin (by simpa [EntryModel.ofM] using hty) cc (by simpa [EntryModel.ofM] using hd)
  have hcc : ∀ e ∈ R, e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc →
      ccApplyOk (GMap.listToSet γ.raft.vs) cc := by
    intro e he hne cc hd
    have hin : e ∈ A := by rw [← hR]; exact List.mem_append_right _ he
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hin
    obtain ⟨-, hty⟩ := Hidx k e (by rw [← hke]; exact List.getElem?_eq_getElem hk)
    rcases hty with h0 | ⟨h1, -⟩
    · exact absurd h0 hne
    · exact hmem e hin h1 cc hd
  -- the `members` bucket is the rest model's
  obtain ⟨-, -, -, ⟨f, hf⟩, -⟩ := himg
  have hD : D.lookup go!"members" =
      (restModel (W64 0) γ.raft.boot (γ.raft.boot.map EntryModel.ofM ++ R)).bk.lookup
        go!"members" := by
    rw [hf go!"members" (by simp [mvcc.restBuckets]), restLeasesWith_lookup_other _ _ _ _
      (by decide), hpre, List.nil_append, hR, hc0]
  have h := restModel_confState γ.raft.vs γ.raft.boot R hvs.2 hvs.1 Hurl hbcc hcc D hD
  exact h

/-- **`s.Cleanup()` at the stop, and the image** (see the file header): from the apply thread's
resources at the handed log `A` (`applyResStop`), the stop's slot but its raft part, the data
directory and the caller's unused serving readers (`srvShutdownPre`'s), the stop request's evidence
(`srvBootApplied`), and what `raftNode.stop` returned (`raftNode.stop.specStop`'s post), the
member's image at the stopped incarnation's names. Scope (`run.specStop`'s): a first start
(`ai₀ = 0`, `pre = []`), auth off, no compactor; and (2026-11-05) a store that does not compact
(`E.cmp = false`: in compaction mode the apply thread's compaction right, `apply.cmpOwn`, is both
what `kv.Close` takes, `wsCloserR`, and what the image's observation reads, `apply.cmpObs`), the
voters the bootstrap log's members, distinct (`bootOk`'s `γ.vs = ps ∧ ps.Nodup ∧ srvBootLogOk ps
γ.boot`: what the image's configuration point needs). Besides: the write budget's invariant (the
storage-version monitor's read token, `stop_monitorRT`), `isServerApplyAll` (the KV names' start
log), two later credits. A `Prop`, so that `run`'s proof takes it as a hypothesis. -/
abbrev stopCleanupImage.spec : Prop :=
  ∀ (K : AuthC) (C : ApplyCtx GF) (A : List EntryModel) (Er : RNEnv GF)
    (γg : GoNames) (γcx : context.ContextNames) (v : RunFields) (SP : IProp GF)
    (TM : MetaCI → IProp GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (dd : GoString),
    C.E.authMode = K.mode → C.E.authOn = false → v.compactor = GoInterface.nil →
    (Er.C = srvCM K.isOn C.ρ C.E C.ai₀ C.c₀ C.x₀ ∧ Er.γr = C.γr ∧
      (uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧ C.rn.pre = [] ∧ C.ai₀ = W64 0)) →
    storage.diskOk →
    C.E.cmp = false →
    (C.ρ.rd.raft.raft.vs.Nodup ∧ srvBootLogOk C.ρ.rd.raft.raft.vs C.ρ.rd.raft.raft.boot) →
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
            (C.rn.pre ++ A).length ≤ σ.commit⌝) ∗
        srvWTPool C.E C.wt ∗ isServerApplyAll C.s C.γr ∗ £ 2 }}
      (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
    {{ RET #(); srvDiskImage C.ρ.rd.raft.raft C.ρ C.rn.id dd }}

/-- `stopCleanupImage.spec`'s proof, from `Cleanup`'s spec and the stop commit's request's callees
(`commitReq_freeze`'s). -/
theorem stop_cleanup_image (hCl : EtcdServer.Cleanup.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    stopCleanupImage.spec (GF := GF) (hG := hG) := by
  intro K C A Er γg γcx v SP TM cfg dd hM hoff hcp hEr hdisk hcmp hvs
  iintro %Φ ⟨#Hpkg, #Hsrv0, #Hrn, #Hrf, Hres, Hclp, Hcsp, Himp, #Hdd, Hrds, #Hba, Hvac,
    ⟨%S, %σ, Hrst, Hwc, %hσ⟩, #Hpool, #Hsa, Hlc⟩ HΦ
  -- auth off
  cases K with
  | on γa =>
    exfalso
    simp [apply.AEnv.authOn, hM, AuthC.mode, auth.AuthMode.isOn] at hoff
  | off => ?_
  unfold applyResStop
  icases Hres with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %hB, #Hsrv, -, -, -, -, -, Hst, -, -,
    -, Hbr, -, HKV, Hao, #Hlog, Hkr, HRs, #Hkv, -, -, Hso, %hp⟩
  obtain ⟨hc0a, hpre, hai0⟩ := hEr.2.2
  have hc00 : C.c₀ = W64 0 := by rw [hai0] at hc0a; word
  -- the current backend's environment is the start's on another backend
  obtain ⟨-, pB, PB, fB, cB, ROB, RWB, hEB⟩ := hB
  have hBcmp : B.E.cmp = false := by rw [hEB]; exact hcmp
  have hBs : B.E.s = C.E.s := by rw [hEB]; rfl
  have hBbe : B.E.γbe = C.E.γbe := by rw [hEB]; rfl
  have hBam : B.E.authMode = .off := by rw [hEB]; exact hM
  have hrdr : mvcc.storeReader (GF := GF) C.E.s C.E.γ = mvcc.storeReader B.E.s B.E.γ := by
    rw [hEB]; rfl
  -- the apply thread's view of the server: its backend `d`, with its hooks, not compacting
  have hS : isServerC (GF := GF) AuthC.off C.s B.γ C.ci B.TM B.E C.ρ C.γr ⊢
      isServer C.s B.γ C.ci B.TM B.E C.ρ C.γr :=
    (isServerM_C AuthC.off C.s B.γ C.ci B.TM B.E C.ρ C.γr).2
  ihave #HsrvI := hS $$ Hsrv
  ihave #Hsrv' := Hsrv
  iunfold isServerC at Hsrv'
  icases Hsrv' with ⟨%hρ, #HCI, ⟨%vf, #Hf⟩, #Hat, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hbh⟩
  iunfold srvBeHooked at Hbh
  icases Hbh with ⟨%d, %bh, %lgh, %Hd, -, #Hbhk, #HhkAt, #HB⟩
  obtain ⟨hkb, hcK, hhP⟩ := Hd
  obtain ⟨-, -, -, γB, HH, hRO, -, d', _al, _stl, _lp, hkb', hγB, -, hcm⟩ := Henv
  rw [hkb] at hkb'
  obtain rfl := Option.some.inj hkb'
  subst hγB
  have hdcm : d.cm = false := hcm.trans hBcmp
  have hnk : ¬ mvcc.kbCmpM B.E.γ.kb := by rw [hkb]; simp [mvcc.kbCmpM, hdcm]
  iunfold srvAtomicsC at Hat
  icases Hat with ⟨-, -, #Hki⟩
  iunfold srvKVInvsC at Hki
  icases Hki with ⟨-, -, #Hrl, -⟩
  -- the start's backend does not compact either (`srvKeepRdN`'s count)
  ihave #Hsrv0' := Hsrv0
  iunfold isServerC at Hsrv0'
  icases Hsrv0' with ⟨-, -, ⟨%vf0, #Hf0⟩, -⟩
  iunfold srvFieldsAtM at Hf0
  icases Hf0 with ⟨-, -, -, -, -, %Henv0, -⟩
  obtain ⟨-, -, -, -, -, -, -, d0, -, -, -, hkb0, -, -, hcm0⟩ := Henv0
  have hnj0 : mvcc.nJobRd C.E.γ.kb = 0 := by
    rw [hkb0]; simp [mvcc.nJobRd, hcm0, hcmp]
  have hnjB : mvcc.nJobRd B.E.γ.kb = 0 := by
    rw [hkb]; simp [mvcc.nJobRd, hdcm]
  -- the lessor's stop right and the auth store's closer (the slot's)
  icases srvStop.cleanup_pieces C.s C.E $$ Hclp with ⟨⟨%lp, #Hlpa, Hlst⟩, #Hauth⟩
  ihave Hac := Hauth $$ %hoff
  icases Hac with ⟨%stl, #Hstla, #Hacl⟩
  -- the snapshot path's resources at the current backend: its stop channels, the constructors'
  -- half of the open token, the KV's closer, the backend's file and its directory entry
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γt, %nt, -, -, -, Hsr⟩
  iunfold srvSnapRes at Hsr
  icases Hsr with ⟨%d2, %al2, %dd2, %hd2, #Hsch, Hhalf, -, Hkc, #Hdd2, Hpath, #Hbf⟩
  rw [hkb] at hd2
  obtain rfl := Option.some.inj hd2
  have hq : srvOpenQ B.E.authMode = (1 : Qp).half := by rw [hBam]; rfl
  rw [hq, srvKVCloserW_off C.s B.E hnk]
  iunfold srvKVCloser at Hkc
  icases Hkc with ⟨%wsl, #Hkva, Hwcl⟩
  -- the watchable store at the KV field
  icases Hkv with ⟨%kv, #Hkva', #HisKV⟩
  icombine Hkva Hkva' gives %hkveq
  iunfold txn.isKV at HisKV
  icases HisKV with (⟨%hk1, -, -⟩ | ⟨%ws, %γw, %hk2, #Hws⟩)
  · exfalso
    rw [← hkveq] at hk1
    simp [interface.mkOk] at hk1
    have hne : go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty ≠
        go_etcd_io.etcd.server.v3.storage.mvcc.store.ty := by
      unfold go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty
        go_etcd_io.etcd.server.v3.storage.mvcc.store.ty
      simp
    exact hne hk1.1
  obtain ⟨hk2, hγw⟩ := hk2
  rw [← hkveq] at hk2
  have hws : wsl = ws := by
    simp only [interface.mkOk, GoInterface.ok.injEq] at hk2
    simpa [intoVal_eq_iff] using hk2
  subst hws
  -- the apply thread's KV resources
  icases srvApplyKVC_coreA AuthC.off C.s B.E C.γw x sa $$ HKV with ⟨%ua, Hcore, -, -⟩
  iunfold srvApplyKVCore at Hcore
  icases Hcore with ⟨-, -, Hakv, Hbo, -, -⟩
  iunfold apply.applyKV at Hakv
  icases Hakv with ⟨%pu, -, -, Hko, -⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨HsrA, Hkw, -, -, Hwo⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfr⟩
  ihave %Hwf := soleWriter_idxWf B.E.γ x.log $$ Hsw
  iunfold txn.wlogOwn at Hwl
  icases Hwl with ⟨-, Hpin⟩
  iunfold mvcc.writerOwn at Hwo
  icases Hwo with ⟨HrtA, Hret⟩
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d3, %hd3, Hbe, Hg, -, HbPl⟩
  rw [hkb] at hd3
  obtain rfl := Option.some.inj hd3
  iunfold backend.bkRPool at HbPl
  icases HbPl with ⟨-, HoPs⟩
  rw [hBbe]
  -- the monitor's read token (H2)
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc1, Hlc2⟩
  imod stop_monitorRT C.E C.wt d $$ [Hlc1 Hg] with ⟨Hg, HrtM⟩
  · iframe Hlc1 Hpool Hg
  -- the census (gap 4): the slot's readers with the compactor's, the caller's 128, the apply
  -- thread's own, at the current names
  iunfold srvRunFieldsAt at Hrf
  icases Hrf with ⟨-, -, -, -, -, -, -, #Hcpa, #Hcpok, -⟩
  rw [hcp]
  ihave Hcr := srvStop.census_readers C.s C.E $$ [Hcsp Hcpa]
  · iframe Hcsp Hcpa
  ihave Hrs := stop_rep_join _ _ _ $$ Hcr Hrds
  rw [hrdr]
  ihave Hrs := stop_rep_cons1 _ _ $$ Hrs HsrA
  ihave #HisSt : mvcc.isStore B.E.s B.E.γ $$ [Hws]
  · rw [← hγw]; iapply mvcc.isWatchableStore_isStore; iexact Hws
  have hm : srvKeepRdN C.E.γ + 1 + (64 + 64) + 1 + mvcc.wsLoopN + 2 =
      backend.rdStockN - mvcc.nJobRd B.E.γ.kb := by
    have hL : mvcc.wsLoopN = 2 := rfl
    simp only [srvKeepRdN, hnj0, hnjB, backend.rdStockN_val, hL]
  ihave Hwand := stop_census B.E.s B.E.γ d hkb (srvKeepRdN C.E.γ + 1 + (64 + 64) + 1) hm
    $$ [Hlc2 HisSt Hfr Hrs Hret HrtA HrtM Hhalf HoPs]
  · iframe Hlc2 HisSt Hfr Hrs Hret HrtA HrtM Hhalf HoPs
  ihave Hwand' : (mvcc.wsCloseRes B.E.s γw.st ={⊤}=∗ backend.bOpen d.γB 1) $$ [Hwand]
  · rw [hγw]; iexact Hwand
  ihave Hwcm : mvcc.wsCloserM wsl B.E.s γw.st (-1) $$ [Hwcl]
  · rw [hγw]; iapply (mvcc.wsCloserM_off _ _ _ _ hnk).2; iexact Hwcl
  -- the stop commit's request (`commitReq_freeze`)
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hschpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hcipkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Hnh := isBackendNH_of_hooksAt d.γB d.P (mvcc.lateWD d)
    (batchLockInv B.γ (metaTM d.γB d.P)) d.be (storage.hooksIface bh) $$ [HB HhkAt]
  · iframe #
  iunfold isServerCI at HCI
  icases HCI with ⟨-, #Hci, #Hinv⟩
  ihave #Hreq := commitReq_freeze hOn hSave hPut hUR hID hName hSafe B.γ C.ci d.γB d.P
    (mvcc.lateWD d) d.be bh lgh hcK hhP st hp.1.1
    $$ [Hspkg Hbpkg Hschpkg Hcipkg Hbhk Hnh HB Hci Hinv]
  · iframe #
  iunfold srvStopChans at Hsch
  icases Hsch with ⟨-, #HSC⟩
  -- `s.Cleanup()`
  iapply wp_fupd
  wp_apply hCl C.s lp wsl B.E.s γw (-1) stl iprop(True) C.E.γbe d (mvcc.lateWD d)
      (batchLockInv B.γ (metaTM d.γB d.P)) v.compactor (applyThread B.γ st) (freezeY B.γ st)
    $$ [Hlst Hwcm Hbr Hbe Hg Hwand' Hst]
    as ⟨-, -, -, -, HY, %D, Hsv, Hfile⟩
  · rw [hcp]
    iframe Hlpa Hlst Hkva Hws Hwcm Hstla Hacl Hbr Hbe Hg HB HSC Hwand' Hst Hreq Hcpa Hcpok
  -- the stopped backend's data observed: the image of the applied log at `ai`
  have hci : ciEff B.γ st.k = ai := by
    obtain ⟨-, -, hJ, hle, -⟩ := hp
    rcases hJ with h | ⟨-, h⟩
    · rw [h, hc00] at hle ⊢; word
    · word
  have hRB : ∀ n ∈ restBuckets, d.P.RB n = true := fun n hn => by
    simp [mvcc.KBReal.P, hn]
  ihave ⟨%f, HRs, -, -⟩ := srvRest_open B.E C.γr A $$ HRs
  rw [hRO]
  iunfold srvRestOwnH at HRs
  icases HRs with ⟨Hro, -⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrc, Hrn', -, -⟩
  ihave %hobsM := stop_mergedObsP B.γ B.E C.γr ai A x d f st D hkb hcK hRB hcm hdcm hci Hwf
    $$ [HY Hrc Hrn' Hpin Hsv]
  · iframe HY Hrc Hrn' Hpin Hsv
  have hobs := mergedObs_of_M hBam hobsM
  -- the KV names' start values
  have ekr : kvRunM (GF := GF) AuthC.off.isOn C.γr C.ai₀ C.c₀ A x sa = kvRun C.γr C.ai₀ C.c₀ A x :=
    rfl
  rw [ekr]
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka, %hk0⟩
  iunfold isServerApplyAll at Hsa
  icases Hsa with ⟨%wt0, %msc, %sc, -, -, -, -, -, -, -, -, -, -, -, %Hlog0⟩
  have hc0' : C.γr.kv.c0 = W64 0 := hk0.1.trans hc00
  imod merged_imageAt C.s B.γ C.ci B.TM B.E C.ρ C.γr ai A x D ⟨hc0', Hlog0⟩ $$ [HsrvI Hka]
    with ⟨Hka, %himg⟩
  · iframe HsrvI Hka; ipureintro; exact hobs
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, -⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, -⟩
  -- raft's names: the raft wrapper's
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  icases Hrn' with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, #Henv, -⟩
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %hraft, -⟩
  have hγ : C.γr.raft.raft = C.rn.node := by rw [← hEr.2.1]; exact hraft.1
  have hpre' : C.γr.raft.pre = [] := by rw [← hEr.2.1, hraft.2.1, hpre]
  have hai : uint.nat ai = A.length := by
    have h1 := hp.2.1; rw [hai0] at h1; word
  -- the bootstrap log applied (the stop request's evidence)
  ihave #Hrl' := Hrl
  iunfold srvRaftLogInv at Hrl'
  icases Hrl' with ⟨-, #Hcl, -⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, %HbL, -⟩
  iunfold srvBootApplied at Hba
  icases Hba with ⟨%vb, #Hvb, %hvb⟩
  rw [hρ] at hvb hvs
  iunfold appliedAtLeast at Hvb
  iunfold srvAppliedOwn at Hao
  icases Hao with ⟨Hao, -⟩
  rw [hρ]
  ihave %hle := monoNatLbOwn_valid C.γr.applied _ _ _ $$ Hao Hvb
  have hboot : C.γr.raft.raft.boot.length ≤ A.length := by rw [← hai]; omega
  -- the configuration point
  imod stop_imageConf C.γr.raft C.γr.kv A D ai hpre' hai hvs hc0' hboot himg $$ [Hrl HA]
    with ⟨#Hconf, %hconf⟩
  · iframe Hrl HA
  -- the registry's authority and the WAL's files
  icases srvStop.image_inputs C.s cfg C.rn dd $$ [Himp Hdd] with ⟨⟨%M, HM⟩, %st', #Hst', %hwd⟩
  · iframe Himp Hdd
  iunfold rnWalClosed at Hwc
  icases Hwc with ⟨%st2, #Hst2, Hw⟩
  iunfold rnWalClosedW at Hw
  icombine Hst' Hst2 gives %hsteq
  subst hsteq
  -- the backend's file
  iunfold srvDataDir at Hdd
  icases Hdd with ⟨#Hdd1, -⟩
  icombine Hdd1 Hdd2 gives %hddeq
  subst hddeq
  icases Hfile with (⟨%path, #Hbf2, Hfh⟩ | %hbad)
  rotate_left
  · exact absurd hdisk.2.1.2.2.2 hbad
  ihave %hpath := backend.bFile_agree d.γB (config.backendPathOf dd) path $$ [Hbf Hbf2]
  · iframe Hbf Hbf2
  subst hpath
  -- the image
  imodintro
  iapply HΦ
  iunfold srvDiskImage
  iexists S, σ, ai, A, D, Membership.simple C.γr.raft.raft.cfg, M
  rw [hρ] at *
  iunfold srvFiles
  rw [← hwd, ← hγ]
  iframe Hvac Hrst HA HM Hpath Hfh Hconf Hw
  ipureintro
  have h1 := hp.2.1
  have h2 := hσ.2.1
  have h3 := hσ.2.2
  rw [hpre] at h2 h3
  refine ⟨hσ.1, ⟨rfl, hc0'⟩, ⟨by rw [hk0.2]; exact h1, by rw [hpre'] at himg ⊢; exact himg⟩,
    ⟨by simp at h2; omega, by simp at h3; omega, by rw [HbL]; omega⟩, hconf⟩

end proof

end EtcdGrove
end Perennial
