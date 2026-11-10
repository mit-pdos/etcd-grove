/-
**`run`'s deferred shutdown: the apply thread's resources at the stop, `Cleanup` and the image**
(the restart plan's R2b-3d stage 5c/5d, 2026-11-05; `notes/restart-plan.md`, "R2b-3d stage 5").
Lean-first (no Rocq counterpart).

`run.spec`'s proof (`EtcdServer__run.lean`, `wp_proofG`, at a stop request) runs the deferred
shutdown: `close(stopping)` under `wgMu`, `cancel()`, `sched.Stop()` (the apply thread's resources
at the handed log `A` back, `applyResR`), `s.wg.Wait()`, `s.r.stop()` (`raftNode.stop.spec`),
`s.Cleanup()`, `close(done)` with the image escrowed. This file has the step that is about the
apply thread's resources rather than the control flow (what `raftNode.stop` takes out of them, the
WAL's apply half and the live transport for `Er.ST`, is `EtcdServer__run.lean`'s `stop_split`, the
rest kept as `applyResStopR`):
* `stop_cleanup_image`: `s.Cleanup()` from the rest, the stop's slot (`srvStop.slot`) and what
  `raftNode.stop` returned, giving the stopped member's image (`srvDiskImage`): `Cleanup`'s
  precondition by gap 4's census (every store reader retired, the backend's whole open token) and
  the stop commit's request (`commitReq_freeze`), then the image from `Cleanup`'s post
  (`StopImage.stopImageG`, `stop_obs`, `stop_imageAt`, `RestConf.restModel_confState`, `srvFiles`;
  R6, 2026-11-07: over mvcc's API, the census by mvcc's reader tokens and `mvccClosed_rest.law`, the
  store's image by `mvccImage_stop.law`). Since R2d'a swap batch 4 (2026-11-07) in restart form, over `applyResStopR` and the ghost log
  (`stopCleanupImage.spec`; its first-start instance, the old text, was `specFirst`, deleted with
  the run swap, swap batch 5).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestConf
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cleanup
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__stop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopCensus
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

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

/-- **The apply thread's resources at the stop, in restart form, but what `raftNode.stop` takes**
(R2d'a A10 item 3; `stopCleanupImage.spec`'s since swap batch 4): `applyResR`'s without the WAL's apply half (`rnWalTokA`) and the membership resource
(`srvApRes`, whose live transport goes to `Er.ST`). -/
def applyResStopR (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV)
      (sa : auth.AuthState) (g : w64),
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServerC K C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗
    epCsAt C.ρ.raft (ghostOf rp A) cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ mvcc.api.mvccReaders B.E.γ 1 ∗
    srvApplyKVC K C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr g ∗ appliedLogAt C.γr g x.log ∗ kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A) x sa ∗
    srvRestR B.E C.γr rp A ∗ srvRLogLb C.ρ.raft rp.A₀ ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ □ mvcc.api.isMvcc kv B.E.γ ∗ ⌜kv = B.E.kv⌝) ∗
    (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗ acTok K (ciEff B.γ st.k) ∗
    srvSnapOwn C.s C.ci B.E C.γr B.γ ai ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff B.γ st.k) C.c₀ g ∧
      uint.Z g ≤ uint.Z (ciEff B.γ st.k) ∧
      lastTermIs A at' ∧
      uint.Z g = uint.Z C.ai₀ + (ghostOf rp A).length ∧ rp.b ≤ A.length ∧
      (∀ m ∈ rp.A₀, m.typ = W32 0 ∨ m.typ = W32 1) ∧
      uint.Z C.ai₀ + rp.A₀.length ≤ uint.Z (ciEff B.γ st.k) ∧
      uint.Z C.ai₀ + rp.A₀.length + 1 < 2 ^ 64⌝)

/-- `kvRunM`'s log is committed (`r2d-prime`'s `kvRunM_lb`, `RunWindow.lean:212`). -/
theorem kvRunM_lbR (on : Bool) (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (st : auth.AuthState) :
    kvRunM (GF := GF) on γr ai₀ c₀ A x st ⊢ srvRLogLb γr.raft A ∗ kvRunM on γr ai₀ c₀ A x st := by
  refine (persistent_entails_left ?_).trans sep_comm.1
  cases on
  · unfold kvRunM kvRun kvApplied kvAppliedL
    iintro ⟨⟨⟨#H, -⟩, -⟩, -⟩; iexact H
  · unfold kvRunM kvRunAtOn kvAppliedOn kvAppliedLOn
    iintro ⟨⟨⟨#H, -⟩, -⟩, -⟩; iexact H

/-- The replay changes only the members: its buckets are the backend log's model's. -/
theorem restReplay_bk (γr : ReadNames) (rp : RestartPt) (G : List EntryModel) :
    (restReplay γr rp G).bk = (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ rp.A₀)).bk := by
  unfold restReplay
  rw [fold_restEntryV2]

/-- The leases' records written over two images with the same buckets have the same buckets. -/
theorem restLeasesWith_bk_congr (f : w64 → w64) (ids : List w64) (r r' : apply.RestM)
    (h : r.bk = r'.bk) : (apply.restLeasesWith f ids r).bk = (apply.restLeasesWith f ids r').bk := by
  unfold apply.restLeasesWith
  induction ids generalizing r r' with
  | nil => exact h
  | cons id ids ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold apply.restGrantT
    rw [apply.RestM.putIn_bk, apply.RestM.putIn_bk, h]


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

/-- **The storage-version monitor's read token's open share of the current backend `d`, at the stop**
(H2, `questions.md`; 2026-11-05): `srvWTPool`'s invariant holds the monitor's read token of the
backend its quarter of `E.γbe` names, or, while the monitor's session has it checked out, a part of
`E.γbe` with the monitor goroutine's receipt at the registered name (`W.reg`, `GoAttach`'s `γg.run`).
Once the shutdown's `Wait` returned (`goWaited γg`), no receipt is running (`goWaited_running`), so
the token is in. The stop takes its open share and leaves in its place an eighth of the apply
thread's quarter of `E.γbe` with its `goWaited` (so that no swap follows, and no second stop: three
halves of the receipts' authority with `GoAttach`'s invariant's). Stated at the apply thread's
quarter of `E.γbe` at `bkKey d` (which fixes the backend's names; an eighth comes back) and one
later credit (the invariant's opening). (R6, 2026-11-07, the `lean` merge: the pool's ghost
variable names the backend by its key `bkKey`, so the token's open share, the census's, rather than
the token at `d`'s parameters.) -/
theorem stop_monitorRT (E : apply.AEnv GF) (γp : WTNames) (γg : GoNames) (d : mvcc.KBReal) :
    £ 1 ∗ srvWTPool (GF := GF) E γp ∗ inv goAttachN (goAttachInv γg) ∗
      dghostVar γp.reg DFrac.discard (some γg.run) ∗ goWaited γg ∗
      dghostVar E.γbe (DFrac.own (1 : Qp).half.half) (bkKey d) ⊢
      |={⊤}=> dghostVar E.γbe (DFrac.own (1 : Qp).half.half.half) (bkKey d) ∗
        backend.bOpen d.γB backend.rdOpen := by
  iintro ⟨Hlc, #Hp, #Hgi, #Hreg, Hw, Hq⟩
  unfold srvWTPool
  iinv Hp with ⟨%a, %d0, >Ha, >Hg0, #Hs0, >Hc, Hrt⟩ Hclose
  ihave %Hdd := dghostVar_agree E.γbe (bkKey d) _ (bkKey d0) _ $$ Hq Hg0
  have hγB : d0.γB = d.γB := (congrArg Prod.fst Hdd).symm
  imod lc_fupd_elim_later (E := ⊤ \ ↑srvWTN) $$ Hlc Hrt with Hrt
  icases Hrt with (Hrt | ⟨%q, Hdep, %r, #Hreg', Hrun⟩)
  · -- the token in: its open share out, an eighth of the quarter and `goWaited` in its place
    icases (dghostVar_split (GF := GF) E.γbe (bkKey d) (DFrac.own (1 : Qp).half.half.half)
      (DFrac.own (1 : Qp).half.half.half)) $$ [Hq] with ⟨Hq1, Hq2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hq
    iunfold apply.bkRT at Hrt
    icases Hrt with ⟨-, Ho⟩
    imod Hclose $$ [Ha Hg0 Hc Hq2 Hw] with -
    · inext
      iexists a, d0
      iframe Ha Hg0 Hs0 Hc
      iright
      iexists (1 : Qp).half.half.half
      rw [← Hdd]
      iframe Hq2
      iexists γg.run
      iframe Hreg
      iright
      iunfold goWaited at Hw
      iexact Hw
    imodintro
    iframe Hq1
    rw [← hγB]
    iexact Ho
  · -- checked out: the receipt is at `γg.run`
    ihave %Hr := dghostVar_agree γp.reg _ _ _ _ $$ Hreg Hreg'
    obtain rfl := Option.some.inj Hr
    icases Hrun with (Hrun | Hw')
    · iexfalso
      iapply goWaited_running γg
      iframe Hw
      iunfold goRunning
      iexact Hrun
    · -- a second stop's: three halves of the authority with the protocol's
      have hmask : (↑goAttachN : CoPset) ⊆ ⊤ \ ↑srvWTN :=
        sync.wg_mask_ndot_ne nroot "srvGoAttach" "srvWT" (by decide)
      imod inv_acc (E := ⊤ \ ↑srvWTN) (N := goAttachN) hmask $$ Hgi with ⟨Hi, -⟩
      iunfold goAttachInv at Hi
      icases Hi with ⟨%b, %ctr, %k, %pq, %dq, -, -, -, -, >Hra, -, -, >%Hdq, -⟩
      iunfold goWaited at Hw
      icombine Hw Hra gives %Hv0
      obtain ⟨Hv0, Hk⟩ := Hv0
      subst Hk
      have hf := (ownTokAuth_fractional (GF := GF) γg.run 0).fractional (1 : Qp).half (1 : Qp).half
      rw [Qp.half_add_half] at hf
      rcases Hdq with rfl | ⟨rfl, -, -, -⟩
      · exfalso
        rw [DFrac.op_own] at Hv0
        have h := DFrac.valid_own.1 Hv0
        have hq := ((1 : Qp).half).2
        simp only [Qp.val_add, Qp.val_one] at h
        grind
      · ihave H := hf.2 $$ [Hw Hra]
        · iframe Hw Hra
        icombine H Hw' gives %Hv
        obtain ⟨Hv, -⟩ := Hv
        exfalso
        rw [DFrac.op_own] at Hv
        exact Qp_one_add_not_le _ (DFrac.valid_own.1 Hv)

-- `stop_census` (the reader tokens, 2026-11-06) is `StopCensus.lean`'s.

/-! ## The image's configuration point -/

/-- **The stopped member's configuration point** (`srvDiskImage`'s): at the applied index `i` of
the server's log `A` (a first start: `pre = []`, `ai0 = 0`), past the bootstrap log, raft's
membership is the voters' simple one (`srv_confAt_simple`), and every conf state a restart can
build from the image's `members` bucket is it (`RestConf.restModel_confState`, its premises from
`srvRaftLogInv` and the committed log's conf changes, `srv_committed_ccBoot`), the
voters the bootstrap log's members, distinct (`srvRaftLogInv`'s; R2c-1, until then a premise). -/
theorem stop_imageConf (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (D : backend.Data) (i : w64) (hpre : γ.pre = []) (hi : uint.nat i = A.length)
    (hc0 : γk.c0 = W64 0)
    (hboot : γ.raft.boot.length ≤ A.length)
    (himg : imageRestAt γk γ.raft.boot i (γ.pre ++ A) D) :
    srvRaftLogInv (GF := GF) γ ∗ srvRLogLb γ A ⊢
      |={⊤}=> confAt γ.raft.cl (uint.nat i) (Membership.simple γ.raft.cfg) ∗
        ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs (Membership.simple γ.raft.cfg)⌝ := by
  iintro ⟨#Hinv, #HA⟩
  ihave #Hinv' := Hinv
  iunfold srvRaftLogInv at Hinv'
  icases Hinv' with ⟨-, #Hcl, -, -, -, #Hb, %Hvs0⟩
  have hvs := Hvs0.2
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, -, %Hurl, -⟩
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
  obtain ⟨-, -, ⟨f, -, hf⟩⟩ := himg
  have hD : D.lookup go!"members" =
      (restModel (W64 0) γ.raft.boot (γ.raft.boot.map EntryModel.ofM ++ R)).bk.lookup
        go!"members" := by
    rw [hf go!"members" (by simp [mvcc.restBuckets]), restLeasesWith_lookup_other _ _ _ _
      (by decide), hpre, List.nil_append, hR, hc0]
  have h := restModel_confState γ.raft.vs γ.raft.boot R hvs.2 hvs.1 Hurl hbcc hcc D hD
  exact h

/-- **`s.Cleanup()` at the stop, and the image** (see the file header; R2d'a swap batch 4,
2026-11-07: one spec in restart form, the old text its first-start instance, `specFirst`, until the
run swap, swap batch 5; until then also `StopR.lean`'s `stopCleanupImageR.spec`, inside the
replay window only): from the apply thread's resources at Go's handed log `A` in restart form at the
restart point `rp` (`applyResStopR`: the ghost rows at the ghost log `ghostOf rp A`, the backend's log
`rp.A₀` committed), the stop's slot but its raft part, the caller's unused serving readers
(`srvStopReaders`, `srvStopReq`'s, R2c-4), the stop request's evidence and data directory
(`srvBootApplied`, `srvDataDir`: `srvStopReq`'s), and what `raftNode.stop` returned
(`raftNode.stop.spec`'s post; R6, 2026-11-07, the `lean` merge: the serving readers as mvcc's
reader tokens, until then 128 of mvcc's `storeReader`s) with the records' stored commit at least the ghost log (inside the
window `|A₀|`, from the restart data, `rnRestartOk_commit`), the member's image at the stopped
incarnation's names, of the ghost log (inside the window the backend's `A₀`: both committed and of
one length, so equal; past it Go's `A`). Scope (the stop request's, `srvStop.scope`): `ai₀ = 0`,
`pre = []`, auth off, no compactor (R2c-2: from no compaction mode, `srvStop.census_readers`; until
then a premise); and (2026-11-05) a store that does not compact (`E.cmp = false`). (R2c-1) The voters the bootstrap log's members,
distinct, are `srvRaftLogInv`'s. Besides: the write budget's invariant (the storage-version monitor's
read token, `stop_monitorRT`), `isServerApplyAll` (the KV names' start log), two later credits, and
(H2, 2026-11-05) the budget's register at `GoAttach`'s receipts' name and `Wait`'s `goWaited` (which
rule the monitor's open session out). A `Prop`, so that `run`'s proof takes it as a hypothesis. -/
abbrev stopCleanupImage.spec : Prop :=
  ∀ (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) (Er : RNEnv GF)
    (γg : GoNames) (γcx : context.ContextNames) (v : RunFields) (SP : IProp GF)
    (TM : MetaCI → IProp GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (dd : GoString),
    C.E.authMode = K.mode → C.E.authOn = false →
    (Er.C = srvCM K.isOn C.ρ C.E C.ai₀ C.c₀ C.x₀ ∧ Er.γr = C.γr ∧
      (uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧ C.rn.pre = [] ∧ C.ai₀ = W64 0)) →
    storage.diskOk →
    C.E.cmp = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerC K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
        isRaftNode Er C.rn (srvRAddr C.s) ∗
        srvRunFieldsAt C.s C.γr γg γcx v SP ∗
        applyResStopR K C rp A ∗
        srvStop.cleanupPart C.s C.E ∗ srvStop.censusPart C.s C.E ∗ srvStop.imagePart C.s cfg C.rn ∗
        srvDataDir C.s dd ∗ srvStopReaders C.E ∗
        srvBootApplied C.ρ ∗
        nodeVacant C.rn.node.cl C.rn.id ∗
        (∃ (S : RaftState) (σ : StorContents), raftState C.rn.node.cl C.rn.id S ∗
          rnWalClosed C.rn (srvRAddr C.s) σ ∗
          ⌜StorageHolds S σ ∧ σ.b ≤ (C.rn.pre ++ A).length ∧
            (C.rn.pre ++ ghostOf rp A).length ≤ σ.commit⌝ ∗
          -- (R2d, Q14 (a), DRAFT) the records' snapshot certificate (`raftNode.stop`'s)
          walSnapCert C.rn.node.cl σ) ∗
        srvWTPool C.E C.wt ∗ isServerApplyAll C.s C.γr ∗ £ 2 ∗
        -- (H2, 2026-11-05) the budget's register at `GoAttach`'s receipts, and `Wait` returned
        dghostVar C.wt.reg DFrac.discard (some γg.run) ∗ goWaited γg }}
      (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
    {{ RET #(); srvDiskImage C.ρ.rd.raft.raft C.ρ C.rn.id dd }}

/-- The store's reader tokens the stop counts make all of them: those `NewServer` kept
(`srvKeepRdN`), the compactor's slot's, the serving stocks' (`srvStopReaders`) and the apply
thread's. -/
theorem srvKeepRdN_total : srvKeepRdN + 1 + (64 + 64) + 1 = mvcc.api.mvccReaderN := by
  simp only [srvKeepRdN, mvcc.api.mvccReaderN_eq, backend.rdStockN_val]

/-- `stopCleanupImage.spec`'s proof, from `Cleanup`'s spec, the stop commit's request's callees
(`commitReq_freeze`'s) and mvcc's laws (R6, 2026-11-07: the reader tokens' split, the closed store's
rest, the stopped backend's image, persistence and reachability); one tail over the ghost log `G` (R2d'a swap batch 4: until then
the frozen proof at Go's log and `StopR.lean`'s `stop_cleanup_imageR` inside the window). -/
theorem stop_cleanup_image (hCl : EtcdServer.Cleanup.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hStop : mvcc.api.mvccImage_stop.law (GF := GF))
    (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) :
    stopCleanupImage.spec (GF := GF) (hG := hG) := by
  intro K C rp A Er γg γcx v SP TM cfg dd hM hoff hEr hdisk hcmp
  iintro %Φ ⟨#Hpkg, #Hsrv0, #Hrn, #Hrf, Hres, Hclp, Hcsp, Himp, #Hdd, Hrds, #Hba, Hvac,
    ⟨%S, %σ, Hrst, Hwc, %hσ, #Hσc⟩, #Hpool, #Hsa, Hlc, #Hreg, Hwd⟩ HΦ
  -- auth off
  cases K with
  | on γa =>
    exfalso
    simp [apply.AEnv.authOn, hM, AuthC.mode, auth.AuthMode.isOn] at hoff
  | off => ?_
  unfold applyResStopR
  icases Hres with ⟨%B, %st, %ai0g, %at', %a, %t, %cs, %x, %sa, %ai, %hB, #Hsrv, -, -, -, -, -, Hst,
    -, -, -, Hbr, -, Hrdk, HKV, Hao, #Hlog, Hkr, HRs, #HlbA0, #Hkv, -, -, Hso, %hp⟩
  obtain ⟨hc0a, hpre, hai0⟩ := hEr.2.2
  have hc00 : C.c₀ = W64 0 := by rw [hai0] at hc0a; word
  -- the current backend's environment is the start's on another backend
  obtain ⟨-, pB, PB, fB, cB, ROB, RWB, hEB⟩ := hB
  have hBbe : B.E.γbe = C.E.γbe := by rw [hEB]; rfl
  have hBam : B.E.authMode = .off := by rw [hEB]; exact hM
  have hBγ : B.E.γ = C.E.γ := by rw [hEB]; rfl
  -- the apply thread's view of the server: its backend `d`, with its hooks
  have hS : isServerC (GF := GF) AuthC.off C.s B.γ C.ci B.TM B.E C.ρ C.γr ⊢
      isServer C.s B.γ C.ci B.TM B.E C.ρ C.γr :=
    (isServerM_C AuthC.off C.s B.γ C.ci B.TM B.E C.ρ C.γr).2
  ihave #HsrvI := hS $$ Hsrv
  ihave #Hsrv' := Hsrv
  iunfold isServerC at Hsrv'
  icases Hsrv' with ⟨%hρ, #HCI, ⟨%vf, #Hf⟩, -⟩
  -- (R2d'a swap batch 4) the ghost log `G` (`ghostOf rp A`, the ghost index `ai` at it): inside the
  -- window the backend's `A₀` (both committed, of one length), past it Go's; the rest buckets at an
  -- image `rG` with the model's buckets either way (inside, the replay's, `restReplay_bk`)
  ihave ⟨#HlbG, Hkr⟩ := kvRunM_lbR AuthC.off.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A) x sa $$ Hkr
  ihave %hpc := srvRLogLb_prefix C.γr.raft (ghostOf rp A) rp.A₀ $$ [HlbG HlbA0]
  · rw [← hρ]; iframe HlbG HlbA0
  obtain ⟨rG, hRG, hbk⟩ : ∃ rG : apply.RestM, srvRestR B.E C.γr rp A =
      srvRestRp B.E C.γr (ghostOf rp A) rG ∧
      rG.bk = (restModel C.γr.kv.c0 C.γr.raft.raft.boot (C.γr.raft.pre ++ ghostOf rp A)).bk := by
    by_cases hwin : A.length < rp.A₀.length
    · have hl : (ghostOf rp A).length = rp.A₀.length := by
        simp only [ghostOf, List.length_append, List.length_drop]; omega
      have hGA : ghostOf rp A = rp.A₀ := by
        rcases hpc with h | h
        · exact h.eq_of_length hl
        · exact (h.eq_of_length hl.symm).symm
      refine ⟨restReplay C.γr rp A, ?_, ?_⟩
      · rw [srvRestR_in B.E C.γr rp A hwin, hGA]
      · rw [hGA]; exact restReplay_bk C.γr rp A
    · have hp' : rp.A₀.length ≤ A.length := by omega
      refine ⟨restModel C.γr.kv.c0 C.γr.raft.raft.boot (C.γr.raft.pre ++ ghostOf rp A), ?_, rfl⟩
      rw [srvRestR_past B.E C.γr rp A hp', ghostOf_past rp A hp', srvRestRp_model]
  have hAG : A.length ≤ (ghostOf rp A).length := by
    simp only [ghostOf, List.length_append]; omega
  rw [hRG]
  generalize ghostOf rp A = G at hp hbk hAG hσ ⊢
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hbh⟩
  iunfold srvBeHooked at Hbh
  icases Hbh with ⟨%d, %bh, %lgh, %gx, %Hd, -, #Hbhk, #HhkAt, -⟩
  obtain ⟨hBT, hcK, hhP, hPk⟩ := Hd
  obtain ⟨-, -, γB, HH, hRO, -, d', _al, _stl, _lp, hBT', hγB, -⟩ := Henv
  have hdd' : d' = d := srvBkTie_inj d' d (hBT'.symm.trans hBT)
  subst d' γB
  -- the store invariant (`srvKVInvs`'s)
  ihave #HsrvI' := HsrvI
  iunfold isServer at HsrvI'
  icases HsrvI' with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨-, -, #Hrl, #Hks, %Hwit, -⟩
  obtain ⟨-, -, ⟨hw1, hw2, hw3, hw4⟩, -⟩ := Hwit
  -- the lessor's stop right and the auth store's closer (the slot's)
  icases srvStop.cleanup_pieces C.s C.E $$ Hclp with ⟨⟨%lp, #Hlpa, Hlst⟩, #Hauth⟩
  ihave Hac := Hauth $$ %hoff
  icases Hac with ⟨%stl, #Hstla, #Hacl⟩
  -- the snapshot path's resources at the current backend: its stop channels at the store's write
  -- invariant, the constructors' half of the open token, the backend's file and its directory entry
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γt, %nt, -, -, -, Hsr⟩
  iunfold srvSnapRes at Hsr
  icases Hsr with ⟨%d2, %al2, %dd2, %hd2, #Hsch, Hhalf, -, #Hdd2, Hpath, #Hbf⟩
  have hd2' : d2 = d := srvBkTie_inj d2 d (hd2.symm.trans hBT)
  subst d2
  have hq : srvOpenQ B.E.authMode = (1 : Qp).half := by rw [hBam]; rfl
  rw [hq]
  -- the apply thread's KV resources
  have hK := srvApplyKVM_C (GF := GF) AuthC.off C.s B.E C.γw x sa
  simp only [AuthC.isOn, srvApplyKVM_false] at hK
  ihave HKV := hK.2 $$ HKV
  iunfold srvApplyKV at HKV
  icases HKV with ⟨%ua, -, -, Hakv, Hbo, -, -, -, -⟩
  iunfold apply.applyKV at Hakv
  icases Hakv with ⟨%p, -, -, Hko, Hcmo⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨⟨%c, Hws⟩, Hkb, -, -⟩
  iunfold apply.kvBk at Hkb
  icases Hkb with ⟨%B2, HmB, -, HtB⟩
  ihave %HB2 : ⌜B2 = d⌝ $$ [HtB]
  · rw [hBT]; iunfold srvBkTie at HtB; iexact HtB
  subst B2
  iunfold apply.cmpOwn at Hcmo
  icases Hcmo with ⟨Hop, Hcr⟩
  -- the writer's compaction revision, the apply thread's
  iunfold srvApi.wSt at Hws
  icases Hws with ⟨Hws1, Hws2⟩
  iunfold srvApi.crOwn at Hcr
  icombine Hws2 Hcr gives %Hcc
  have hcx : c = x.crev := Hcc.2
  subst hcx
  ihave Hws : srvApi.wSt B.E.γs x.log x.crev $$ [Hws1 Hws2]
  · iunfold srvApi.wSt; iframe Hws1 Hws2
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d3, %hd3, Hbe, Hg, -, HbPl, Hrt⟩
  have hd3' : d3 = d := srvBkTie_inj d3 d (hd3.symm.trans hBT)
  subst d3
  iunfold backend.bkRPool at HbPl
  icases HbPl with ⟨-, HoPs⟩
  iunfold apply.bkRT at Hrt
  icases Hrt with ⟨-, HoA⟩
  rw [hBbe]
  -- the monitor's read token's open share (H2)
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc1, Hlc2⟩
  ihave #Hrf' := Hrf
  iunfold srvRunFieldsAt at Hrf'
  icases Hrf' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hgok⟩
  iunfold srvGoAttachOk at Hgok
  icases Hgok with ⟨%gch, %gc, -, -, -, #Hginv, -⟩
  imod stop_monitorRT C.E C.wt γg d $$ [Hlc1 Hg Hwd] with ⟨Hg, HoM⟩
  · iframe Hlc1 Hpool Hginv Hreg Hwd Hg
  -- the census (gap 4): the slot's reader tokens with the compactor's, the caller's 128, the apply
  -- thread's, every one of the store's
  iunfold srvRunFieldsAt at Hrf
  icases Hrf with ⟨-, -, -, -, -, -, -, #Hcpa, #Hcpok, -⟩
  icases srvStop.census_readers hRS C.s C.E v.compactor hcmp $$ [Hcsp Hcpa] with ⟨%hcp, Hcr0⟩
  · iframe Hcsp Hcpa
  iunfold srvStopReaders at Hrds
  rw [hBγ] at *
  ihave Hrs := (hRS C.E.γ (srvKeepRdN + 1) (64 + 64)).2 $$ [Hcr0 Hrds]
  · iframe Hcr0 Hrds
  ihave Hrs := (hRS C.E.γ (srvKeepRdN + 1 + (64 + 64)) 1).2 $$ [Hrs Hrdk]
  · iframe Hrs Hrdk
  rw [srvKeepRdN_total]
  ihave Hwand := stop_census_open hCR C.E.γ d 1 (B.E.Pk d) $$ [HoA HoM Hhalf HoPs]
  · iframe HoA HoM Hhalf HoPs
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
  iunfold srvStopChans at Hsch
  icases Hsch with ⟨#HB, #HSC⟩
  ihave #Hnh := isBackendNH_of_hooksAt d.γB d.P (mvcc.api.mvccW d.gx)
    (batchLockInv B.γ (metaTM d.γB d.P)) d.be (storage.hooksIface bh) $$ [HB HhkAt]
  · iframe #
  iunfold isServerCI at HCI
  icases HCI with ⟨-, #Hci, #Hinv⟩
  ihave #Hreq := commitReq_freeze hOn hSave hPut hUR hID hName hSafe B.γ C.ci d.γB d.P
    (mvcc.api.mvccW d.gx) d.be bh lgh hcK hhP st hp.1.1
    $$ [Hspkg Hbpkg Hschpkg Hcipkg Hbhk Hnh HB Hci Hinv]
  · iframe #
  -- the KV at the store's handle
  icases Hkv with ⟨%kv, #Hkva, #HisKV, %HkvE⟩
  -- `s.Cleanup()`
  iapply wp_fupd
  wp_apply hCl C.s lp kv C.E.γ 1 (B.E.Pk d) stl iprop(True) C.E.γbe d
      (DFrac.own (1 : Qp).half.half.half) (mvcc.api.mvccW d.gx)
      (batchLockInv B.γ (metaTM d.γB d.P)) v.compactor (applyThread B.γ st) (freezeY B.γ st)
    $$ [Hlst Hop Hrs HmB Hbr Hbe Hg Hwand Hst]
    as ⟨-, HmB, -, -, -, HY, %D, Hsv, Hfile⟩
  · rw [hcp]
    iframe Hlpa Hlst Hkva HisKV Hop Hrs HmB Hstla Hacl Hbr Hbe Hg HB HSC Hwand Hst Hreq Hcpa Hcpok
  -- the stopped backend's data: the image of the applied log at `ai`
  have hci : ciEff B.γ st.k = ai := by
    obtain ⟨-, -, hJ, hle, -⟩ := hp
    rcases hJ with h | ⟨-, h⟩
    · rw [h, hc00] at hle ⊢; word
    · word
  have hRB : ∀ n ∈ restBuckets, d.P.RB n = true := fun n hn => by
    simp [mvcc.KBReal.P, hn]
  ihave ⟨%f, %Hfb, HRs, -, -, -⟩ := srvRestRp_open B.E C.γr G rG $$ HRs
  rw [hRO]
  iunfold srvRestOwnH at HRs
  icases HRs with ⟨Hro, -⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrc, Hrn', -, -⟩
  -- the image's buckets are the model's at `G` (inside the window: the replay changes only the
  -- members)
  rw [restLeasesWith_bk_congr f (srvIds B.E (appliedTable C.γr G).ids) _
    (restModel C.γr.kv.c0 C.γr.raft.raft.boot (C.γr.raft.pre ++ G)) hbk]
  -- the store's part (`mvccImage_stop.law`, with the apply thread's whole share)
  ihave HmB : mvcc.api.mvccBackend C.E.γ 1 (mvcc.api.etcdStorage d)
      (batchLockInv B.γ (metaTM d.γB d.P)) $$ [HmB]
  · rw [← hPk]; iexact HmB
  imod srvApi.stopImageG Hp Hr hStop B.E.Nx B.E.Cp B.E.kv C.E.γ B.E.γs x.log x.crev d
    (batchLockInv B.γ (metaTM d.γB d.P)) D
    $$ [Hks Hws HmB Hsv] with ⟨-, -, Hsv, %Hre, %u, #Him⟩
  · iframe Hks Hws HmB Hsv
  -- the server's parts (the window's observation on the stopped lock's pieces)
  ihave %hobs := stop_obs B.γ B.E C.γr ai G d f st (mvcc.api.mvccW d.gx) D hcK hRB hci Hfb
    $$ [HY Hrc Hrn' Hsv]
  · iframe HY Hrc Hrn' Hsv
  ihave #Hmi : mergedImgM (GF := GF) B.E.authMode B.E.lg C.γr ai G x.log x.crev D $$ []
  · iunfold mergedImgM
    isplitr
    · ipureintro; exact ⟨hobs.1, hobs.2.1, hobs.2.2, Hre⟩
    iexists u; iexact Him
  -- the KV names' start values
  have ekr : kvRunM (GF := GF) AuthC.off.isOn C.γr C.ai₀ C.c₀ G x sa = kvRun C.γr C.ai₀ C.c₀ G x :=
    rfl
  rw [ekr]
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka, %hk0⟩
  iunfold isServerApplyAll at Hsa
  icases Hsa with ⟨%wt0, %msc, %sc, -, -, -, -, -, -, -, -, -, -, -, %Hlog0⟩
  have hc0' : C.γr.kv.c0 = W64 0 := hk0.1.trans hc00
  imod stop_imageAt C.s B.γ C.ci B.TM B.E C.ρ C.γr ai G x D hBam ⟨hc0', Hlog0⟩ $$ [HsrvI Hka]
    with ⟨Hka, %himg, %u', #Him'⟩
  · iframe HsrvI Hka Hmi
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
  have hai : uint.nat ai = G.length := by
    have h1 := hp.2.2.2.2.2.1; rw [hai0] at h1; word
  -- the bootstrap log applied (the stop request's evidence)
  ihave #Hrl' := Hrl
  iunfold srvRaftLogInv at Hrl'
  icases Hrl' with ⟨-, #Hcl, -⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, %HbL, -⟩
  iunfold srvBootApplied at Hba
  icases Hba with ⟨%vb, #Hvb, %hvb⟩
  rw [hρ] at hvb
  iunfold appliedAtLeast at Hvb
  iunfold srvAppliedOwn at Hao
  icases Hao with ⟨Hao, -⟩
  rw [hρ]
  ihave %hle := monoNatLbOwn_valid C.γr.applied _ _ _ $$ Hao Hvb
  have hboot : C.γr.raft.raft.boot.length ≤ G.length := by rw [← hai]; omega
  -- the configuration point
  imod stop_imageConf C.γr.raft C.γr.kv G D ai hpre' hai hc0' hboot himg.1
    $$ [Hrl HA] with ⟨#Hconf, %hconf⟩
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
  iexists S, σ, ai, G, D, Membership.simple C.γr.raft.raft.cfg, M
  rw [hρ] at *
  iunfold srvFiles
  rw [← hwd, ← hγ]
  have h1 := hp.2.2.2.2.2.1
  have h2 := hσ.2.1
  have h3 := hσ.2.2
  rw [hpre] at h2 h3
  ihave Hσc := wal.stopImage_intro _ S σ ai hσ.1 (by simp at h2; omega) (by simp at h3; omega)
    $$ Hσc
  iframe Hvac Hrst HA HM Hpath Hfh Hconf Hw Hσc
  isplitr
  · ipureintro; exact ⟨rfl, hc0'⟩
  isplitr
  · ipureintro
    exact ⟨by rw [hk0.2]; exact h1, himg⟩
  isplitr
  · iexists u'; iexact Him'
  ipureintro
  exact ⟨by rw [HbL]; omega, hconf⟩

end proof

end EtcdGrove
end Perennial
