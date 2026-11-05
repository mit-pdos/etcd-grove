/-
**`KV.Compact.contract` over the store's compaction** (stage 2, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `mvcc.store.Compact.core`: `store.Compact`'s internal statement (the compaction right, the hook's
  context `lockCtxM`, the caller's ghost step `cmpCb` with its excluder `S`, the commit request), which
  `store__Compact.lean` proves from its callees and turns into the contract.
* `compact_cmpCb`: the client's atomic update is the ghost step (`MvccReachable.compact`).
* `store.Compact.wp_api`: the contract's body at a store `s` from the core: the open token at the
  store's location and current names, the backend share's token the excluder, its names the right's,
  its batch lock's invariant the store's; the hook's contract set (`csContract`) or `nil` (the unset
  arm at the hook frozen at `nil`, `DFrac.discard`: §4.8, a store without a hook).
* `watchableStore.Compact.wp_proof`: the promoted method, `store.Compact`'s at the inner store.
* `restore()`'s excluders (`wr_restoring_excl`, `wr_frozen_excl`, the latter by `slotF_excl_M1`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M1Placeholders
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section core
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.Compact(trace, rev)`, the store's internal statement** (the core of `KV.Compact.contract`,
2026-11-06; until then `store.Compact.spec` itself): with the compaction right at the store's
compaction revision `c` (`compactRightR`), under the critical section's context by the post-lock
hook's state (`lockCtxM`), `trace ≠ nil`, the store's backend supporting the compaction
(`storeCmp`), a revision past `0`, the caller's ghost step `cmpCb` with its excluder `S`
(`updateCompactRev`'s) and its commit request `X` to `Y` (`ForceCommit`'s), under `s.mu` held
exclusively: above `c` and a revision of the committed log, the right at `rev`, `Post`, `Fok`, `Y`,
the job's channel; at or below `c`, `ErrCompacted`, the barrier's channel, `Pre`, `Fce`, `X`; past the
committed log, `ErrFutureRev`, no channel, `Pre`, `Ffr`, `X`. The reader token and the hook's context
are given back in every case. -/
abbrev mvcc.store.Compact.core : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF)
    (hk : Option val) (dq : DFrac) (Pre Q Post S Fok Fce Ffr X Y : IProp GF) (te : Bool),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c → 1 ≤ sint.Z rev →
  (mvcc.slotF γ ∗ S ⊢ False) → (ghostVar γ.wr 1 () ∗ mvcc.slotFr γ ∗ S ⊢ False) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.compactRightR s γ c ∗
      mvcc.crevPermAt γ (sint.Z rev) ∗ mvcc.lockCtxM γ P hk Pre Q Post dq ∗
      traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb ∗ S ∗
      mvcc.cmpCb γ c c (sint.Z rev) Fok Fce Ffr ∗ X ∗ mvcc.storeReq γ X Y }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk dq ∗ S ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) ∗
        Fok ∗ Y) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True) ∗ Fce ∗ X) ∨
      (⌜ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ Ffr ∗ X)) }}


/-! ## `KV.Compact.contract` at `*store` and `*watchableStore` (2026-11-06)

Over the core (`mvcc.store.Compact.spec`): the handle's store (`isMvccPlain`; the watchable store's
inner one), the open token at the store's current names (`mvccOpen`: the compaction right, its
quarter of the API's compaction authority, the reader token and the supply), the backend share
(`mvccBackend`: its token the excluder `S`, the names agreeing with the right's, the batch lock's
invariant the store's `hookP`), the hook's contract (`hookRun`: set, `csContract`; `nil`, the unset
arm at the frozen share of the hook at `nil`, §4.8), the backend's commit request, and the client's update made
the ghost step (`compact_cmpCb`). -/

/-- A compaction's channel, tracked, can be received on (`compactChanOk`). -/
theorem mvcc.compactChan_ok (ch : GoChan) (Qc : IProp GF) :
    mvcc.compactChan ch Qc ⊢ mvcc.api.compactChanOk ch := by
  iintro #H
  iunfold mvcc.api.compactChanOk
  iunfold mvcc.compactChan at H
  icases H with ⟨%γc, #Hb⟩
  iintro !> %Φ !> - HΦ
  iapply (chan.wp_receive (V := Unit) ch γc)
  · iapply ownBroadcastChan_is_chan $$ Hb
  iintro ⟨Hlc, -⟩
  -- the continuation's later stripped with a credit, inside `recvAu`'s first update
  iunfold recvAu
  imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc HΦ with HΦ
  ihave HR : recvAu (GF := GF) γc Unit (fun v ok => Φ (PairV #v #ok)) $$ [HΦ]
  · iapply broadcast_chan_receive _ _ _ _ _ $$ Hb
    iintro ⟨-, -⟩
    iapply HΦ
    itrivial
  iunfold recvAu at HR
  iexact HR

theorem mvcc.writerN_sub : (⊤ \ ↑mvcc.api.mvccN : CoPset) ⊆ ⊤ \ ↑mvcc.writerN := by
  intro p hp
  rw [CoPset.in_diff] at hp ⊢
  exact ⟨hp.1, fun h => hp.2 (nclose_subseteq mvcc.api.mvccN "writer" p h)⟩

/-- **The client's compaction update is the store's ghost step** (`cmpCb`, at `cp = c`): success, the
view (the client's half, `s.revMu`'s and the writer's quarters) and the compaction authority (the
client's half, `s.revMu`'s and the right's quarters) moved to `rev`, the state compacted
(`MvccReachable.compact`: nothing pending, the writer's part at `none`); at the errors, the state
read. -/
theorem mvcc.compact_cmpCb (γ0 : mvcc.StoreNames) (p : mvcc.PhysNames) (c rev : Int) (h1 : 1 ≤ rev)
    (Q : mvcc.api.MvccState → IProp GF) :
    mvcc.api.crevAuth γ0.api (1 : Qp).half.half c ∗
      iprop(AU <{ ∃∃ (σ : mvcc.api.MvccState), mvcc.api.mvccStateI γ0.api σ }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
        <{ mvcc.api.mvccStateI γ0.api (if σ.crev < rev ∧ rev ≤ (σ.rev : Int)
              then σ.compactTo rev else σ), COMM Q σ }>) ⊢
    mvcc.cmpCb (γ0.withPhys p) c c rev
      iprop(mvcc.api.crevAuth γ0.api (1 : Qp).half.half rev ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜σ.crev < rev ∧ rev ≤ (σ.rev : Int)⌝)
      iprop(mvcc.api.crevAuth γ0.api (1 : Qp).half.half c ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜rev ≤ σ.crev⌝)
      iprop(mvcc.api.crevAuth γ0.api (1 : Qp).half.half c ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜(σ.rev : Int) < rev⌝) := by
  generalize hγ : (γ0.withPhys p) = γ
  have hapi : γ.api = γ0.api := by rw [← hγ]; rfl
  rw [← hapi]
  iintro ⟨Hcr, Hau⟩
  iunfold mvcc.cmpCb
  isplit
  · -- success
    iintro %L %Hf ⟨HX, HYa, HYp⟩
    obtain ⟨hlt, -, hrl⟩ := Hf
    ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvcc.api.mvccN) (Eo2 := ⊤ \ ↑mvcc.writerN)
      mvcc.writerN_sub $$ Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvcc.api.mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach⟩
    iunfold mvcc.slotX at HX
    iunfold mvcc.api.revMuAbs at HX
    icases HX with ⟨HXa, HXc⟩
    ihave %Hag := mvcc.api.absPart_agree γ.api _ _ _ _ _ _ $$ [Ha HXa]
    · iframe Ha HXa
    obtain ⟨hlog, hcrev⟩ := Hag
    ihave %Hpn := mvcc.api.pndPart_agree γ.api _ _ _ _ $$ [Hp HYp]
    · iframe Hp HYp
    have hrev : rev ≤ (σ.rev : Int) := by
      unfold mvcc.api.MvccState.rev; rw [hlog]; omega
    have hcond : σ.crev < rev ∧ rev ≤ (σ.rev : Int) := ⟨by rw [hcrev]; exact hlt, hrev⟩
    -- the view: the writer's and the lock's quarters joined, then updated with the client's half
    have hq := (mvcc.api.absPart_fractional (GF := GF) γ.api L c).fractional
      (1 : Qp).half.half (1 : Qp).half.half
    rw [Qp.half_add_half] at hq
    ihave HXY := hq.2 $$ [HXa HYa]
    · rw [← hlog, ← hcrev]; iframe HXa HYa
    imod mvcc.api.absPart_update γ.api (1 : Qp).half (1 : Qp).half (Qp.half_add_half 1) σ.log L L
      σ.crev c rev $$ [Ha HXY] with ⟨Ha, HXY⟩
    · rw [← hlog, ← hcrev]; iframe Ha HXY
    have hq' := (mvcc.api.absPart_fractional (GF := GF) γ.api L rev).fractional
      (1 : Qp).half.half (1 : Qp).half.half
    rw [Qp.half_add_half] at hq'
    icases hq'.1 $$ HXY with ⟨HXa, HYa⟩
    -- the authority: the client's half, the lock's quarter and the right's quarter, raised
    have hc := (mvcc.api.crevAuth_fractional (GF := GF) γ.api c).fractional
      (1 : Qp).half.half (1 : Qp).half.half
    rw [Qp.half_add_half] at hc
    have hc2 := (mvcc.api.crevAuth_fractional (GF := GF) γ.api c).fractional
      (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at hc2
    ihave Hc1 := hc.2 $$ [HXc Hcr]
    · iframe HXc Hcr
    ihave Hc1 := hc2.2 $$ [Hcc Hc1]
    · rw [← hcrev]; iframe Hcc Hc1
    imod mvcc.api.crevAuth_update γ.api c rev (by omega) $$ Hc1 with ⟨Hc1, -⟩
    have hc' := (mvcc.api.crevAuth_fractional (GF := GF) γ.api rev).fractional
      (1 : Qp).half (1 : Qp).half
    rw [Qp.half_add_half] at hc'
    have hc'' := (mvcc.api.crevAuth_fractional (GF := GF) γ.api rev).fractional
      (1 : Qp).half.half (1 : Qp).half.half
    rw [Qp.half_add_half] at hc''
    icases hc'.1 $$ Hc1 with ⟨Hcc, Hc1⟩
    icases hc''.1 $$ Hc1 with ⟨HXc, Hcr⟩
    imod Hcommit $$ [Ha Hp Hcc Hnl] with HQ
    · simp only [hcond, and_self, ↓reduceIte]
      iunfold mvcc.api.mvccStateI
      have hnl : (σ.compactTo rev).notifiedLog = σ.notifiedLog := by
        unfold mvcc.api.MvccState.notifiedLog mvcc.api.MvccState.compactTo; rfl
      rw [hnl]
      simp only [mvcc.api.MvccState.compactTo]
      rw [hlog]
      iframe Ha Hp Hcc Hnl
      ipureintro
      rw [← hlog]
      exact mvcc.api.MvccReachable.compact σ rev Hreach Hpn h1 hcond.1 hcond.2
    imodintro
    iframe HYa HYp Hcr
    isplitl [HXa HXc]
    · iunfold mvcc.slotX; iunfold mvcc.api.revMuAbs; iframe HXa HXc
    iexists σ; iframe HQ; ipureintro; exact hcond
  isplit
  · -- `ErrCompacted`
    iintro %L %Hle HX
    ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvcc.api.mvccN) (Eo2 := ⊤)
      (fun _ _ => CoPset.mem_full) $$ Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvcc.api.mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach⟩
    iunfold mvcc.slotX at HX
    iunfold mvcc.api.revMuAbs at HX
    icases HX with ⟨HXa, HXc⟩
    ihave %Hag := mvcc.api.absPart_agree γ.api _ _ _ _ _ _ $$ [Ha HXa]
    · iframe Ha HXa
    obtain ⟨-, hcrev⟩ := Hag
    have hn : ¬ (σ.crev < rev ∧ rev ≤ (σ.rev : Int)) := by omega
    imod Hcommit $$ [Ha Hp Hcc Hnl] with HQ
    · simp only [hn, ↓reduceIte]
      iunfold mvcc.api.mvccStateI
      iframe Ha Hp Hcc Hnl
      ipureintro; exact Hreach
    imodintro
    iframe Hcr
    isplitl [HXa HXc]
    · iunfold mvcc.slotX; iunfold mvcc.api.revMuAbs; iframe HXa HXc
    iexists σ; iframe HQ; ipureintro; omega
  · -- `ErrFutureRev`
    iintro %L %Hf HX
    ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvcc.api.mvccN) (Eo2 := ⊤)
      (fun _ _ => CoPset.mem_full) $$ Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvcc.api.mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach⟩
    iunfold mvcc.slotX at HX
    iunfold mvcc.api.revMuAbs at HX
    icases HX with ⟨HXa, HXc⟩
    ihave %Hag := mvcc.api.absPart_agree γ.api _ _ _ _ _ _ $$ [Ha HXa]
    · iframe Ha HXa
    obtain ⟨hlog, -⟩ := Hag
    have hlt : (σ.rev : Int) < rev := by
      unfold mvcc.api.MvccState.rev; rw [hlog]; omega
    have hn : ¬ (σ.crev < rev ∧ rev ≤ (σ.rev : Int)) := by omega
    imod Hcommit $$ [Ha Hp Hcc Hnl] with HQ
    · simp only [hn, ↓reduceIte]
      iunfold mvcc.api.mvccStateI
      iframe Ha Hp Hcc Hnl
      ipureintro; exact Hreach
    imodintro
    iframe Hcr
    isplitl [HXa HXc]
    · iunfold mvcc.slotX; iunfold mvcc.api.revMuAbs; iframe HXa HXc
    iexists σ; iframe HQ; ipureintro; exact hlt

/-- `restore()`'s excluder, `s.mu`'s deposit ghost whole: the restoring state holds it too. -/
theorem mvcc.wr_restoring_excl (γ : mvcc.StoreNames) :
    ghostVar (GF := GF) γ.wr 1 () ∗ mvcc.slotFr γ ∗ ghostVar γ.wr 1 () ⊢ False := by
  iintro ⟨H1, -, H2⟩
  ihave %Hv := ghostVar_valid_2 γ.wr () 1 () 1 $$ H1 H2
  exact absurd Hv.1 (Qp_one_add_not_le _)

/-- `restore()`'s excluder of the frozen state: none yet (the placeholder `slotF_excl_M1`;
M1-REPLACE: `KV.Restore.contract`, the restorer's share of the backend token). -/
theorem mvcc.wr_frozen_excl (γ : mvcc.StoreNames) :
    mvcc.slotF (GF := GF) γ ∗ ghostVar γ.wr 1 () ⊢ False := by
  iintro ⟨HF, -⟩
  iapply (mvcc.slotF_excl_M1 γ)
  isplitl [HF]
  · iexact HF
  · iempintro


/-- `restore`'s and a writer's restoring state excluded by a share of the backend token. -/
theorem mvcc.slotFr_share_excl (γ : mvcc.StoreNames) (q : Qp) :
    ghostVar (GF := GF) γ.wr 1 () ∗ mvcc.slotFr γ ∗ mvcc.api.shareTok γ.api q ⊢ False := by
  iintro ⟨-, HFr, HS⟩
  icases (mvcc.slotFr_some (γ := γ) rfl).1 $$ HFr with HFr
  iapply mvcc.api.shareTok_excl γ.api q $$ [HFr HS]
  iframe HFr HS

/-- **`KV.Compact.contract` at `*store`**, from the core: the handle a plain store's (its location
and permit `True`). -/
theorem mvcc.store.Compact.wp_api (hcore : mvcc.store.Compact.core (GF := GF) (hG := hG)) :
    mvcc.api.store.Compact.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) trace te rev q B P f Pre Q' Post X Y Q
  iintro %Φ ⟨#Hpkg, Hmv, Hopen, Htt, %htr, %hpos1, Htrc, HB, #Hhk, HX, #Hreq, HPre, Hrun, Hupd, HAU⟩
    HΦ
  iunfold mvcc.api.isMvcc at Hmv
  icases Hmv with #(Hmv | Hmv)
  rotate_left 1
  · iunfold mvcc.api.isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold mvcc.api.isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, #Hperm⟩
  have hs : s = s' := mvcc.mkOk_loc_inj _ Hk
  cases hs
  iunfold mvcc.api.mvccState at HAU
  -- the open token, at the store's location and current names
  iunfold mvcc.api.mvccOpen at Hopen
  icases Hopen with ⟨%s2, %p, %c, #Hloc2, Hright, Hcra, HRT, #Hsup, %hc⟩
  ihave %Hss := mvcc.api.locIs_agree _ _ _ $$ [Hloc Hloc2]
  · isplitl
    · iexact Hloc
    · iexact Hloc2
  cases Hss
  -- the backend share: its names are the right's
  iunfold mvcc.api.mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp⟩
  obtain ⟨hpk, hcm, rfl⟩ := Hd
  icases (mvcc.compactRightR_iff s ((γ : mvcc.StoreNames).withPhys p) c).1 $$ Hright with
    ⟨Hcr, Hq, %o, ⟨Hfs, #Hsc, Hstc, Htok⟩, #Hstop⟩
  icases mvcc.fieldShareAt_cur s ((γ : mvcc.StoreNames).withPhys p) _ o $$ Hfs with ⟨Hcur, Hfsb⟩
  ihave %Hv := mvcc.curAt_agree ((γ : mvcc.StoreNames).withPhys p) ((γ : mvcc.StoreNames).withPhys p')
      rfl _ _ o o' $$ [Hcur Hcur']
  · isplitl [Hcur]
    · iexact Hcur
    · iexact Hcur'
  obtain ⟨-, hp⟩ := Hv
  have hp' : p = p' := hp
  subst hp'
  ihave Hfs := Hfsb $$ Hcur
  ihave Hright : mvcc.compactRightR (GF := GF) s ((γ : mvcc.StoreNames).withPhys p) c
      $$ [Hcr Hq Hfs Hstc Htok]
  · iapply (mvcc.compactRightR_iff s ((γ : mvcc.StoreNames).withPhys p) c).2
    iframe Hcr Hq
    iexists o
    iframe Hfs Hsc Hstc Htok Hstop
  -- the store's compaction facts at its current names
  have hkb : ((γ : mvcc.StoreNames).withPhys p).kb = some d := hpk
  have hcmp : mvcc.storeCmp ((γ : mvcc.StoreNames).withPhys p) := by
    show mvcc.kbCmpM ((γ : mvcc.StoreNames).withPhys p).kb
    rw [hkb]; exact hcm
  ihave #HpR : mvcc.crevPermAt (GF := GF) ((γ : mvcc.StoreNames).withPhys p) (sint.Z rev) $$ []
  · iapply mvcc.crevPermAt_of _ (fun _ => iprop(True))
    isplitl
    · iapply (mvcc.crevPermIs_cperm (γ : mvcc.StoreNames) ((γ : mvcc.StoreNames).withPhys p) rfl
        (fun _ => iprop(True)))
      iexact Hperm
    · iintro !>; itrivial
  ihave #HreqS : mvcc.storeReq (GF := GF) ((γ : mvcc.StoreNames).withPhys p) X Y $$ []
  · simp only [mvcc.storeReq, mvcc.StoreNames.withPhys_kb, hpk]
    iunfold mvcc.kbReq
    iunfold mvcc.bkReq
    iright
    iexists (mvcc.api.mvccW d.gx), P
    iframe Hbk Hreq
  ihave #Hsup' : mvcc.kbWTSupplyM (GF := GF) ((γ : mvcc.StoreNames).withPhys p).kb $$ []
  · rw [mvcc.StoreNames.withPhys_kb]; iexact Hsup
  -- the hook's context: set, the hook's facts and the caller's contract; nil, the unset arm
  ihave ⟨%hk, %dq, Hctx⟩ : (∃ (hk : Option val) (dq : DFrac),
      mvcc.lockCtxM (GF := GF) ((γ : mvcc.StoreNames).withPhys p) P hk Pre Q' Post dq)
      $$ [HPre Hrun Hupd]
  · by_cases hf : f = func.nil
    · iexists none, DFrac.discard
      rw [mvcc.lockCtxM_none]
      iunfold mvcc.api.hookRun at Hrun
      simp only [hf, ↓reduceIte]
      iframe Hhp HPre
      isplitr
      · rw [mvcc.StoreNames.withPhys_kb, hpk]
        iunfold mvcc.kbHookNilAt
        rw [← hf]; iexact Hhk
      iintro HPP
      imod Hrun $$ HPP with HQ'
      iapply Hupd $$ HQ'
    · iexists (some #f), DFrac.discard
      rw [mvcc.lockCtxM_some]
      iunfold mvcc.api.hookRun at Hrun
      simp only [hf, ↓reduceIte]
      icases Hrun with #Hrun
      isplitr
      · iunfold mvcc.hookOk
        iframe Hhp
        iunfold mvcc.hookFn
        rw [mvcc.StoreNames.withPhys_kb, hpk]
        iunfold mvcc.kbHookIs
        iunfold mvcc.bkHookIs
        iexists f
        iframe Hhk
        ipureintro; exact ⟨rfl, hf⟩
      iunfold mvcc.csContract
      iframe HPre Hrun Hupd
  -- the client's update, the store's ghost step
  ihave Hcb := mvcc.compact_cmpCb γ p c (sint.Z rev) hpos1 Q $$ [Hcra HAU]
  · iframe Hcra HAU
  iapply (hcore s ((γ : mvcc.StoreNames).withPhys p) trace rev c P hk dq Pre Q' Post
      (mvcc.api.shareTok (γ : mvcc.StoreNames).api q)
      iprop(mvcc.api.crevAuth (γ : mvcc.StoreNames).api (1 : Qp).half.half (sint.Z rev) ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)⌝)
      iprop(mvcc.api.crevAuth (γ : mvcc.StoreNames).api (1 : Qp).half.half c ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜sint.Z rev ≤ σ.crev⌝)
      iprop(mvcc.api.crevAuth (γ : mvcc.StoreNames).api (1 : Qp).half.half c ∗
        ∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜(σ.rev : Int) < sint.Z rev⌝)
      X Y te htr hcmp hc hpos1
      (mvcc.slotF_share_excl (γ := (γ : mvcc.StoreNames).withPhys p) rfl q)
      (mvcc.slotFr_share_excl ((γ : mvcc.StoreNames).withPhys p) q))
    $$ [Hright Hctx Htrc HRT HF Hcb HX] [-]
  · rw [mvcc.isStore_withPhys]
    iframe #
    iframe Hright Hctx Htrc HRT HF Hcb HX
  inext
  iintro %ch %err ⟨Htrc, HRT, -, HF, Hres⟩
  ihave HB : mvcc.api.mvccBackend (GF := GF) γ q ⟨d.γB, d.P, d.be⟩ P $$ [HF Hcur']
  · iunfold mvcc.api.mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp
    ipureintro; exact ⟨hpk, hcm, rfl⟩
  icases Hres with (⟨⟨%Herr, %Hlt⟩, Hright, #Hlb, HPost, #Hch, ⟨Hcra, %σ, HQ, %Hσ⟩, HYB⟩ |
    ⟨%Hle, ⟨%ec, #Hec, %Herr⟩, Hright, HPre, #Hch, ⟨Hcra, %σ, HQ, %Hσ⟩, HXB⟩ |
    ⟨%Hch, ⟨%ef, #Hef, %Herr⟩, Hright, HPre, ⟨Hcra, %σ, HQ, %Hσ⟩, HXB⟩)
  · iapply HΦ
    iframe Htt Htrc HB
    isplitl [Hright Hcra HRT]
    · iunfold mvcc.api.mvccOpen
      iexists s, p, (sint.Z rev)
      iframe Hloc Hright Hcra HRT Hsup
      ipureintro; omega
    iexists σ
    iframe HQ
    ileft
    iframe HPost HYB
    isplitr
    · ipureintro; exact ⟨Herr, Hσ⟩
    iapply mvcc.compactChan_ok; iexact Hch
  · subst Herr
    iapply HΦ
    iframe Htt Htrc HB
    isplitl [Hright Hcra HRT]
    · iunfold mvcc.api.mvccOpen
      iexists s, p, c
      iframe Hloc Hright Hcra HRT Hsup
      ipureintro; exact hc
    iexists σ
    iframe HQ
    iright
    ileft
    iframe HPre HXB Hec
    isplitr
    · ipureintro; exact Hσ
    iapply mvcc.compactChan_ok; iexact Hch
  · subst Herr
    iapply HΦ
    iframe Htt Htrc HB
    isplitl [Hright Hcra HRT]
    · iunfold mvcc.api.mvccOpen
      iexists s, p, c
      iframe Hloc Hright Hcra HRT Hsup
      ipureintro; exact hc
    iexists σ
    iframe HQ
    iright
    iright
    iframe HPre HXB Hef
    ipureintro; exact ⟨Hσ, Hch⟩

/-- **`KV.Compact.contract` at `*watchableStore`**: the promoted method, the inner store's
(`store.Compact.spec` at it: the handle's inner store, its location and permit). -/
theorem mvcc.watchableStore.Compact.wp_proof (h : mvcc.api.store.Compact.spec (GF := GF)) :
    mvcc.api.watchableStore.Compact.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) trace te rev q B P f Pre Q' Post X Y Q
  wp_start as ⟨Hmv, Hrest⟩
  iunfold mvcc.api.isMvcc at Hmv
  icases Hmv with #(Hmv | Hmv)
  · iunfold mvcc.api.isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold mvcc.api.isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, #Hws, -, -, #Hloc, #Hperm⟩
  obtain ⟨Hk, hγ⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  ihave #Hws' := Hws
  iunfold mvcc.isWatchableStore at Hws'
  icases Hws' with ⟨%vc, %stc, %rv, %γv, Hws'⟩
  iNamed Hws'
  ihave Hmvs : mvcc.api.isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType store.ty) #st) γ $$ []
  · iunfold mvcc.api.isMvcc
    iintro !>
    ileft
    iunfold mvcc.api.isMvccPlain
    iexists st
    rw [← hγ]
    iframe Hs Hloc Hperm
    ipureintro; rfl
  (try wp_auto)
  wp_apply (h st γ trace te rev q B P f Pre Q' Post X Y Q) $$ [Hrest Hmvs] as %ch %err HQ
  · iframe #; iframe Hmvs; iexact Hrest
  iapply HΦ; iexact HQ

end core

end EtcdGrove
end Perennial
