/-
`mvcc.store.Compact.core` (the store's internal compaction statement) and the compaction callback's
lemmas (`compact_cmpCb`, `slotFr_share_excl`, ...), out of `CmpCb.lean`'s proofs so that
`CompactChan.lean` imports them without the proofs (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply

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
    icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach, #Hrcm⟩
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
      iframe Hrcm; ipureintro
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
    icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach, #Hrcm⟩
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
      iframe Hrcm; ipureintro; exact Hreach
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
    icases Hσ with ⟨Ha, Hp, Hcc, Hnl, %Hreach, #Hrcm⟩
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
      iframe Hrcm; ipureintro; exact Hreach
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

/-- `restore()`'s excluder of the frozen state (2026-11-06; until then the placeholder
`slotF_excl_M1`): the restorer's whole share token, which it holds again after the finish. -/
theorem mvcc.wr_frozen_excl (γ : mvcc.StoreNames) :
    mvcc.slotF (GF := GF) γ ∗ (ghostVar γ.wr 1 () ∗ mvcc.slotFr γ) ⊢ False := by
  iintro ⟨HF, -, HFr⟩
  iunfold mvcc.slotF at HF
  iunfold mvcc.slotFr at HFr
  iapply (mvcc.api.shareTok_excl (GF := GF) γ.api 1) $$ [HF HFr]
  iframe HF HFr

/-- `restore()`'s excluder of the restoring state, with the restorer's token: `s.mu`'s deposit
ghost whole. -/
theorem mvcc.wrFr_restoring_excl (γ : mvcc.StoreNames) :
    ghostVar (GF := GF) γ.wr 1 () ∗ mvcc.slotFr γ ∗ (ghostVar γ.wr 1 () ∗ mvcc.slotFr γ) ⊢ False := by
  iintro ⟨H1, -, H2, -⟩
  ihave %Hv := ghostVar_valid_2 γ.wr () 1 () 1 $$ H1 H2
  exact absurd Hv.1 (Qp_one_add_not_le _)


/-- `restore`'s and a writer's restoring state excluded by a share of the backend token. -/
theorem mvcc.slotFr_share_excl (γ : mvcc.StoreNames) (q : Qp) :
    ghostVar (GF := GF) γ.wr 1 () ∗ mvcc.slotFr γ ∗ mvcc.api.shareTok γ.api q ⊢ False := by
  iintro ⟨-, HFr, HS⟩
  icases (mvcc.slotFr_some (γ := γ) rfl).1 $$ HFr with HFr
  iapply mvcc.api.shareTok_excl γ.api q $$ [HFr HS]
  iframe HFr HS


end core

end EtcdGrove
end Perennial
