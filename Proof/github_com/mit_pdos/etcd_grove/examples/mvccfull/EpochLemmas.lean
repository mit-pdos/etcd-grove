/-
Lemmas of an epoch's streams for `startEpoch` and `endEpoch` (`Streams.lean`'s vocabulary).
Lean-first (no Rocq counterpart).

- The masks: `streamN` outside `mvccN` and the members' namespaces.
- **A new stream's ghost state** (`stream_alloc`): the names around the stream's mvcc name, the
  stream's invariant at `wsStart` (open, no watcher, no cancel), the registrar's halves, the lock's
  half of the registry and both halves of the received responses; **its lock** (`smu_alloc`) at no
  watcher and nothing received.
- **`Close`'s update** (`close_au`): the registrar's half of the closed flag shows the stream open;
  both halves become `true`.
- **A watch on the closed stream** (`watch_closed_au`): with a live share of the incarnation (its
  invariant gives the store's state, unchanged), the stream closed: no registration.
- **A cancel on the closed stream** (`cancel_closed_au`): **not provable** over today's
  `streamInv`; see its docstring.
- **The incarnation's store is a watchable store** (`inc_watchable`): **not provable** from
  today's `isInc`; see its docstring.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StreamLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

theorem regOk'_start : regOk' wsStart (∅ : GMap w64 Reg) [] := by
  refine ⟨fun id wi h => ?_, fun id x h => ?_⟩
  · simp [wsStart] at h
  · simp at h

theorem rcvKnown'_start : rcvKnown' [] (∅ : GMap w64 Reg) := by
  intro r hr; simp at hr

theorem eventlessOk_start : eventlessOk [] (W64 0) :=
  ⟨by decide, Or.inl rfl⟩

theorem streamN_mvccN : (↑streamN : CoPset) ⊆ ⊤ \ ↑mvccN := by
  unfold streamN mvccN
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "mvccfull" ≠ "mvcc") p
    ⟨nclose_subseteq _ _ p hp, h'⟩⟩

theorem streamN_memberN (i : Nat) (E : CoPset) (hE : (↑streamN : CoPset) ⊆ E) :
    (↑streamN : CoPset) ⊆ E \ ↑(memberN i) := by
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  refine ⟨hE p hp, fun h' => ?_⟩
  unfold streamN at hp
  unfold memberN at h'
  exact ndot_ne_disjoint (nroot .@ "mvccfull") (by decide : "stream" ≠ "member") p
    ⟨hp, nclose_subseteq _ _ p h'⟩

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem streamInv_timeless (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (σs : StreamNames) : Timeless (streamInv (GF := GF) σs) := by
  haveI := hpers.2.2.2.2.2.2.1
  unfold streamInv; infer_instance

/-- **A new stream's ghost state** (see the file header). -/
theorem stream_alloc (ι : WsName) :
    wsState (GF := GF) ι wsStart ⊢
      |={⊤}=> ∃ σs : StreamNames, ⌜σs.ws = ι⌝ ∗ inv streamN (streamInv σs) ∗
        ghostVar σs.cl (1 : Qp).half false ∗ ghostVar σs.cn (1 : Qp).half ([] : List w64) ∗
        ghostMapAuth σs.reg (1 : Qp).half (∅ : GMap w64 Reg) ∗
        ghostVar σs.rcv (1 : Qp).half ([] : List WResp) ∗
        ghostVar σs.rcv (1 : Qp).half ([] : List WResp) := by
  iintro HS
  imod ghostVar_alloc (GF := GF) false with ⟨%gcl, Hcl⟩
  icases (ghostVar_split_half gcl 1 false).1 $$ Hcl with ⟨Hcl1, Hcl2⟩
  imod ghostVar_alloc (GF := GF) ([] : List w64) with ⟨%gcn, Hcn⟩
  icases (ghostVar_split_half gcn 1 ([] : List w64)).1 $$ Hcn with ⟨Hcn1, Hcn2⟩
  imod (ghost_map_alloc_empty (GF := GF) :
    ⊢ |==> ∃ γ, ghostMapAuth (GF := GF) γ 1 (∅ : GMap w64 Reg)) with ⟨%greg, Hreg⟩
  icases (ghostMapAuth_halves greg ∅).1 $$ Hreg with ⟨Hreg1, Hreg2⟩
  imod ghostVar_alloc (GF := GF) ([] : List WResp) with ⟨%grcv, Hrcv⟩
  icases (ghostVar_split_half grcv 1 ([] : List WResp)).1 $$ Hrcv with ⟨Hrcv1, Hrcv2⟩
  let σs : StreamNames := ⟨ι, gcl, greg, grcv, gcn⟩
  imod inv_alloc streamN ⊤ (streamInv (GF := GF) σs) $$ [HS Hcl1 Hreg1 Hcn1] with #Hinv
  · inext
    iunfold streamInv
    iexists wsStart, ∅, []
    rw [show wsStart.closed = false from rfl]
    iframe HS Hcl1 Hreg1 Hcn1
    ipureintro; exact regOk'_start
  imodintro
  iexists σs
  isplitr
  · ipureintro; rfl
  iframe Hinv Hcl2 Hcn2 Hreg2 Hrcv1 Hrcv2

/-- **A new stream's lock** (see the file header). -/
theorem smu_alloc (T : Strm) :
    sF go!"mu" T.s ↦ zero_val sync.Mutex ∗ T.wm ↦$ (∅ : GMap w64 Loc) ∗
        sF go!"order" T.s ↦ (slice.nil : GoSlice) ∗ sF go!"eventless" T.s ↦ W64 0 ∗
        ghostMapAuth T.σs.reg (1 : Qp).half (∅ : GMap w64 Reg) ∗
        ghostVar T.σs.rcv (1 : Qp).half ([] : List WResp) ⊢
      |={⊤}=> sync.isMutex (GF := GF) (sF go!"mu" T.s) (smuInv T) := by
  iintro ⟨Hmu, Hwm, Hord, Hevl, Hreg, Hrcv⟩
  imod monoListLbOwn_nil (GF := GF) T.ep.γh.l (A := HRev) with #Hlb
  iapply sync.init_Mutex (smuInv (GF := GF) T) ⊤ (sF go!"mu" T.s) $$ Hmu
  inext
  iunfold smuInv
  iexists [], ∅, [], W64 0
  iunfold smuBody
  rw [GMap.fmap_empty]
  iframe Hwm Hevl Hreg Hrcv Hlb
  isplitl [Hord]
  · iexists slice.nil, []
    iframe Hord
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; exact ⟨List.nodup_nil, fun id => by simp⟩
  isplitr
  · ipureintro; exact ⟨rcvKnown'_start, eventlessOk_start⟩
  iapply BigSepM.bigSepM_empty.2; itrivial

/-- **`Close`'s update** at the stream's invariant (see the file header). -/
theorem close_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (σs : StreamNames) :
    inv streamN (streamInv σs) ∗ ghostVar σs.cl (1 : Qp).half false ⊢
      AU <{ ∃∃ (S : StreamState), wsState (GF := GF) σs.ws S ∗ ⌜S.closed = false⌝ }> @ ⊤ \ ↑mvccN, ∅
      <{ wsState σs.ws S.close,
        COMM (fun (_ : StreamState) => ghostVar (GF := GF) σs.cl (1 : Qp).half true) S }> := by
  haveI := streamInv_timeless hpers σs
  have Hm := streamN_mvccN
  iintro ⟨#Hinv, Hcl⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold streamInv at Hi
  icases Hi with ⟨%S, %W, %C, HS, HScl, Hreg, Hcn, %Hok⟩
  ihave %Hc := ghostVar_agree σs.cl _ _ _ _ $$ HScl Hcl
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑streamN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
  iframe HS
  isplitr
  · ipureintro; exact Hc
  isplit
  · iintro ⟨HS, -⟩
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg Hcn] with -
    · inext; iunfold streamInv; iexists S, W, C; iframe; ipureintro; exact Hok
    imodintro
    iframe
  · iintro HS
    imod ghostVar_update_halves true σs.cl _ _ $$ HScl Hcl with ⟨HScl, Hcl⟩
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg Hcn] with -
    · inext; iunfold streamInv
      iexists S.close, W, C
      iframe
      ipureintro
      exact Hok
    imodintro
    iexact Hcl

/-- **A watch on the closed stream** (see the file header): the store's state from the
incarnation's invariant (a live share rules out its retired case, `memberInv_live`), unchanged; the
stream closed (`endEpoch`'s half of the closed flag at `true`), so no registration. -/
theorem watch_closed_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (E : Ep) (qw : Qp) (σs : StreamNames) (kk e : List w8) (endk : GoSlice) (st : w64)
    (fs : List (EvM → Bool)) :
    epLive (GF := GF) E qw ∗ inv streamN (streamInv σs) ∗ ghostVar σs.cl (1 : Qp).half true ⊢
      AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState E.ι.kv σ ∗ wsState σs.ws S }>
        @ ⊤ \ ↑mvccN, ∅
      <{ ∀∀ (id : w64) (k : Nat), mvccState E.ι.kv σ ∗
          (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState σs.ws S
           else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb σs.ws k ∗
             wsState σs.ws (S.register id
               ⟨watchRangeOf kk e endk st id, fs, watchLo σ st, k, true⟩)),
        COMM (fun (_ : MvccState) (S : StreamState) (_ : w64) =>
          iprop(epLive (GF := GF) E qw ∗ ghostVar σs.cl (1 : Qp).half true ∗ ⌜S.closed = true⌝))
          σ S id }> := by
  haveI := streamInv_timeless hpers σs
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : Timeless (memberInv (GF := GF) E.ks E.γh E.mp E.m E.ι) := by
    unfold memberInv memberState; infer_instance
  haveI : Persistent (isInc (GF := GF) E.ks E.γh E.i E.mp E.m E.ι E.kv) := by
    haveI := hpers.1; unfold isInc; infer_instance
  have Hmm := memberN_mask E.i
  have Hms := streamN_memberN E.i (⊤ \ ↑mvccN) streamN_mvccN
  iintro ⟨Hlive, #Hinv, Hcl⟩
  iauintro
  unfold atomic_acc
  iunfold epLive at Hlive
  iunfold incLive at Hlive
  icases Hlive with ⟨#Hinc, Hret⟩
  iunfold isInc at Hinc
  icases Hinc with ⟨#Hmi, #Hkv⟩
  iinv Hmi with >Hm Hclm
  icases memberInv_live E.ks E.γh E.mp E.m E.ι qw $$ [$Hret $Hm] with ⟨Hret, Hm⟩
  iunfold memberState at Hm
  icases Hm with ⟨%σ, %b, %Hl, Hσ, Hmrest⟩
  iinv Hinv with >Hi Hclose
  iunfold streamInv at Hi
  icases Hi with ⟨%S, %W, %C, HS, HScl, Hreg, Hcn, %Hok⟩
  ihave %Hc := ghostVar_agree σs.cl _ _ _ _ $$ HScl Hcl
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑mvccN) \ ↑(memberN E.i)) \ ↑streamN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, S
  iframe Hσ HS
  isplit
  · iintro ⟨Hσ, HS⟩
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg Hcn] with -
    · inext; iunfold streamInv; iexists S, W, C; iframe; ipureintro; exact Hok
    imod Hclm $$ [Hσ Hmrest] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b, Hl; iframe
    imodintro
    iframe
    iunfold epLive; iunfold incLive; iunfold isInc
    iframe
    iframe #
  · iintro %id %k ⟨Hσ, HS⟩
    rw [Hc]
    simp only [↓reduceIte]
    icases HS with ⟨-, HS⟩
    imod Hclose2 with -
    imod Hclose $$ [HS HScl Hreg Hcn] with -
    · inext; iunfold streamInv; iexists S, W, C; rw [Hc]; iframe; ipureintro; exact Hok
    imod Hclm $$ [Hσ Hmrest] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b, Hl; iframe
    imodintro
    iframe
    iunfold epLive; iunfold incLive; iunfold isInc
    iframe
    iframe #

/-- **A cancel on the closed stream** (`endEpoch`'s `ws.Cancel(0)`, after the receiver ended):
mvcc's `Cancel` commits `S.cancel id` on a closed stream too, which makes the watcher `id` not
live. **Not provable over today's `streamInv`** (proof `sorry`): `regOk'` keeps every watcher of
the registry live unless the registrar's cancel record `C` has it, and it may join `C` only with its
registry entry cancel-marked (`x.cm`), but that entry's other half is in `s.mu`'s invariant, which
`endEpoch` does not hold (the code takes no lock there). The watcher `0` is the first a stream
registers (mvcc's automatic ids count from `0`), so the case is reachable. Proposed fix
(`Streams.lean`): `streamInv`'s `⌜regOk' S W C⌝` becomes `⌜regOk' S W C⌝ ∨ ∃ rs, wsRecv σs.ws rs`,
`endEpoch` depositing the receiver's `wsRecv` (back from `recvDone`) before the cancel; the receiver,
which holds its `wsRecv`, rules the second branch out (`excl.law`), so `recv_facts` keeps its
statement (with `excl.law` among its hypotheses). -/
theorem cancel_closed_au (σs : StreamNames) (id : w64) :
    inv streamN (streamInv σs) ∗ ghostVar σs.cl (1 : Qp).half true ⊢
      AU <{ ∃∃ (S : StreamState), wsState (GF := GF) σs.ws S }> @ ⊤ \ ↑mvccN, ∅
      <{ wsState σs.ws (S.cancel id),
        COMM (fun (S : StreamState) => iprop(ghostVar (GF := GF) σs.cl (1 : Qp).half true ∗
          ⌜S.closed = true⌝)) S }> := by
  sorry

/-- **An incarnation's store is a watchable store** (`startEpoch`'s `m.kv.NewWatchStream()`: the
contract of `NewWatchStream` is only in `isWatchableKV`, which `shapes.law` gives of
`*watchableStore`; `isMvcc` is sealed and may be a plain store's, whose type has no
`NewWatchStream`). **Not provable from today's `isInc`** (proof `sorry`): it records the store's
handle `kv` and `isMvcc kv ι.kv`, not its type. Proposed fix (`Members.lean`): `isInc` gains
`⌜∃ s : Loc, kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #s⌝`, which `runner.open`
has from `mvcc.api.New.spec`'s post (`RET #(interface.mkOk PW #ws)`). -/
theorem inc_watchable (E : Ep) :
    isInc (GF := GF) E.ks E.γh E.i E.mp E.m E.ι E.kv ⊢
      ⌜∃ s : Loc, E.kv = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #s⌝ := by
  sorry

/-- **A stream after its registrar's end** (`endEpoch`, after `regDone.Wait()`): its handles, the
receiver's wait group, and the registrar's resources back. -/
def epochStream1 (E : Ep) (q : Qp) (s : Loc) : IProp GF :=
  iprop(∃ T : Strm, ⌜T.ep = E ∧ T.s = s⌝ ∗ streamCtx T ∗
    sync.join.ownAdder (sF go!"recvDone" s) (W32 1) iprop(True ∗ ∃ rs, rcvOwn T q.half rs) ∗
    ∃ C, regOwn T q.half C)

/-- An open stream's handles, kept. -/
theorem epochStream_ctx (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (E : Ep) (q : Qp)
    (s : Loc) :
    epochStream (GF := GF) E q s ⊢
      epochStream E q s ∗ ∃ T : Strm, ⌜T.ep = E ∧ T.s = s⌝ ∗ streamCtx T := by
  iintro H
  iunfold epochStream at H
  icases H with ⟨%T, %hT, Hctx, Ha, Hb⟩
  haveI := streamCtx_persistent hpers T
  icases Hctx with #Hctx
  isplitl
  · iunfold epochStream; iexists T; iframe; iframe #; ipureintro; exact hT
  · iexists T; iframe #; ipureintro; exact hT

/-- A stream's handles, kept, after its registrar's end. -/
theorem epochStream1_ctx (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (E : Ep)
    (q : Qp) (s : Loc) :
    epochStream1 (GF := GF) E q s ⊢
      epochStream1 E q s ∗ ∃ T : Strm, ⌜T.ep = E ∧ T.s = s⌝ ∗ streamCtx T := by
  iintro H
  iunfold epochStream1 at H
  icases H with ⟨%T, %hT, Hctx, Ha, Hb⟩
  haveI := streamCtx_persistent hpers T
  icases Hctx with #Hctx
  isplitl
  · iunfold epochStream1; iexists T; iframe; iframe #; ipureintro; exact hT
  · iexists T; iframe #; ipureintro; exact hT

end ghost

end mvccfull
end EtcdGrove
end Perennial
