/-
`runChecks`' ghost state (`examples/mvccrand/mvccrand.go`): the tester's invariant and the shared
objects' handles, made from the new store, stream and history. Lean-first (no Rocq counterpart).

- **The start** (`hist0` against `mvccStart`, `wsStart`): the history's two empty revisions are the
  new store's (`revOk`), the registry empty (`regOk`).
- **The world** (`world_alloc`): the ghost names `RandNames` around the store's and the stream's and
  the history's, the invariant `worldInv` (the store at `mvccStart`, the stream open, published `1`),
  the writer's idle state at the start, the registrar's half of `γ.cl`, `c.mu`'s half of the
  registry and the receiver's and `c.mu`'s halves of `γ.rcv`.
- **The history's lock** (`hist_alloc`): from `newHistory`'s raw parts, the guard and the counter's
  invariant (`isHistory`) and the lock's reader slots, `n` of them dealt as handles (`histRd`).
- **The watch check's lock** (`cmu_alloc`): its invariant at no watcher and nothing received.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WatchLock
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksBackend

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

theorem stMatch_nil : stMatch ∅ [] := by
  refine ⟨fun k => ?_, fun v hv => ?_⟩
  · simp [findKey]
  · simp at hv

theorem stateAt_start (r : Nat) : stateAt mvccStart.log r = [] := by
  unfold stateAt stateAfter mvccStart
  rcases r with _ | _ | r <;> rfl

/-- The history's start is the new store's. -/
theorem revOk_start : ∀ r < hist0.length, ∃ e, hist0[r]? = some e ∧ revOk mvccStart.log hist0 r e := by
  intro r hr
  have hr' : r = 0 ∨ r = 1 := by simp [hist0] at hr; omega
  rcases hr' with rfl | rfl
  · refine ⟨(∅, []), rfl, ?_, fun h => absurd h (by decide)⟩
    rw [stateAt_start]; exact stMatch_nil
  · refine ⟨(∅, []), rfl, ?_, fun _ => ⟨(∅, []), rfl, rfl⟩⟩
    rw [stateAt_start]; exact stMatch_nil

theorem histOkM_start : histOkM mvccStart hist0 :=
  ⟨by simp [MvccState.notifiedLog, mvccStart, hist0],
    fun r hr => revOk_start r (by simpa [MvccState.notifiedLog, mvccStart, hist0] using hr)⟩

theorem regOk_start : regOk wsStart ∅ := by
  intro id
  simp only [GMap.lookup_empty]
  intro wi hwi
  simp [wsStart] at hwi

theorem rcvKnown_start : rcvKnown [] (∅ : GMap w64 (Loc × RegInfo)) := by
  intro r hr; simp at hr

end model

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The tester's ghost state at the start** (see the file header). -/
theorem world_alloc (h : Loc)
    (γk : MvccName) (ι : WsName) (γh : HistNames) :
    mvccState γk mvccStart ∗ wsState ι wsStart ∗
        sync.atomic.ownInt64 (hPub h) (DFrac.own 1) (W64 1) ∗ histW γh hist0 ⊢
      |={⊤}=> ∃ γ : RandNames, ⌜γ.kv = γk ∧ γ.ws = ι ∧ γ.h = γh⌝ ∗
        inv worldN (worldInv h γ) ∗ writerIdle γ mvccStart hist0 ∗
        ghostVar γ.cl (1 : Qp).half false ∗
        ghostMapAuth γ.reg (1 : Qp).half (∅ : GMap w64 (Loc × RegInfo)) ∗
        ghostVar γ.rcv (1 : Qp).half ([] : List WResp) ∗
        ghostVar γ.rcv (1 : Qp).half ([] : List WResp) ∗ monoListLbOwn γh.l hist0 := by
  iintro ⟨Hσ, HS, Hpub, Hw⟩
  ihave ⟨Hw, #Hlb⟩ := histW_lb γh hist0 $$ Hw
  imod ghostVar_alloc (GF := GF) mvccStart with ⟨%gσ, Hgσ⟩
  icases (ghostVar_split_half gσ 1 mvccStart).1 $$ Hgσ with ⟨Hgσ1, Hgσ2⟩
  imod mono_nat_own_alloc (GF := GF) 1 with ⟨%gpub, Hpm, -⟩
  imod ghostVar_alloc (GF := GF) (W64 1) with ⟨%gpv, Hpv⟩
  icases (ghostVar_split_half gpv 1 (W64 1)).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
  imod (ghost_map_alloc_empty (GF := GF) :
    ⊢ |==> ∃ γ, ghostMapAuth (GF := GF) γ 1 (∅ : GMap w64 (Loc × RegInfo))) with ⟨%greg, Hreg⟩
  icases (ghostMapAuth_halves greg ∅).1 $$ Hreg with ⟨Hreg1, Hreg2⟩
  imod ghostVar_alloc (GF := GF) ([] : List WResp) with ⟨%grcv, Hrcv⟩
  icases (ghostVar_split_half grcv 1 ([] : List WResp)).1 $$ Hrcv with ⟨Hrcv1, Hrcv2⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%gcl, Hcl⟩
  icases (ghostVar_split_half gcl 1 false).1 $$ Hcl with ⟨Hcl1, Hcl2⟩
  let γ : RandNames := ⟨γk, ι, γh, gσ, gpub, gpv, greg, grcv, gcl⟩
  imod inv_alloc worldN ⊤ (worldInv (GF := GF) h γ) $$ [Hσ Hgσ1 HS Hcl1 Hreg1 Hpub Hpv1 Hpm] with #Hinv
  · inext
    iunfold worldInv
    iexists mvccStart, wsStart, W64 1, hist0, ∅
    rw [show wsStart.closed = false from rfl, show sint.nat (W64 1) = 1 from rfl]
    iframe Hσ Hgσ1 HS Hcl1 Hreg1 Hpub Hpv1 Hpm Hlb
    ipureintro
    exact ⟨rfl, by decide, by decide, histOkM_start, regOk_start⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iframe Hinv Hcl2 Hreg2 Hrcv1 Hrcv2 Hlb
  iunfold writerIdle
  iframe Hgσ2 Hw
  isplitl [Hpv2]
  · rw [show (W64 ((mvccStart.rev : Nat) : Int)) = W64 1 from rfl]; iexact Hpv2
  ipureintro
  exact ⟨rfl, rfl, by decide, revOk_start⟩

/-- `n` handles of the history from as many reader slots. -/
theorem histRds_of (h : Loc) (γh : HistNames) : ∀ n : Nat,
    isHistory (GF := GF) h γh ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (hMu h) (histR h γh)) ⊢
      [∗list] _x ∈ List.replicate n (), histRd h γh
  | 0 => by
    iintro -
    simp only [List.replicate]
    iapply BigSepL.bigSepL_nil.2; itrivial
  | n + 1 => by
    iintro ⟨#Hh, Hs⟩
    rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H1, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iunfold histRd; iframe Hh H1
    · iapply histRds_of h γh n $$ [Hs]; iframe Hh Hs

/-- **The history's lock and handles** (see the file header): `n` handles, at most the lock's
reader slots. -/
theorem hist_alloc (h : Loc) (γh : HistNames) (n : Nat)
    (hn : n ≤ Int.toNat sync.rwmutex.actualMaxReaders) :
    hMu h ↦ zero_val sync.RWMutex ∗ histR (GF := GF) h γh 1 ∗
        sync.atomic.ownInt64 (hAbove h) (DFrac.own 1) (W64 0) ⊢
      |={⊤}=> isHistory h γh ∗ [∗list] _x ∈ List.replicate n (), histRd h γh := by
  iintro ⟨Hmu, Hr, Hab⟩
  imod sync.init_RWMutex (histR (GF := GF) h γh) (E := ⊤) (hMu h) $$ [Hr] Hmu with Hslots
  · inext; iexact Hr
  ihave ⟨Hslots, #Hg⟩ := sync.ownRWMutex_slots_guard (hMu h) (histR (GF := GF) h γh) $$ Hslots
  imod inv_alloc histN ⊤ (aboveInv (GF := GF) h) $$ [Hab] with #Hab
  · inext; iunfold aboveInv; iexists W64 0; iexact Hab
  ihave #Hh : isHistory (GF := GF) h γh $$ []
  · iunfold isHistory; iframe Hg Hab
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = n + m := ⟨_, (Nat.add_sub_cancel' hn).symm⟩
  rw [hm]
  icases (backend.bigSepL_replicate_add _ n m).1 $$ Hslots with ⟨Hn, -⟩
  imodintro
  iframe Hh
  iapply histRds_of h γh n $$ [Hn]
  iframe Hh Hn

/-- **The watch check's lock** (see the file header). -/
theorem cmu_alloc (c : Loc) (γ : RandNames) (wm : GoMap) :
    cF go!"mu" c ↦ zero_val sync.Mutex ∗ wm ↦$ (∅ : GMap w64 Loc) ∗
        ghostMapAuth γ.reg (1 : Qp).half (∅ : GMap w64 (Loc × RegInfo)) ∗
        ghostVar γ.rcv (1 : Qp).half ([] : List WResp) ∗ monoListLbOwn γ.h.l hist0 ⊢
      |={⊤}=> sync.isMutex (GF := GF) (cF go!"mu" c) (cmuInv wm γ) := by
  iintro ⟨Hmu, Hwm, Hreg, Hrcv, #Hlb⟩
  iapply sync.init_Mutex (cmuInv (GF := GF) wm γ) ⊤ (cF go!"mu" c) $$ Hmu
  inext
  iunfold cmuInv
  iexists [], ∅, hist0
  rw [GMap.fmap_empty]
  iframe Hwm Hreg Hrcv Hlb
  isplitr
  · ipureintro; exact rcvKnown_start
  iapply BigSepM.bigSepM_empty.2; itrivial

/-- **`ws.Close()`'s update** at the tester's invariant: the registrar's half of `γ.cl`, given back
after its last `Watch`, shows the stream open; the close sets both halves. -/
theorem close_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (h : Loc) (γ : RandNames) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.cl (1 : Qp).half false ⊢
      AU <{ ∃∃ (S : StreamState), wsState γ.ws S ∗ ⌜S.closed = false⌝ }> @ ⊤ \ ↑mvccN, ∅
      <{ wsState γ.ws S.close, COMM (fun (_ : StreamState) => iprop(True)) S }> := by
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask_wl
  iintro ⟨#Hinv, Hcl⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W', Hσ, Hgσ, ⟨HS, HScl⟩, Hreg', Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave %Hc := ghostVar_agree γ.cl _ _ _ _ $$ HScl Hcl
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
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
    imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W'; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iframe
  · iintro HS
    imod ghostVar_update_halves true γ.cl _ _ $$ HScl Hcl with ⟨HScl, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
    · inext; iunfold worldInv
      iexists σ, S.close, p, Hl, W'
      iframe; iframe #
      ipureintro
      exact Hok
    imodintro
    itrivial

/-- **The published revision, loaded after the writer's end**: a lower bound of the history that
has it, and a revision below `2 ^ 63 - 1` (the tester's invariant and the store's reachability). -/
theorem pub_facts (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (σ : MvccState) (p : w64) (Hl : List HRev) (kv : GoInterface) (γk : MvccName)
    (h1 : 1 ≤ sint.Z p) (h2 : sint.nat p ≤ σ.rev) (h3 : histOkM σ Hl) :
    isMvcc (GF := GF) kv γk ∗ mvccState γk σ ⊢
      mvccState γk σ ∗ ⌜sint.Z p < Hl.length ∧ sint.Z p < 2 ^ 63 - 1⌝ := by
  iintro ⟨Hkv, Hσ⟩
  ihave %Hr := hreach kv γk σ $$ [$Hkv $Hσ]
  iframe Hσ
  ipureintro
  have hle : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  have hz : (sint.nat p : Int) = sint.Z p := by
    have : sint.nat p = (sint.Z p).toNat := rfl
    omega
  have h3' := h3.1
  have h4 := Hr.2
  unfold MvccState.rev at h2
  constructor <;> omega

end ghost

end mvccrand
end EtcdGrove
end Perennial
