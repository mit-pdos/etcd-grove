/-
# Probe: v3rpc's watch proof over mvcc's frozen watch laws (client side)

Scratch (never built by `lake build`; check with `lake env lean notes/mvcc-api-probes/WatchClientProbe.lean`
from the worktree root). Does v3rpc's watch proof go through over the API's watch laws
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`), before either side is proved? The laws
are taken as hypotheses (`persistent.law`, `wsRecv_ok.law`, `wsChan_recv.law`, `wsSentLb_zero.law`);
the client is a minimal model of what v3rpc holds (the draft `notes/mvcc-api-clients/WatchSpecs.lean`,
§3 and §7):

* §1 the model: the run's invariant at `wsN` (`wsState ι S`, the registry `γreg` of the watch ids
  it created, every watcher unfiltered, every watcher live or cancelled at the client's request
  `cancelQ`), and the server's peek: an invariant at `srvN` (disjoint from `mvccN`) holding
  `mvccState γ σ`;
* §2 `drain_empty` (O5): the non-blocking receive's empty arm, at a `wsSentLb ι k`, gives
  `k ≤ |rs|`, and with it the created response's `createdAfter` (in the model's terms);
* §3 `snap_after_recv` (O4): after a receive, at `⊤` with no credit and no step, the snapshot
  `wsRecvOk σ S rs` with the registry's entries of `S`, and every id the client holds a registry
  entry of (`regIs`) a watcher of `S` with that entry;
* §4 `progressCov`'s core: a received `-1` at index `n ≥ |l| ≥ k` covers every watcher of the
  snapshot registered at stamp `k`: live, conjunct 3 at `n`; not live, the client's cancel request.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoList

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc
namespace WatchClientProbe

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

/-! ## §0 The pure models (the draft's §2) -/

instance WResp.countable : Pos.Countable WResp :=
  .ofInjective (fun r => Pos.Countable.encode (r.id, r.evs, r.rev, r.compactRev))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- **A registry entry**: what v3rpc records of a watcher at `Watch`'s commit (the draft's
`RegInfo`: the `WInfo` but its filters, `[]` for v3rpc's watchers, and its liveness). -/
structure RegInfo where
  rg : mvcc.WatchRange
  lo : Nat
  k : Nat

instance RegInfo.countable : Pos.Countable RegInfo :=
  .ofInjective (fun r => Pos.Countable.encode (r.rg, r.lo, r.k))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

def regInfoOf (w : WInfo) : RegInfo := ⟨w.rg, w.lo, w.k⟩

/-- No filter drops an event. -/
theorem filtered_nil (evs : List mvcc.EvM) : mvcc.filtered [] evs = evs := by
  simp [mvcc.filtered]

/-! ## §1 The model of what v3rpc holds -/

section probe
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- v3rpc's per-run invariant's namespace (the draft's `wsN`). -/
def wsN : Namespace := (nroot .@ "v3rpc") .@ "ws"
/-- The server's invariant holding `mvccState` (the draft's `SrvW.N`). -/
def srvN : Namespace := nroot .@ "srv"

/-- Both outside `mvccN` (so they open inside `Watch`'s update, at `⊤ \ ↑mvccN`), and disjoint. -/
theorem probe_masks : (↑srvN : CoPset) ⊆ ⊤ \ ↑mvccN ∧ (↑wsN : CoPset) ⊆ ⊤ \ ↑mvccN ∧
    (↑srvN : CoPset) ⊆ ⊤ \ ↑wsN := by
  unfold srvN wsN mvccN
  refine ⟨?_, ?_, ?_⟩ <;> solve_ndisj

/-- The registry's entry of `id` (persistent). -/
abbrev regIs (γreg : GName) (id : w64) (i : RegInfo) : IProp GF :=
  ghostMapElem γreg id DFrac.discard i

/-- The send loop's received list has `l` first (persistent). -/
abbrev rcvLb (γr : GName) (l : List WResp) : IProp GF := monoListLbOwn γr l

/-- The client's per-watcher facts of the stream's state `S`: each watcher's registry entry, and
live or cancelled at the client's request (`cancelQ`: today's `∃ i, upAtW γs i (.cancel id)`, a
`monoListIdxOwn`, persistent and timeless). -/
abbrev regFacts (γreg : GName) (cancelQ : w64 → IProp GF) (S : StreamState) : IProp GF :=
  iprop([∗map] id ↦ w ∈ S.ws, regIs γreg id (regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cancelQ id))

/-- **v3rpc's invariant of a run** (the draft's `wsInv`, minimal): the stream's state, the
registry's authority agreeing with it, every watcher unfiltered, and the per-watcher facts. -/
abbrev wsInv (ι : WsName) (γreg : GName) (cancelQ : w64 → IProp GF) : IProp GF :=
  iprop(∃ (S : StreamState) (R : GMap w64 RegInfo), wsState ι S ∗ ghostMapAuth γreg 1 R ∗
    ⌜(∀ id, R.lookup id = (S.ws !! id).map regInfoOf) ∧ ∀ id w, S.ws !! id = some w → w.fs = []⌝ ∗
    □ regFacts γreg cancelQ S)

/-- **The server's peek**, minimal: an invariant at `srvN` holding the store's state. -/
abbrev srvInv (γ : MvccName) : IProp GF := iprop(∃ σ : MvccState, mvccState γ σ)

/-- **The send loop's snapshot of `rs`** (the draft's `rcvSnap`, without the server's `histLb` and
`crevOk`, which are the server's): the watch guarantee at the state and stream state of a moment
after the receive, every watcher unfiltered, and the per-watcher facts. -/
def rcvSnap (γreg : GName) (cancelQ : w64 → IProp GF) (rs : List WResp) (σ : MvccState)
    (S : StreamState) : IProp GF :=
  iprop(⌜wsRecvOk σ S rs ∧ ∀ id w, S.ws !! id = some w → w.fs = []⌝ ∗ □ regFacts γreg cancelQ S)

variable (cancelQ : w64 → IProp GF) [hcqP : ∀ id, Persistent (cancelQ id)]
  [hcqT : ∀ id, Timeless (cancelQ id)]

/-! ## §2 The drain (O5) -/

/-- **The drain's poll** (O5, from `wsChan_recv.law`'s non-blocking receive): the stream's
channel, and for every poll at a stamp `k` (`wsSentLb ι k`), with the send loop's received list's
authority at `rs` framed through, the receive's arm (as the law's) or the empty arm with
`k ≤ |rs|` and the received list's lower bound at `rs`. -/
theorem drain_poll (hR : wsChan_recv.law (GF := GF)) (ws : GoInterface) (γ : MvccName)
    (ι : WsName) :
    isMvccWatchStream ws γ ι ⊢ isChan (wsChanOf ι) (wsChanNames ι) WatchResponse ∗
      □ ∀ (rs : List WResp) (k : Nat) (γr : GName) (Φ : WatchResponse → Bool → IProp GF)
          (Ψ : IProp GF),
        wsRecv ι rs -∗ wsSentLb ι k -∗ monoListAuthOwn γr 1 rs -∗
        ((∀ (v : WatchResponse) (ok : Bool),
            (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗
            monoListAuthOwn γr 1 rs -∗ Φ v ok) ∧
          (wsRecv ι rs -∗ monoListAuthOwn γr 1 rs -∗ rcvLb γr rs -∗ ⌜k ≤ rs.length⌝ -∗ Ψ)) -∗
        nonblockingRecvAuAlt (wsChanNames ι) WatchResponse Φ Ψ := by
  iintro Hws
  icases hR ws γ ι $$ Hws with ⟨#Hch, -, #Hnb⟩
  isplitr
  · iexact Hch
  imodintro
  iintro %rs %k %γr %Φ %Ψ Hr Hk HA HK
  iapply Hnb $$ Hr Hk
  isplit
  · iintro %v %ok Hres
    icases HK with ⟨HK, -⟩
    iapply HK $$ Hres HA
  · iintro Hr %Hle
    icases HK with ⟨-, HK⟩
    ihave #Hlb := monoListLbOwn_get γr 1 rs $$ HA
    iapply HK $$ Hr HA Hlb
    ipureintro
    exact Hle

/-- **The created response's `createdAfter`** (the draft's `createdAfter2`, with the sent list
abstracted as `sent n x`: the `n`-th received `x` was sent). -/
def createdAfterM (γr : GName) (k : Nat) (sent : Nat → WResp → Prop) : IProp GF :=
  iprop(∃ l : List WResp, rcvLb γr l ∗
    ⌜k ≤ l.length ∧ ∀ (n : Nat) (x : WResp), l[n]? = some x → x.id = W64 (-1) → sent n x⌝)

/-- **`drain_empty`** (O5, the draft's statement, `regIs`'s `i.k` as `k` and the sent list as
`sent`): the empty arm's `k ≤ |rs|` and the drain's own fact (every `-1` received was sent) give
the created response's `createdAfter`, the received list's authority kept. -/
theorem drain_empty (γr : GName) (rs : List WResp) (k : Nat) (sent : Nat → WResp → Prop) :
    monoListAuthOwn (GF := GF) γr 1 rs ∗
      ⌜k ≤ rs.length ∧ ∀ (n : Nat) (x : WResp), rs[n]? = some x → x.id = W64 (-1) → sent n x⌝ ⊢
    |==> (monoListAuthOwn γr 1 rs ∗ createdAfterM γr k sent) := by
  iintro ⟨HA, %Hk, %Hs⟩
  ihave #Hlb := monoListLbOwn_get γr 1 rs $$ HA
  imodintro
  iframe HA
  unfold createdAfterM
  iexists rs
  iframe Hlb
  ipureintro
  exact ⟨Hk, Hs⟩

/-- **The drain before a refused create** (no stamp): the poll at `wsSentLb ι 0`
(`wsSentLb_zero.law`). -/
theorem drain_poll_zero (hR : wsChan_recv.law (GF := GF)) (hz : wsSentLb_zero.law (GF := GF))
    (ws : GoInterface) (γ : MvccName) (ι : WsName) (rs : List WResp) (γr : GName)
    (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF) :
    isMvccWatchStream ws γ ι ∗ wsRecv ι rs ∗ monoListAuthOwn γr 1 rs ∗
      ((∀ (v : WatchResponse) (ok : Bool),
          (if ok then ∃ r : WResp, wsRecv ι (rs ++ [r]) ∗ wrespIs v r else wsRecv ι rs) -∗
          monoListAuthOwn γr 1 rs -∗ Φ v ok) ∧
        (wsRecv ι rs -∗ monoListAuthOwn γr 1 rs -∗ Ψ)) ⊢
    isChan (wsChanOf ι) (wsChanNames ι) WatchResponse ∗
      nonblockingRecvAuAlt (wsChanNames ι) WatchResponse Φ Ψ := by
  iintro ⟨Hws, Hr, HA, HK⟩
  icases drain_poll hR ws γ ι $$ Hws with ⟨#Hch, #Hp⟩
  ihave #H0 := hz ι
  isplitr
  · iexact Hch
  iapply Hp $$ %rs %0 %γr %Φ %Ψ Hr H0 HA
  isplit
  · icases HK with ⟨HK, -⟩
    iexact HK
  · icases HK with ⟨-, HK⟩
    iintro Hr HA - -
    iapply HK $$ Hr HA

/-! ## §2' `Watch`'s commit (O1's ghost step, a check of the contract's premises) -/

/-- **At `Watch`'s commit on an open stream** (inside the update v3rpc passes, at `⊤ \ ↑mvccN`,
where `probe_masks` puts both invariants): the contract's `S.ws !! id = none` makes the id fresh in
the registry, so the invariant's registry part is re-established for `S.register id w` (an
unfiltered, live watcher), with the new entry's `regIs` for the created response. -/
theorem watch_commit (γreg : GName) (S : StreamState) (R : GMap w64 RegInfo) (id : w64)
    (rg : mvcc.WatchRange) (lo k : Nat)
    (HR : (∀ x, R.lookup x = (S.ws !! x).map regInfoOf) ∧ ∀ x w, S.ws !! x = some w → w.fs = [])
    (hfresh : S.ws !! id = none) :
    ghostMapAuth (GF := GF) γreg 1 R ∗ □ regFacts γreg cancelQ S ⊢
    |==> ∃ R' : GMap w64 RegInfo, ghostMapAuth γreg 1 R' ∗
      ⌜(∀ x, R'.lookup x = ((S.register id ⟨rg, [], lo, k, true⟩).ws !! x).map regInfoOf) ∧
        ∀ x w, (S.register id ⟨rg, [], lo, k, true⟩).ws !! x = some w → w.fs = []⌝ ∗
      □ regFacts γreg cancelQ (S.register id ⟨rg, [], lo, k, true⟩) ∗
      regIs γreg id ⟨rg, lo, k⟩ := by
  iintro ⟨HA, #Hreg⟩
  have hR : R.lookup id = none := by rw [HR.1 id, hfresh]; rfl
  imod ghost_map_insert_persist id ⟨rg, lo, k⟩ hR $$ HA with ⟨HA, #Hid⟩
  imodintro
  iexists R.insert id ⟨rg, lo, k⟩
  iframe HA
  isplitr
  · ipureintro
    refine ⟨fun x => ?_, fun x w hx => ?_⟩
    · by_cases hx : id = x
      · subst hx
        show (R.insert id _).lookup id = ((S.ws.insert id _).lookup id).map regInfoOf
        rw [GMap.lookup_insert, GMap.lookup_insert]; rfl
      · show (R.insert id _).lookup x = ((S.ws.insert id _).lookup x).map regInfoOf
        rw [GMap.lookup_insert_ne _ _ hx, GMap.lookup_insert_ne _ _ hx]
        exact HR.1 x
    · by_cases hix : id = x
      · subst hix
        have : (S.ws.insert id ⟨rg, [], lo, k, true⟩).lookup id = some w := hx
        rw [GMap.lookup_insert] at this
        cases this; rfl
      · have : (S.ws.insert id ⟨rg, [], lo, k, true⟩).lookup x = some w := hx
        rw [GMap.lookup_insert_ne _ _ hix] at this
        exact HR.2 x w this
  isplitl []
  · unfold regFacts
    imodintro
    rw [show (S.register id ⟨rg, [], lo, k, true⟩).ws =
      Std.insert S.ws id ⟨rg, [], lo, k, true⟩ from rfl]
    iapply (BigSepM.bigSepM_insert
      (Φ := fun id w => iprop(regIs γreg id (regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cancelQ id)))
      (show Std.get? S.ws id = none from hfresh)).2
    isplitl []
    · rw [show regInfoOf ⟨rg, [], lo, k, true⟩ = ⟨rg, lo, k⟩ from rfl]
      iframe Hid
      ileft
      ipureintro
      rfl
    · iexact Hreg
  · iexact Hid

/-! ## §3 The snapshot after a receive (O4) -/

/-- **`snap_after_recv`** (O4): holding `wsRecv ι rs` (right after a receive) and the registry
entries `M` of the ids the client cares about (the live ids of the responses it sent), a ghost step
at `⊤`, with no credit: open the run's invariant and the server's peek (timeless: the later is
stripped), apply `wsRecv_ok.law`, close both unchanged. The snapshot, and each id of `M` a watcher
of the snapshot's `S` with that entry. -/
theorem snap_after_recv (hP : persistent.law (GF := GF)) (hok : wsRecv_ok.law (GF := GF))
    (ws : GoInterface) (γ : MvccName) (ι : WsName) (γreg : GName) (rs : List WResp)
    (M : GMap w64 RegInfo) :
    isMvccWatchStream ws γ ι ∗ inv wsN (wsInv ι γreg cancelQ) ∗ inv srvN (srvInv γ) ∗
      wsRecv ι rs ∗ □ ([∗map] X ↦ i ∈ M, regIs γreg X i) ⊢
    |={⊤}=> wsRecv ι rs ∗ ∃ (σ : MvccState) (S : StreamState), rcvSnap γreg cancelQ rs σ S ∗
      ⌜∀ X i, M.lookup X = some i → ∃ w, S.ws !! X = some w ∧ regInfoOf w = i⌝ := by
  have : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hP.2.1
  have : ∀ γ σ, Timeless (mvccState (GF := GF) γ σ) := hP.2.2.2.2.1
  have : ∀ ι S, Timeless (wsState (GF := GF) ι S) := hP.2.2.2.2.2.1
  iintro ⟨#Hws, #Hwi, #Hsi, Hr, #HM⟩
  iinv Hwi with > ⟨%S, %R, HS, HA, %HR, #Hreg⟩ Hcw
  iinv Hsi with > ⟨%σ, Hσ⟩ Hcs
  · exact probe_masks.2.2
  ihave %Hok := hok ws γ ι rs S σ $$ [Hr HS Hσ]
  · iframe ∗ #
  ihave %HMR := ghost_map_lookup_big M $$ HA HM
  imod Hcs $$ [Hσ] with -
  · inext
    iexists σ
    iexact Hσ
  imod Hcw $$ [HS HA] with -
  · inext
    iexists S, R
    iframe HS HA Hreg
    ipureintro
    exact HR
  imodintro
  iframe Hr
  iexists σ, S
  unfold rcvSnap
  iframe Hreg
  ipureintro
  refine ⟨⟨Hok, HR.2⟩, fun X i hX => ?_⟩
  have h1 := HR.1 X
  rw [HMR X i hX] at h1
  cases hw : S.ws !! X with
  | none => rw [hw] at h1; simp at h1
  | some w =>
    rw [hw] at h1
    exact ⟨w, rfl, (Option.some.inj h1).symm⟩

/-! ## §4 `progressCov`'s core -/

/-- **A received `-1` covers every live watcher registered before it was sent** (pure, from
`wsRecvOk`): at the `n`-th received response `x`, a `-1`, and a watcher `X` of `S`, live, whose
stamp is at most the received list `l` its created response's drain saw (`createdAfter`), itself at
most `n` (the draft's step 1: a `-1` before `|l|` was sent before the created response), under the
watch condition: `X`'s events received up to `x` are exactly its kept events up to `x`'s revision.
The `-1`'s event-less, non-compaction shape is conjunct 1's, not a premise. -/
theorem progressCov_pure (σ : MvccState) (S : StreamState) (rs : List WResp) (n : Nat)
    (x : WResp) (X : w64) (w : WInfo) (l : List WResp) (hok : wsRecvOk σ S rs)
    (hx : rs[n]? = some x) (hid : x.id = W64 (-1)) (hw : S.ws !! X = some w)
    (hlive : w.live = true) (hkl : w.k ≤ l.length) (hln : l.length ≤ n)
    (honce : onceUpTo σ.notifiedLog w.lo σ.crev) :
    recvEvs (rs.take (n + 1)) X =
      mvcc.filtered w.fs (mvcc.watchEvents σ.notifiedLog w.rg w.lo (sint.nat x.rev + 1)) := by
  have hmem : x ∈ rs := List.mem_of_getElem? hx
  obtain ⟨hev, hcr, -⟩ := (hok.1 x hmem).2.2.2.2.1 hid
  exact hok.2.2 n x X w hx hev hcr hw honce (Or.inr ⟨hid, hlive, by omega⟩)

/-- **`progressCov`'s core at the snapshot** (the draft's steps 2-3): at the snapshot of `rs`, an id
`X` the client registered with the entry `i` (a watcher of the snapshot's `S` with that entry:
`snap_after_recv`'s second conclusion), a received `-1` at `n ≥ |l| ≥ i.k`, and the watch condition
at the entry's first revision: `X`'s events received up to the `-1` are exactly its range's events
up to the `-1`'s revision (unfiltered: v3rpc's watchers are), or the client asked to cancel `X`. -/
theorem progressCov_core (γreg : GName) (rs : List WResp) (σ : MvccState) (S : StreamState)
    (n : Nat) (x : WResp) (X : w64) (i : RegInfo) (l : List WResp) :
    rcvSnap γreg cancelQ rs σ S ⊢
    ⌜(∃ w, S.ws !! X = some w ∧ regInfoOf w = i) ∧ rs[n]? = some x ∧ x.id = W64 (-1) ∧
      i.k ≤ l.length ∧ l.length ≤ n ∧ onceUpTo σ.notifiedLog i.lo σ.crev⌝ -∗
    (⌜recvEvs (rs.take (n + 1)) X =
        mvcc.watchEvents σ.notifiedLog i.rg i.lo (sint.nat x.rev + 1)⌝ ∨ cancelQ X) := by
  unfold rcvSnap regFacts
  iintro ⟨%Hs, #Hreg⟩ % ⟨⟨w, hw, hwi⟩, hx, hid, hkl, hln, honce⟩
  subst hwi
  ihave ⟨-, Hl⟩ := BigSepM.bigSepM_lookup
    (Φ := fun id w => iprop(regIs γreg id (regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cancelQ id))) hw $$ Hreg
  icases Hl with (%hlive | Hc)
  · ileft
    ipureintro
    have := progressCov_pure σ S rs n x X w l Hs.1 hx hid hw hlive hkl hln honce
    rw [Hs.2 X w hw, filtered_nil] at this
    exact this
  · iright
    iexact Hc

end probe

/-! ## §5 Findings

* **Sufficient.** `drain_poll`, `drain_empty`, `drain_poll_zero`, `watch_commit`, `snap_after_recv`,
  `progressCov_pure`, `progressCov_core` are proved from the laws, no `sorry`. The snapshot is a
  `|={⊤}=>` with no credit and no step: `wsState`, `mvccState` (`persistent.law`) and the model's
  invariant contents are timeless, the namespaces fit (`probe_masks`: both outside `mvccN`, so they
  also open inside `Watch`'s, `Cancel`'s and `Close`'s updates at `⊤ \ ↑mvccN`), and
  `wsRecv_ok.law`'s pure conclusion keeps its four resources (iris-lean's `ihave %`). The `-1`'s
  event-less, non-compaction shape that conjunct 3 needs is conjunct 1's (no premise for the
  client). Conjunct 3's `w.k ≤ j` (received index) meets `wsSentLb`'s stamp through the drain:
  `k ≤ |l| ≤ n`.
* **Awkward, not too weak.** (1) `persistent.law` gives the instances as a `Prop`, so each client
  proof re-declares them as local instances (`have : ∀ ι S, Timeless (wsState ι S) := hP.2.2.2.2.2.1`,
  three here) before `#`/`>` patterns and `iinv` find them; at adoption, state them as `instance`s
  of the defined predicates. (2) `wsChan_recv.law`'s `∃ γch` has no name: a client can use it
  inside one proof (destruct once, keep `isChan` and the boxed receives together), but cannot
  mention it in a definition (a run record, a spec's loop resources) without threading an
  existential; the fix, should a client need it: `opaque wsChanNames (ι : WsName) : ChanNames` and
  the law at `wsChanNames ι` in place of `∃ γch`.
* **Not missing, the client's.** "Registered before the snapshot" (the draft's `-1` clause of
  `mvccOk2`, `X ∈ S`) has no API witness: the client's own registry gives it, by handing its
  entries (`M`) to the snapshot, where the authority's lookup places them in `S`. -/

end WatchClientProbe
end v3rpc
end EtcdGrove
end Perennial
