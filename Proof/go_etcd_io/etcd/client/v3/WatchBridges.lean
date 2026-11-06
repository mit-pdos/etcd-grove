/-
**The client's watch path over v3rpc's restated stream spec: the bridges** (strict M1,
2026-11-06; the draft's §8, `notes/mvcc-api-clients/WatchSpecs.lean`). What an mvcc response the
watch server sent (`v3rpc.mvccOk`: its source in the send loop's received list and the snapshot
`rcvSnap` of the API's watch guarantee `wsRecvOk` at it) says to the client, in place of mvcc's
internal `watchRecvOk`, `watcherIs`, `respCov`, `regsAt`, `idAssigned`, `crevPermAt`:

* `mvccOk_at`: the response's facts at its source `(n, x)`;
* `srvEventIdsAssigned_holds` (S3): a response of an id other than `-1` is of a registered id;
* `recvEvents`: a registered watcher's events received up to `x` are its range's events of
  `[lo, hi)` of a certified log (under the client's watch condition `srvOnce`);
* `progressCov`: an event-less, non-compaction response of a watcher's own id, or the stream's
  `-1` after its created response, covers it exactly up to its revision (or the client asked to
  cancel it);
* `compactResp`: a compaction response's revision is at most a permitted one;
* `mvccOk_revLb`: a response that is not a compaction's is at a revision of a certified log.

The draft's `recvEvents`/`progressCov` take `srvOnce` alone; the snapshot's certified log is
spatial (`histLb` is persistent only by `srvWOk`'s law) and `srvOnce` consumes it, so they also take
`srvWLaws` (the client's member facts have it). Lean-first, no Rocq counterpart.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## Pure facts -/

/-- Two prefix-comparable lists agree where both are defined. -/
theorem getElem?_of_comparable {α : Type} {l l' : List α} (h : l <+: l' ∨ l' <+: l) {n : Nat}
    {a : α} (hl : n < l.length) (h' : l'[n]? = some a) : l[n]? = some a := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.getElem?_append_left hl] at h'; exact h'
  · have hn : n < l'.length := (List.getElem?_eq_some_iff.1 h').1
    rw [List.getElem?_append_left hn]; exact h'

/-- Two comparable lists of one length are equal. -/
theorem eq_of_comparable {α : Type} {l l' : List α} (h : l <+: l' ∨ l' <+: l)
    (hl : l.length = l'.length) : l = l' := by
  rcases h with h | h
  · exact h.eq_of_length hl
  · exact (h.eq_of_length hl.symm).symm

/-- No filters keep every event. -/
theorem filtered_nil (evs : List mvcc.EvM) : mvcc.filtered [] evs = evs := by
  unfold mvcc.filtered; simp

/-! ## What the watch guarantee does not say (finding F-W1, `notes/mvcc-migration/clientv3.md`)

mvcc's API (`mvcc.api.wsRecvOk`, frozen) does not say that a watcher's progress notification is at
a revision at least its first revision less one, nor that event-less responses' revisions do not
decrease along the stream. client/v3's completeness contract (the exported `watchStateRespOk`: a
progress notification at or past the cursor) needs both; until M1 mvcc's internal `covFact`
(`γw.lo ≤ rev + 1`) and `respRev` (`∀ y ∈ pre, y.evs = [] → y.rev ≤ x.rev`) gave them, and the
code does them (`progressIfSync`: progress only for synced watchers with `rev ≥ startRev`, at the
store's revision, which only grows). Each is a placeholder here until the API states it. -/

/-- **(M1-REPLACE) A watcher's progress notification is past its first revision less one.** -/
theorem wsRecvOk_progLo (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState)
    (rs : List mvcc.api.WResp) (_h : mvcc.api.wsRecvOk σ S rs) :
    ∀ (j : Nat) (r : mvcc.api.WResp) (id : w64) (w : mvcc.api.WInfo), rs[j]? = some r →
      r.evs = [] → r.compactRev = W64 0 → S.ws !! id = some w →
      (r.id = id ∨ (r.id = W64 (-1) ∧ w.live = true ∧ w.k ≤ j)) →
      (w.lo : Int) ≤ sint.Z r.rev + 1 := by
  sorry -- M1-REPLACE: wsRecvOk lacks a progress notification's lower bound (finding F-W1)

/-- **(M1-REPLACE) Event-less responses' revisions do not decrease along the stream.** -/
theorem wsRecvOk_progMono (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState)
    (rs : List mvcc.api.WResp) (_h : mvcc.api.wsRecvOk σ S rs) :
    ∀ (i j : Nat) (y x : mvcc.api.WResp), i < j → rs[i]? = some y → rs[j]? = some x →
      y.evs = [] → x.evs = [] → x.compactRev = W64 0 → sint.Z y.rev ≤ sint.Z x.rev := by
  sorry -- M1-REPLACE: wsRecvOk lacks event-less responses' monotone revisions (finding F-W1)

section bridges
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **An mvcc response's facts at its source** `(n, x)` (`v3rpc.mvccOk` unfolded, with the
snapshot's parts). -/
theorem mvccOk_at (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (hsrc : m.src = some (n, x)) :
    v3rpc.mvccOk r j m ⊢ ∃ (pre : List mvcc.api.WResp) (L : List v3rpc.WatchRespM)
      (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState),
      ⌜m = v3rpc.mvccResp n x m.hdr ∧ m.hdr.revision = x.rev ∧ L.length = j ∧ pre.length = n ∧
        (x.id ≠ W64 (-1) → v3rpc.idLive L x.id) ∧
        (x.id = W64 (-1) → ∀ X, v3rpc.idLive L X → X ≠ W64 (-1) → (S.ws !! X).isSome) ∧
        (x.evs ≠ [] → v3rpc.sentEvsOf L x.id ++ [x] =
          ((pre ++ [x]).filter (fun y => decide (y.id = x.id))).filter
            (fun y => decide (y.evs ≠ []))) ∧
        (∀ m' ∈ L, ∀ y, m'.src ≠ some (n, y)) ∧ v3rpc.fwdIdx L n x ∧
        (∀ X, v3rpc.fwdEvs L pre x X) ∧ mvcc.api.wsRecvOk σ S (pre ++ [x]) ∧
        (∀ id w, S.ws !! id = some w → w.fs = [])⌝ ∗
      monoListLbOwn r.γs.down L ∗ v3rpc.rcvLb r.γr (pre ++ [x]) ∗
      r.W.histLb σ.notifiedLog ∗ r.W.crevOk σ.crev ∗
      □ ([∗map] id ↦ w ∈ S.ws, v3rpc.regIs r.γreg id (v3rpc.regInfoOf w) ∗
        (⌜w.live = true⌝ ∨ v3rpc.cancelQ r.γs id)) := by
  iintro Hm
  iunfold v3rpc.mvccOk at Hm
  icases Hm with ⟨%n0, %x0, %pre, %L, %σ, %S, %H, #HL, #Hr, Hsnap⟩
  have hs : m.src = some (n0, x0) := by rw [H.1]; rfl
  rw [hs] at hsrc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsrc)
  unfold v3rpc.rcvSnap v3rpc.rcvSnapG
  icases Hsnap with ⟨%Hok, Hh, Hc, #Hreg⟩
  iexists pre, L, σ, S
  iframe HL Hr Hh Hc Hreg
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := H
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Hok.1, Hok.2⟩

/-- **(S3) A response of an id other than `-1` carries an id the run registered** (the draft's
`srvEventIdsAssigned2`): the snapshot's watch guarantee has the id among the stream's watchers
(`wsRecvOk`'s first conjunct), each registered (`rcvSnap`'s registry entries). -/
theorem srvEventIdsAssigned_holds (R : v3rpc.WSrv GF) (W : v3rpc.SrvW GF) :
    ⊢ srvEventIdsAssigned R W := by
  iunfold srvEventIdsAssigned
  iintro !> %r %j %n %m %x %- Hm %Hs
  obtain ⟨hsrc, hX⟩ := Hs
  ihave ⟨%pre, %L, %σ, %S, %H, -, -, -, -, #Hreg⟩ := mvccOk_at r j m n x hsrc $$ Hm
  have hok := H.2.2.2.2.2.2.2.2.2.2.1
  have hx : x ∈ pre ++ [x] := by simp
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hok.1 x hx).1 hX)
  ihave ⟨#Hr, -⟩ := BigSepM.bigSepM_lookup (Φ := fun id w => iprop(v3rpc.regIs (GF := GF) r.γreg id
    (v3rpc.regInfoOf w) ∗ (⌜w.live = true⌝ ∨ v3rpc.cancelQ r.γs id))) hw $$ Hreg
  iexists v3rpc.regInfoOf w
  iexact Hr

/-- The snapshot's watcher at a registered id: its entry is the registry's. -/
theorem snap_regInfo (γreg : GName) (cq : w64 → IProp GF) [∀ X, Persistent (cq X)]
    (S : mvcc.api.StreamState) (X : w64) (i : v3rpc.RegInfo) (w : mvcc.api.WInfo)
    (hw : S.ws !! X = some w) :
    □ ([∗map] id ↦ w ∈ S.ws, v3rpc.regIs γreg id (v3rpc.regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cq id)) ∗
      v3rpc.regIs (GF := GF) γreg X i ⊢ ⌜i = v3rpc.regInfoOf w⌝ ∗ (⌜w.live = true⌝ ∨ cq X) := by
  iintro ⟨#Hreg, #Hi⟩
  ihave ⟨#Hr, #Hl⟩ := BigSepM.bigSepM_lookup (Φ := fun id w => iprop(v3rpc.regIs (GF := GF) γreg id
    (v3rpc.regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cq id))) hw $$ Hreg
  iunfold v3rpc.regIs at Hr Hi
  ihave %He := ghostMapElem_agree _ _ _ _ _ _ $$ Hi Hr
  iframe Hl
  ipureintro; exact He

/-- **A watcher's events, from the snapshot** (the draft's `recvEvents`, with `srvWLaws`): the
`n`-th received response `x` of the id `X` registered at `i`, under the client's watch condition:
`X`'s events received up to `x` are the range's events of the revisions `[i.lo, hi)` of a
certified log, `hi` at most its length; with the down list `Ls` before the response (its length
`j`) and, for a response with events, its id's responses with events sent before it, then `x`,
those received. -/
theorem recvEvents (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (i : v3rpc.RegInfo) (hsrc : m.src = some (n, x))
    (hX : x.id ≠ W64 (-1)) :
    srvWLaws r.W ∗ v3rpc.srvOnce r.W ∗ v3rpc.mvccOk r j m ∗ v3rpc.regIs r.γreg x.id i ⊢ |={⊤}=>
      ∃ (pre : List mvcc.api.WResp) (Ls : List v3rpc.WatchRespM) (L : mvcc.Log) (hi : Nat),
        monoListLbOwn r.γs.down Ls ∗ v3rpc.rcvLb r.γr (pre ++ [x]) ∗ □ r.W.histLb L ∗
        ⌜Ls.length = j ∧ pre.length = n ∧ hi ≤ L.length ∧
          mvcc.api.recvEvs (pre ++ [x]) x.id = mvcc.watchEvents L i.rg i.lo hi ∧
          (x.evs ≠ [] → v3rpc.sentEvsOf Ls x.id ++ [x] =
            ((pre ++ [x]).filter (fun y => decide (y.id = x.id))).filter
              (fun y => decide (y.evs ≠ [])))⌝ := by
  iintro ⟨#Hl, #Ho, Hm, #Hi⟩
  ihave ⟨%pre, %Ls, %σ, %S, %H, #HLs, #Hr, Hh, Hc, #Hreg⟩ := mvccOk_at r j m n x hsrc $$ Hm
  obtain ⟨-, -, hLs, hpre, -, -, hfilt, -, -, -, hok, hfs⟩ := H
  iunfold srvWLaws at Hl
  icases Hl with ⟨#Hhp, -, -, -, #Hcp⟩
  ihave #Hh := Hhp $$ Hh
  ihave #Hc := Hcp $$ Hc
  have hx : x ∈ pre ++ [x] := by simp
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hok.1 x hx).1 hX)
  ihave ⟨%Hiw, -⟩ := snap_regInfo r.γreg (v3rpc.cancelQ r.γs) S x.id i w hw $$ [Hreg Hi]
  · iframe #
  iunfold v3rpc.srvOnce at Ho
  imod Ho $$ %σ.notifiedLog %σ.crev %w.lo Hh Hc with %Hon
  obtain ⟨hi, hhi, hev⟩ := hok.2.1 x.id w hw Hon
  rw [hfs x.id w hw, filtered_nil] at hev
  imodintro
  iexists pre, Ls, σ.notifiedLog, hi
  iframe HLs Hr Hh
  ipureintro
  subst Hiw
  exact ⟨hLs, hpre, hhi, hev, hfilt⟩

/-- **A watcher covered by a progress response** (persistent): the `n`-th received response `x`
(after `pre`) of the watch id `X` (registered with the range `rg` and first revision `lo`) has its
id's received events up to it exactly the range's events up to its revision of a certified log
`L`, which reaches that revision; the first revision at most one past it; and what was forwarded
of `X` before it, sent after the responses `Lj` (`fwdEvs`). -/
def progCovd (r : v3rpc.WRun GF) (Lj : List v3rpc.WatchRespM) (n : Nat) (x : mvcc.api.WResp)
    (X : w64) (rg : mvcc.WatchRange) (lo : Nat) : IProp GF :=
  iprop(∃ (pre : List mvcc.api.WResp) (L : mvcc.Log), v3rpc.rcvLb r.γr (pre ++ [x]) ∗
    □ r.W.histLb L ∗ ⌜pre.length = n ∧
      mvcc.api.recvEvs (pre ++ [x]) X = mvcc.watchEvents L rg lo (sint.nat x.rev + 1) ∧
      (lo : Int) ≤ sint.Z x.rev + 1 ∧ sint.nat x.rev < L.length ∧ v3rpc.fwdEvs Lj pre x X⌝)

instance progCovd_persistent (r : v3rpc.WRun GF) (Lj : List v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (X : w64) (rg : mvcc.WatchRange) (lo : Nat) :
    Persistent (progCovd r Lj n x X rg lo) := by
  unfold progCovd; infer_instance

/-- **A progress response's coverage** (the draft's `progressCov`, with `srvWLaws`, stated over
the created response's facts `createdAfter` gives): an event-less, non-compaction response `x`
(the `n`-th received, sent at `j`) of the watch id `X` (registered at `i`, its created response's
snapshot `l` of the received list, at least its stamp `i.k`, whose `-1` responses were sent among
`Lc`, sent before `j`), `X` live after the `j` responses `Lj` sent before it, `x` its own or the
stream's `-1`: `X`'s events received up to `x` are exactly the range's events up to `x`'s revision
of a certified log, or (for `-1`) the client asked to cancel `X`. -/
theorem progressCov (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (X : w64) (i : v3rpc.RegInfo) (l : List mvcc.api.WResp)
    (Lc Lj : List v3rpc.WatchRespM) (hsrc : m.src = some (n, x)) (hev : x.evs = [])
    (hcmp : x.compactRev = W64 0) (hX : X ≠ W64 (-1)) (hk : i.k ≤ l.length) (hLc : Lc <+: Lj)
    (hj : Lj.length = j)
    (hl : ∀ (n' : Nat) (y : mvcc.api.WResp), l[n']? = some y → y.id = W64 (-1) →
      ∃ m' ∈ Lc, m'.src = some (n', y))
    (hlive : v3rpc.idLive Lj X) (hid : x.id = X ∨ x.id = W64 (-1)) :
    srvWLaws r.W ∗ v3rpc.srvOnce r.W ∗ v3rpc.mvccOk r j m ∗ v3rpc.regIs r.γreg X i ∗
      v3rpc.rcvLb r.γr l ∗ monoListLbOwn r.γs.down Lj ⊢ |={⊤}=>
      (progCovd r Lj n x X i.rg i.lo ∨ (⌜x.id = W64 (-1)⌝ ∗ v3rpc.cancelQ r.γs X)) := by
  iintro ⟨#Hl, #Ho, Hm, #Hi, #Hrl, #HLj⟩
  ihave ⟨%pre, %Ls, %σ, %S, %H, #HLs, #Hr, Hh, Hc, #Hreg⟩ := mvccOk_at r j m n x hsrc $$ Hm
  obtain ⟨-, -, hLs, hpre, hown, hbc, -, hnot, -, hfwe, hok, hfs⟩ := H
  -- the down list before the response is the client's
  ihave %Hdc := mono_list_lb_valid r.γs.down Ls Lj $$ HLs HLj
  have hLeq : Ls = Lj := eq_of_comparable Hdc (by rw [hLs, hj])
  subst hLeq
  iunfold srvWLaws at Hl
  icases Hl with ⟨#Hhp, -, -, -, #Hcp⟩
  ihave #Hh := Hhp $$ Hh
  ihave #Hc := Hcp $$ Hc
  -- `X` is a watcher of the snapshot
  have hXs : (S.ws !! X).isSome := by
    rcases hid with h | h
    · have hx : x ∈ pre ++ [x] := by simp
      rw [← h]; exact (hok.1 x hx).1 (by rw [h]; exact hX)
    · exact hbc h X hlive hX
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hXs
  ihave ⟨%Hiw, #Hlv⟩ := snap_regInfo r.γreg (v3rpc.cancelQ r.γs) S X i w hw $$ [Hreg Hi]
  · iframe #
  subst Hiw
  have hxn : (pre ++ [x])[n]? = some x := by
    rw [List.getElem?_append_right (by omega), hpre]; simp
  have htake : (pre ++ [x]).take (n + 1) = pre ++ [x] := by
    rw [List.take_of_length_le]; simp [hpre]
  -- the conclusion, once the guarantee's third conjunct applies
  have hfin : ∀ (hc : x.id = X ∨ (x.id = W64 (-1) ∧ w.live = true ∧ w.k ≤ n)),
      mvcc.api.onceUpTo σ.notifiedLog w.lo σ.crev →
      mvcc.api.recvEvs (pre ++ [x]) X =
        mvcc.watchEvents σ.notifiedLog w.rg w.lo (sint.nat x.rev + 1) ∧
        (w.lo : Int) ≤ sint.Z x.rev + 1 ∧ sint.nat x.rev < σ.notifiedLog.length := by
    intro hc hon
    have h3 := hok.2.2 n x X w hxn hev hcmp hw hon hc
    rw [htake, hfs X w hw, filtered_nil] at h3
    exact ⟨h3, wsRecvOk_progLo σ S _ hok n x X w hxn hev hcmp hw hc,
      (hok.1 x (by simp)).2.2.1 hcmp⟩
  iunfold v3rpc.srvOnce at Ho
  rcases hid with hown' | hm1
  · imod Ho $$ %σ.notifiedLog %σ.crev %w.lo Hh Hc with %Hon
    imodintro
    ileft
    unfold progCovd
    iexists pre, σ.notifiedLog
    iframe Hr Hh
    ipureintro
    have hf := hfin (Or.inl hown') Hon
    exact ⟨hpre, hf.1, hf.2.1, hf.2.2, hfwe X⟩
  icases Hlv with (%Hlive | #Hq)
  · -- live: registered before the response was received (`createdAfter`'s snapshot `l`)
    iunfold v3rpc.rcvLb at Hrl Hr
    ihave %Hrc := mono_list_lb_valid r.γr l (pre ++ [x]) $$ Hrl Hr
    have hkn : w.k ≤ n := by
      refine Classical.byContradiction fun hc => ?_
      have hnl : n < l.length := by
        have : w.k ≤ l.length := hk
        omega
      have hln : l[n]? = some x := getElem?_of_comparable Hrc hnl hxn
      obtain ⟨m', hm', hs'⟩ := hl n x hln hm1
      exact hnot m' (hLc.subset hm') x hs'
    imod Ho $$ %σ.notifiedLog %σ.crev %w.lo Hh Hc with %Hon
    imodintro
    ileft
    unfold progCovd
    iexists pre, σ.notifiedLog
    iunfold v3rpc.rcvLb
    iframe Hr Hh
    ipureintro
    have hf := hfin (Or.inr ⟨hm1, Hlive, hkn⟩) Hon
    exact ⟨hpre, hf.1, hf.2.1, hf.2.2, hfwe X⟩
  · imodintro
    iright
    iframe Hq
    ipureintro; exact hm1

/-- **Event-less responses' revisions do not decrease** (`wsRecvOk_progMono`, a placeholder): an
event-less response `y` received before the `n`-th received one `x` (event-less, not a
compaction's) is at a revision at most `x`'s. -/
theorem progRev (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (prey : List mvcc.api.WResp) (y : mvcc.api.WResp)
    (hsrc : m.src = some (n, x)) (hlt : prey.length < n) (hye : y.evs = []) (hxe : x.evs = [])
    (hxc : x.compactRev = W64 0) :
    v3rpc.mvccOk r j m ∗ v3rpc.rcvLb r.γr (prey ++ [y]) ⊢ ⌜sint.Z y.rev ≤ sint.Z x.rev⌝ := by
  iintro ⟨Hm, #Hy⟩
  ihave ⟨%pre, %Ls, %σ, %S, %H, -, #Hr, -, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hm
  have hpre := H.2.2.2.1
  have hok := H.2.2.2.2.2.2.2.2.2.2.1
  iunfold v3rpc.rcvLb at Hr Hy
  ihave %Hc := mono_list_lb_valid r.γr (pre ++ [x]) (prey ++ [y]) $$ Hr Hy
  have hy : (prey ++ [y])[prey.length]? = some y := by simp
  have h1 : (pre ++ [x])[prey.length]? = some y :=
    getElem?_of_comparable Hc (by simp; omega) hy
  have hxn : (pre ++ [x])[n]? = some x := by
    rw [List.getElem?_append_right (by omega), hpre]; simp
  ipureintro
  exact wsRecvOk_progMono σ S _ hok prey.length n y x hlt h1 hxn hye hxe hxc

/-- **An mvcc response is duplicable** (its snapshot's certified log and compaction permit, by
the server's laws `srvWLaws`). -/
theorem mvccOk_dup (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) :
    srvWLaws r.W ∗ v3rpc.mvccOk r j m ⊢ □ v3rpc.mvccOk r j m := by
  iintro ⟨#Hl, Hm⟩
  iunfold v3rpc.mvccOk at Hm
  icases Hm with ⟨%n, %x, %pre, %L, %σ, %S, %H, #HL, #Hr, Hsnap⟩
  unfold v3rpc.rcvSnap v3rpc.rcvSnapG
  icases Hsnap with ⟨%Hok, Hh, Hc, #Hreg⟩
  iunfold srvWLaws at Hl
  icases Hl with ⟨#Hhp, -, -, -, #Hcp⟩
  ihave #Hh := Hhp $$ Hh
  ihave #Hc := Hcp $$ Hc
  iintro !>
  iunfold v3rpc.mvccOk
  iexists n, x, pre, L, σ, S
  iframe HL Hr
  isplitr
  · ipureintro; exact H
  unfold v3rpc.rcvSnap v3rpc.rcvSnapG
  iframe Hh Hc Hreg
  ipureintro; exact Hok

/-- **A compaction response** (the draft's `compactResp`): no events, its watcher's, at revision
`0`, its compaction revision positive and at most a permitted one (`crevOk`, at the snapshot's
state). -/
theorem compactResp (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (hsrc : m.src = some (n, x)) (hc : x.compactRev ≠ W64 0) :
    v3rpc.mvccOk r j m ⊢ ∃ c : Int, r.W.crevOk c ∗ ⌜x.evs = [] ∧ x.id ≠ W64 (-1) ∧
      x.rev = W64 0 ∧ 0 < sint.Z x.compactRev ∧ sint.Z x.compactRev ≤ c⌝ := by
  iintro Hm
  ihave ⟨%pre, %Ls, %σ, %S, %H, -, -, -, Hc, -⟩ := mvccOk_at r j m n x hsrc $$ Hm
  have hok := H.2.2.2.2.2.2.2.2.2.2.1
  have hx : x ∈ pre ++ [x] := by simp
  obtain ⟨h1, h2, h3, h4, h5⟩ := (hok.1 x hx).2.2.2.1 hc
  iexists σ.crev
  iframe Hc
  ipureintro; exact ⟨h1, h2, h3, h4, h5⟩

/-- **A response that is not a compaction's is at a revision of a certified log** (in place of
`mvccOk_revLb`'s `notifiedLb`): the snapshot's notified log, past the response's revision. -/
theorem mvccOk_revLb (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (hsrc : m.src = some (n, x)) (hc : x.compactRev = W64 0) :
    v3rpc.mvccOk r j m ⊢ ∃ L : mvcc.Log, r.W.histLb L ∗ ⌜sint.nat x.rev < L.length⌝ := by
  iintro Hm
  ihave ⟨%pre, %Ls, %σ, %S, %H, -, -, Hh, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hm
  have hok := H.2.2.2.2.2.2.2.2.2.2.1
  have hx : x ∈ pre ++ [x] := by simp
  iexists σ.notifiedLog
  iframe Hh
  ipureintro; exact (hok.1 x hx).2.2.1 hc

/-- **A `-1` response is progress at a positive revision**, without events (the snapshot's
watch guarantee). -/
theorem mvccOk_bcast (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (hsrc : m.src = some (n, x)) (h1 : x.id = W64 (-1)) :
    v3rpc.mvccOk r j m ⊢ ⌜x.evs = [] ∧ x.compactRev = W64 0 ∧ 1 ≤ sint.Z x.rev⌝ := by
  iintro Hm
  ihave ⟨%pre, %Ls, %σ, %S, %H, -, -, -, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hm
  have hok := H.2.2.2.2.2.2.2.2.2.2.1
  have hx : x ∈ pre ++ [x] := by simp
  ipureintro; exact (hok.1 x hx).2.2.2.2.1 h1

/-- **An mvcc response's events are positive, each at or below its revision** (the snapshot's
watch guarantee's first conjunct). -/
theorem mvccOk_evs (r : v3rpc.WRun GF) (j : Nat) (m : v3rpc.WatchRespM) (n : Nat)
    (x : mvcc.api.WResp) (hsrc : m.src = some (n, x)) :
    v3rpc.mvccOk r j m ⊢ ⌜(∀ ev ∈ x.evs, sint.Z ev.kv.modRev ≤ sint.Z x.rev) ∧
      ∀ ev ∈ x.evs, 0 < sint.Z ev.kv.modRev ∧
        (ev.del = false → 0 < sint.Z ev.kv.createRev ∧ 0 < sint.Z ev.kv.version)⌝ := by
  iintro Hm
  ihave ⟨%pre, %Ls, %σ, %S, %H, -, -, -, -, -⟩ := mvccOk_at r j m n x hsrc $$ Hm
  have hok := H.2.2.2.2.2.2.2.2.2.2.1
  have hx : x ∈ pre ++ [x] := by simp
  ipureintro; exact ⟨(hok.1 x hx).2.1, (hok.1 x hx).2.2.2.2.2⟩

end bridges

end client
end EtcdGrove
end Perennial
