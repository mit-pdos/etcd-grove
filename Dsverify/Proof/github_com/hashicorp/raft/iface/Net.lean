/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/iface/Net.lean (241f27e).
-/
/-
Interface (redesign R1): the contract between `raft` and its `Transport` (hr3's `inproc`), and the
predicates on the messages.

A request carries its protocol validity as persistent facts (`gprot.aeValid`, `gprot.candIs`);
a response carries the responder's facts (`gprot.ackIs`, `gprot.voteIs`, `gprot.termOk`). The
receiving server `j` gets requests on its RPC channel (`isRpcChan γ j ch`, a bag of `RPC` values)
with a response channel on which it sends one `RPCResponse` satisfying the response predicate for
responder `j`. Request and response structs are deep copies, owned by their receiver.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.iface.Stores
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section pure
variable [GooseExts]

/-- `appendUint64`: 8 bytes, little-endian. -/
def le64 (x : w64) : List w8 :=
  (List.range 8).map (fun j => (x >>> (8 * j)).setWidth 8)

/-- `encodeConfigurationBytes` of the servers `ss` (`EncodeConfiguration`). -/
def encodeServers (ss : List Server) : List w8 :=
  le64 (W64 ss.length) ++
    ss.flatMap (fun s => le64 s.Suffrage' ++ le64 (W64 s.ID'.length) ++ s.ID' ++
      le64 (W64 s.Address'.length) ++ s.Address')

/-- (stage 4) The voters of the servers `ss` (suffrage `Voter`, `0`), in order. -/
def srvVoters (ss : List Server) : List SID :=
  (ss.filter (fun s => decide (s.Suffrage' = W64 0))).map (fun s => (s.ID' : List w8))

/-- (stage 4) The IDs of the servers `ss`, in order. -/
def srvIds (ss : List Server) : List SID := ss.map (fun s => (s.ID' : List w8))

/-- (stage 4; stage 3: `srvsOk γ ss`, the bootstrap servers, one `Voter` per server) **A valid
configuration over the servers `S`** (what `checkConfiguration` accepts, in scope): distinct IDs, each
one of `S`, non-empty and shorter than `2^63` bytes, each its own address, suffrage `Voter` or
`Nonvoter` (no `Staging`: out of scope), at least one voter, fewer than `2^32` servers
(`make(chan …, len(servers))` in `electSelf`/`preElectSelf`). -/
def srvsOkIn (S : List SID) (ss : List Server) : Prop :=
  (srvIds ss).Nodup ∧ (∀ j ∈ srvIds ss, j ∈ S) ∧
  (∀ s ∈ ss, (s.Suffrage' = W64 0 ∨ s.Suffrage' = W64 1) ∧ s.Address' = s.ID' ∧ s.ID' ≠ [] ∧
    s.ID'.length < 2 ^ 63) ∧
  srvVoters ss ≠ [] ∧ ss.length < 2 ^ 32

/-- (stage 4) A valid configuration of protocol `γ` (over its servers `γ.srvs`). -/
abbrev srvsOk (γ : GNames) (ss : List Server) : Prop := srvsOkIn γ.srvs ss

/-- (stage 4) The servers encoded in the configuration data `d`, if `d` encodes a valid configuration
over `S` (`DecodeConfiguration`), else `[]`. -/
def cfgServers (S : List SID) (d : List w8) : List Server := by
  classical
  exact if h : ∃ ss : List Server, encodeServers ss = d ∧ srvsOkIn S ss then Classical.choose h else []

/-- (stage 4) **The voters of an encoded configuration** over the servers `S` (`[]` for data that encodes
no valid configuration): the decoding the protocol fixes (`GNames.cv = cfgDec γ.srvs`,
`proto.PState.cv`; `isRaft_cv`). A configuration entry of the protocol has valid voters
(`proto.ICfgOk`, `cfgValid`), so its data encodes a valid configuration (`cfgDec_valid`). -/
def cfgDec (S : List SID) (d : List w8) : List SID := srvVoters (cfgServers S d)

/-- (stage 4) Decoding an encoded valid configuration gives its servers back (`encodeServers` is
injective on servers with lengths below `2^63`). -/
theorem cfgServers_encode (S : List SID) (ss : List Server) (h : srvsOkIn S ss) :
    cfgServers S (encodeServers ss) = ss := by
  have le64_inj : ∀ x y : w64, le64 x = le64 y → x = y := by
    -- bitwise (no `bv_decide`: its SAT certificates add `_native` axioms to the results)
    intro x y h
    have hm : ∀ j ∈ List.range 8, (x >>> (8 * j)).setWidth 8 = (y >>> (8 * j)).setWidth 8 :=
      List.map_inj_left.mp h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hj := hm (i / 8) (by simp; omega)
    have hb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hj
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at hb
    have e : 8 * (i / 8) + i % 8 = i := by omega
    have : i % 8 < 8 := by omega
    simp only [this, decide_true, Bool.true_and] at hb
    simp only [e] at hb
    simpa [BitVec.getLsbD_eq_getElem hi] using hb
  have le64_len : ∀ x : w64, (le64 x).length = 8 := fun x => by simp [le64]
  have w64_inj : ∀ a b : Nat, a < 2 ^ 63 → b < 2 ^ 63 → W64 (a : Int) = W64 (b : Int) → a = b := by
    intro a b ha hb hab
    have := congrArg (fun w : w64 => w.toNat) hab
    simp only [W64, BitVec.toNat_ofInt] at this
    omega
  -- one server's encoding, followed by anything
  have srv_inj : ∀ (s1 s2 : Server) (r1 r2 : List w8),
      s1.ID'.length < 2 ^ 63 → s1.Address'.length < 2 ^ 63 →
      s2.ID'.length < 2 ^ 63 → s2.Address'.length < 2 ^ 63 →
      (le64 s1.Suffrage' ++ le64 (W64 s1.ID'.length) ++ s1.ID' ++ le64 (W64 s1.Address'.length) ++
        s1.Address') ++ r1 =
      (le64 s2.Suffrage' ++ le64 (W64 s2.ID'.length) ++ s2.ID' ++ le64 (W64 s2.Address'.length) ++
        s2.Address') ++ r2 → s1 = s2 ∧ r1 = r2 := by
    intro s1 s2 r1 r2 a1 b1 a2 b2 he
    simp only [List.append_assoc] at he
    obtain ⟨e1, he⟩ := List.append_inj he (by rw [le64_len, le64_len])
    obtain ⟨e2, he⟩ := List.append_inj he (by rw [le64_len, le64_len])
    have l2 := w64_inj _ _ a1 a2 (le64_inj _ _ e2)
    obtain ⟨e3, he⟩ := List.append_inj he l2
    obtain ⟨e4, he⟩ := List.append_inj he (by rw [le64_len, le64_len])
    have l4 := w64_inj _ _ b1 b2 (le64_inj _ _ e4)
    obtain ⟨e5, he⟩ := List.append_inj he l4
    refine ⟨?_, he⟩
    cases s1; cases s2
    simp only at le64_inj e1 e3 e5
    rw [le64_inj _ _ e1, e3, e5]
  have flat_inj : ∀ l1 l2 : List Server, l1.length = l2.length →
      (∀ s ∈ l1, s.ID'.length < 2 ^ 63 ∧ s.Address'.length < 2 ^ 63) →
      (∀ s ∈ l2, s.ID'.length < 2 ^ 63 ∧ s.Address'.length < 2 ^ 63) →
      l1.flatMap (fun s => le64 s.Suffrage' ++ le64 (W64 s.ID'.length) ++ s.ID' ++
        le64 (W64 s.Address'.length) ++ s.Address') =
      l2.flatMap (fun s => le64 s.Suffrage' ++ le64 (W64 s.ID'.length) ++ s.ID' ++
        le64 (W64 s.Address'.length) ++ s.Address') → l1 = l2 := by
    intro l1
    induction l1 with
    | nil => intro l2 hl _ _ _; cases l2 <;> simp_all
    | cons s1 t1 ih =>
      intro l2 hl b1 b2 he
      cases l2 with
      | nil => simp at hl
      | cons s2 t2 =>
        simp only [List.flatMap_cons] at he
        have bs1 := b1 s1 (by simp)
        have bs2 := b2 s2 (by simp)
        obtain ⟨rfl, hr⟩ := srv_inj s1 s2 _ _ bs1.1 bs1.2 bs2.1 bs2.2 he
        rw [ih t2 (by simpa using hl) (fun s hs => b1 s (by simp [hs]))
          (fun s hs => b2 s (by simp [hs])) hr]
  have enc_inj : ∀ ss' : List Server, srvsOkIn S ss' → encodeServers ss' = encodeServers ss → ss' = ss := by
    intro ss' h' he
    unfold encodeServers at he
    obtain ⟨e0, he⟩ := List.append_inj he (by rw [le64_len, le64_len])
    have hl := w64_inj _ _ (by have := h'.2.2.2.2; omega) (by have := h.2.2.2.2; omega) (le64_inj _ _ e0)
    have bnd : ∀ ss0 : List Server, srvsOkIn S ss0 →
        ∀ s ∈ ss0, s.ID'.length < 2 ^ 63 ∧ s.Address'.length < 2 ^ 63 := by
      intro ss0 h0 s hs
      obtain ⟨_, ha, _, hlen⟩ := (h0.2.2.1 s hs)
      exact ⟨hlen, by rw [ha]; exact hlen⟩
    exact flat_inj ss' ss hl (bnd ss' h') (bnd ss h) he
  unfold cfgServers
  have hex : ∃ ss' : List Server, encodeServers ss' = encodeServers ss ∧ srvsOkIn S ss' := ⟨ss, rfl, h⟩
  rw [dite_cond_eq_true (eq_true hex)]
  have hs := Classical.choose_spec hex
  exact enc_inj _ hs.2 hs.1

/-- (stage 4) The voters of an encoded valid configuration. -/
theorem cfgDec_encode (S : List SID) (ss : List Server) (h : srvsOkIn S ss) :
    cfgDec S (encodeServers ss) = srvVoters ss := by
  unfold cfgDec; rw [cfgServers_encode S ss h]

/-- (stage 4) Data with voters encodes a valid configuration (the decoding of a protocol
configuration entry, `DecodeConfiguration`'s premise). -/
theorem cfgDec_valid (S : List SID) (d : List w8) (h : cfgDec S d ≠ []) :
    ∃ ss : List Server, d = encodeServers ss ∧ srvsOkIn S ss := by
  unfold cfgDec cfgServers at h
  by_cases hex : ∃ ss : List Server, encodeServers ss = d ∧ srvsOkIn S ss
  · obtain ⟨ss, h1, h2⟩ := hex
    exact ⟨ss, h1.symm, h2⟩
  · rw [dite_cond_eq_false (eq_false hex)] at h
    exact absurd rfl h

/-- (stage 4) A valid configuration's voters are a valid configuration of the protocol
(`proto.cfgValid`). -/
theorem srvsOk_cfgValid (S : List SID) (ss : List Server) (h : srvsOkIn S ss) :
    cfgValid S (srvVoters ss) := by
  obtain ⟨hnd, hS, -, hne, -⟩ := h
  have hsub : (srvVoters ss).Sublist (srvIds ss) := by
    unfold srvVoters srvIds
    exact (List.filter_sublist).map _
  exact ⟨hne, hsub.nodup hnd, fun j hj => hS j (hsub.subset hj)⟩

end pure

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-! ## Countability of the channel element types -/

instance rpcResponse_countable : Pos.Countable RPCResponse :=
  Pos.Countable.ofInjective (fun r => Pos.Countable.encode (r.Response', r.Error'))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2; rfl)

instance rpc_countable : Pos.Countable RPC :=
  Pos.Countable.ofInjective (fun r => Pos.Countable.encode (r.Command', r.Reader', r.RespChan'))
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)

/-! ## Message contents -/

/-- An RPC header: protocol version 3 (`DefaultConfig`), `ID` and `Addr` the sender's id bytes. -/
def hdrOk (h : RPCHeader) (snd : SID) : IProp GF :=
  iprop(⌜h.ProtocolVersion' = W64 3⌝ ∗ h.ID' ↦*□ snd ∗ h.Addr' ↦*□ snd)

/-- An AppendEntries request of term `T` from `snd` with previous entry `(prev, pt)`, entries
`ents` (pointers to read-only `Log`s at indexes `prev+1..`) and leader commit index `lci`, valid
in the protocol; (stage 2) sent after the snapshot `ss` (`histLb`: the sender took it before it
sent; a success response is from a later snapshot, `respWit`). -/
def aeReq (γ : GNames) (rq : AppendEntriesRequest) (snd : SID) (T prev pt : Nat) (ents : RLog)
    (lci : Nat) (ss : Snap) : IProp GF :=
  iprop(⌜uint.nat rq.Term' = T ∧ uint.nat rq.PrevLogEntry' = prev ∧ uint.nat rq.PrevLogTerm' = pt ∧
      uint.nat rq.LeaderCommitIndex' = lci⌝ ∗
    hdrOk rq.RPCHeader' snd ∗ rq.Leader' ↦*□ snd ∗
    (∃ ptrs : List Loc, rq.Entries' ↦*□ ptrs ∗ ⌜ptrs.length = ents.length⌝ ∗
      [∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e) ∗
    aeValid γ T prev pt ents lci ∗ histLb γ ss)

/-- (stage 2) The request is a **heartbeat** (upstream's `NetworkTransport`, examples/inproc's
`heartbeatFn`): no previous entry, no entries, no commit index. A transport may hand it to the
receiver's heartbeat handler (`hbHandler`) instead of its RPC channel. -/
def isHb (prev : Nat) (ents : RLog) (lci : Nat) : Prop := prev = 0 ∧ ents = [] ∧ lci = 0

/-- (stage 2) **A responder's term witness**: at a snapshot after the request's snapshot `ss`, the
responder `j`'s term was `T` (it answered in `T`). What VerifyLeader's quorum is made of. -/
def respWit (γ : GNames) (j : SID) (T : Nat) (ss : Snap) : IProp GF :=
  iprop(∃ sq : Snap, histLb γ sq ∗ ⌜snapLe ss sq ∧ sq.term j = T⌝)

/-- An AppendEntries response of responder `j` to a request of term `T` whose last index is `k`,
sent after the snapshot `ss`: its term is an existing one; success means `j` was in term `T` after
`ss` (`respWit`, stage 2) and, unless the request is a heartbeat (`hb`: the heartbeat handler
answers without acknowledging, processHeartbeat), `j` acknowledged `llog T [1..k]` in term `T`. -/
def aeResp (γ : GNames) (rp : AppendEntriesResponse) (j : SID) (T k : Nat) (hb : Prop) (ss : Snap) :
    IProp GF :=
  iprop(termOk γ (uint.nat rp.Term') ∗
    (⌜rp.Success' = false⌝ ∨ (⌜hb⌝ ∨ ackIs γ j T k) ∗ respWit γ j T ss) ∗
    (∃ snd : SID, hdrOk rp.RPCHeader' snd))

/-- A RequestVote of term `T` from candidate `c` with last entry `(li, lt)`, as recorded
(`LeadershipTransfer` any: stage 2, a candidate from a leadership transfer sets it). -/
def rvReq (γ : GNames) (rq : RequestVoteRequest) (c : SID) (T li lt : Nat) : IProp GF :=
  iprop(⌜uint.nat rq.Term' = T ∧ uint.nat rq.LastLogIndex' = li ∧ uint.nat rq.LastLogTerm' = lt⌝ ∗
    hdrOk rq.RPCHeader' c ∗ rq.Candidate' ↦*□ c ∗ candIs γ c T li lt)

/-- A RequestVote response of `j`: an existing term; granted means `j` voted for `c` in `T`. -/
def rvResp (γ : GNames) (rp : RequestVoteResponse) (j c : SID) (T : Nat) : IProp GF :=
  iprop(termOk γ (uint.nat rp.Term') ∗ (⌜rp.Granted' = false⌝ ∨ voteIs γ j T c) ∗
    (∃ b : List w8, rp.Peers' ↦*□ b) ∗ (∃ snd : SID, hdrOk rp.RPCHeader' snd))

/-- A pre-vote request of term `T` (no protocol effect). -/
def pvReq (rq : RequestPreVoteRequest) (c : SID) (T : Nat) : IProp GF :=
  iprop(⌜uint.nat rq.Term' = T⌝ ∗ hdrOk rq.RPCHeader' c)

/-- (stage 2) A TimeoutNow request from `c` (`initiateLeadershipTransfer`: header only; no protocol
facts, the receiver only starts an election, `timeoutNow`). -/
def tnReq (rq : TimeoutNowRequest) (c : SID) : IProp GF := hdrOk rq.RPCHeader' c

/-- A pre-vote response to a request of term `T`: the request's term or an existing one. -/
def pvResp (γ : GNames) (rp : RequestPreVoteResponse) (T : Nat) : IProp GF :=
  iprop((⌜uint.nat rp.Term' = T⌝ ∨ termOk γ (uint.nat rp.Term')) ∗ (∃ snd : SID, hdrOk rp.RPCHeader' snd))

/-- (stage 4) The committed entries at the indexes strictly between `k0` and `k` are no configuration
entries (persistent). -/
def noCfgBetween (γ : GNames) (k0 k : Nat) : IProp GF :=
  iprop([∗list] x ∈ List.range' (k0 + 1) (k - (k0 + 1)),
    ∃ e' : Entry, CIdx γ x e' ∗ ⌜e'.kind ≠ kConfig⌝)

instance noCfgBetween_persistent γ k0 k : Persistent (noCfgBetween (GF := GF) γ k0 k) := by
  unfold noCfgBetween; infer_instance

/-- (stage 4; stage 3: the bootstrap configuration at index 1) **The configuration of the committed log
at `s`** (persistent; a snapshot's, `proto.snap_cfg`): the committed configuration entry at
`1 ≤ ci ≤ s` encodes the valid configuration `ss`, and no committed configuration entry lies in
`(ci, s]`. What a snapshot's meta and an install request carry (`takeSnapshot` takes the committed
configuration, refusing one above the snapshot's index). -/
def snapCfg (γ : GNames) (s ci : Nat) (ss : List Server) : IProp GF :=
  iprop(⌜1 ≤ ci ∧ ci ≤ s ∧ srvsOk γ ss⌝ ∗
    (∃ e : Entry, CIdx γ ci e ∗ ⌜e.kind = kConfig ∧ e.data = encodeServers ss⌝) ∗
    noCfgBetween γ ci (s + 1))

instance snapCfg_persistent γ s ci ss : Persistent (snapCfg (GF := GF) γ s ci ss) := by
  unfold snapCfg; infer_instance

/-- (stage 3) **An InstallSnapshot request** of term `T` from `snd` to `j` (`sendLatestSnapshot`,
the replication goroutine of `snd`'s term `T`, which checked its term after opening the snapshot: fix
`5894fa2`, D31) for the snapshot `(s, st)`, `s ≥ 1`, with bytes `b`: the header; version 1; the leader
of `T` is `snd ≠ j`; the install is valid as an AppendEntries of `T` with previous entry `(s, st)`, no
entries and commit index `s` (`aeValid γ T s st [] s`: `llog T [s]` has term `st`, `s` is covered by
a recorded commit of a term `≤ T` agreeing with `llog T`, and by a publication of a term `≤ T`); (stage 4;
stage 3: the bootstrap configuration at index 1) the configuration and its index are the committed
log's at `s` (`snapCfg`: the encoded valid configuration `ss` of the committed entry at
`ConfigurationIndex ≤ s`, no committed configuration entry after it up to `s`); `Size = |b|`; `Peers`
some read-only bytes. -/
def isReq (γ : GNames) (rq : InstallSnapshotRequest) (snd j : SID) (T s st : Nat) (b : List w8) :
    IProp GF :=
  iprop(⌜uint.nat rq.Term' = T ∧ uint.nat rq.LastLogIndex' = s ∧ uint.nat rq.LastLogTerm' = st ∧
      rq.SnapshotVersion' = W64 1 ∧ uint.nat rq.Size' = b.length ∧
      snd ≠ j ∧ 1 ≤ s⌝ ∗
    hdrOk rq.RPCHeader' snd ∗ rq.Leader' ↦*□ snd ∗ (∃ pb : List w8, rq.Peers' ↦*□ pb) ∗
    (∃ ss : List Server, rq.Configuration' ↦*□ encodeServers ss ∗
      snapCfg γ s (uint.nat rq.ConfigurationIndex') ss) ∗
    leaderIs γ T snd ∗ aeValid γ T s st [] s)

/-- (stage 3) An InstallSnapshot response: an existing term, and a header whose `ID`/`Addr` are
read-only bytes (no protocol facts: the sender keeps the request's own, which its commitment counts
on success). (SNAP-1) The receiver builds the response without a header (raft.go, as upstream): the
zero header, `ProtocolVersion = 0`, `ID`/`Addr` nil; so no `hdrOk`, as `TimeoutNowResponse`'s. -/
def isResp (γ : GNames) (rp : InstallSnapshotResponse) : IProp GF :=
  iprop(termOk γ (uint.nat rp.Term') ∗
    ∃ id ad : List w8, rp.RPCHeader'.ID' ↦*□ id ∗ rp.RPCHeader'.Addr' ↦*□ ad)

/-- (stage 3) **The snapshot stream of an InstallSnapshot** (`RPC.Reader` on the receiver's side;
the `data` reader on the sender's): a reader that never fails (`streamReaderOk`, with `io.EOF`'s value
`eof`) of the bytes `b` of a snapshot of `s` (`snapP s b`, the FSM's meaning, the same at every
server), whose dynamic type is not an `io.WriterTo` (so `io.Copy` reads it with `Read`), and shorter
than `2^63` bytes (`io.Copy`'s premise; the store's latest has it, `core.latestOk`). -/
def snapStream (rd : GoInterfaceOk) (snapP : Nat → List w8 → IProp GF) (s : Nat) (b : List w8) :
    IProp GF :=
  iprop(∃ (R : List w8 → IProp GF) (eof : GoInterface), streamReaderOk rd R eof ∗ R b ∗
    globalAddr io.EOF ↦□ eof ∗ ⌜go.typeSetContains rd.ty io.WriterTo.ty = false⌝ ∗ snapP s b ∗
    ⌜b.length < 2 ^ 63⌝)

/-! ## Errors -/

/-- **An error value with a callable `Error()`** (persistent): non-nil, and its `Error()` method
returns some string (e.g. an `errors.New` or `fmt.Errorf` value). What the transport returns as
an error, and what a responder sends as an error response. -/
def errOk (err : GoInterface) : IProp GF :=
  iprop(∃ x : GoInterfaceOk, ⌜err = GoInterface.ok x⌝ ∗
    □ ∀ Φ : val → IProp GF, (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods x.ty go!"Error" x.v)) (Val #())) {{ Φ }})

instance errOk_persistent err : Persistent (errOk (GF := GF) err) := by
  unfold errOk; infer_instance

/-- (stage 2, D25, D26) **An error value that implements `error` and has no `Format` method**
(pure): its `Error` method has Go's `error` signature `Error() string` (`errOk` asks only for a
method named `Error`; fmt treats a value as an error only with that exact signature, D26) and it has
no `Format` method (which fmt would call instead, and which `errOk` says nothing about, D25); so
`fmt`'s `%v` calls its `Error()`. What `leadershipTransfer` needs of the transport's TimeoutNow error to format it
(`fmt.Errorf.spec_tnErr`). True of inproc's errors (`errors.New` values, `*errors.errorString`,
whose method set is `{Error}`). -/
def errNoFmt (err : GoInterface) : Prop :=
  ∃ x : GoInterfaceOk, err = GoInterface.ok x ∧ methodSet x.ty !! go!"Format" = none ∧
    methodSet x.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])

theorem errOk_ne_nil (err : GoInterface) : errOk (GF := GF) err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold errOk
  iintro ⟨%x, %h, -⟩
  ipureintro
  subst h
  simp

/-! ## The RPC channel of server `j` -/

/-- A response sent on an RPC's response channel: an error, or a response struct of the request's
type (owned by the receiver) satisfying `P` (the error: `errOk`). -/
def rpcRespP (ty : go.GoType) (P : Loc → IProp GF) (r : RPCResponse) : IProp GF :=
  iprop(errOk r.Error' ∨
    ∃ p : Loc, ⌜r.Error' = interface.nil ∧ r.Response' = interface.mkOk (go.GoType.PointerType ty) #p⌝ ∗
      P p)

/-- (stage 2, D25) A response sent on an RPC's response channel that is never an error: a response
struct of the request's type satisfying `P`. The TimeoutNow response (raft's `timeoutNow` responds
`rpc.Respond(&TimeoutNowResponse{}, nil)`; `processRPC` reaches it only after the header check
passed, which it does for a request with `tnReq`). -/
def rpcRespOkP (ty : go.GoType) (P : Loc → IProp GF) (r : RPCResponse) : IProp GF :=
  iprop(∃ p : Loc, ⌜r.Error' = interface.nil ∧ r.Response' = interface.mkOk (go.GoType.PointerType ty) #p⌝ ∗
      P p)

/-- (stage 3) A response on an InstallSnapshot RPC's response channel: any non-nil error (the
receiver passes on `io.Copy`'s, `sink.Close`'s or the restore's error unformatted; the sender only
tests it against nil), or a response struct satisfying `P`. -/
def rpcRespAnyP (ty : go.GoType) (P : Loc → IProp GF) (r : RPCResponse) : IProp GF :=
  iprop(⌜r.Error' ≠ interface.nil⌝ ∨
    ∃ p : Loc, ⌜r.Error' = interface.nil ∧ r.Response' = interface.mkOk (go.GoType.PointerType ty) #p⌝ ∗
      P p)

/-- An AppendEntries `RPC` delivered to server `j` (its main loop or, for a heartbeat, its heartbeat
handler): the request (a fresh copy, owned), valid, and a response channel for one response of
responder `j`. -/
def aeRpcP (γ : GNames) (j : SID) (v : RPC) : IProp GF :=
  iprop(∃ (p : Loc) (rq : AppendEntriesRequest) (snd : SID) (T prev pt : Nat) (ents : RLog) (lci : Nat)
        (ss : Snap) (γc : ChanNames),
        ⌜v.Command' = interface.mkOk (go.GoType.PointerType AppendEntriesRequest.ty) #p⌝ ∗
        p ↦ rq ∗ aeReq γ rq snd T prev pt ents lci ss ∗
        isChanBag (V := RPCResponse) γc v.RespChan'
          (rpcRespP AppendEntriesResponse.ty
            (fun q => iprop(∃ rp : AppendEntriesResponse, q ↦ rp ∗
              aeResp γ rp j T (prev + ents.length) (isHb prev ents lci) ss))))

/-- (stage 3) An InstallSnapshot `RPC` delivered to server `j`: the request (a fresh copy, owned),
valid (`isReq`), its snapshot stream as the RPC's `Reader` (`snapStream`), and a response channel for
one response. -/
def isRpcP (γ : GNames) (snapP : Nat → List w8 → IProp GF) (j : SID) (v : RPC) : IProp GF :=
  iprop(∃ (p : Loc) (rq : InstallSnapshotRequest) (snd : SID) (T s st : Nat) (b : List w8)
        (rd : GoInterfaceOk) (γc : ChanNames),
        ⌜v.Command' = interface.mkOk (go.GoType.PointerType InstallSnapshotRequest.ty) #p ∧
          v.Reader' = GoInterface.ok rd⌝ ∗
        p ↦ rq ∗ isReq γ rq snd j T s st b ∗ snapStream rd snapP s b ∗
        isChanBag (V := RPCResponse) γc v.RespChan'
          (rpcRespAnyP InstallSnapshotResponse.ty
            (fun q => iprop(∃ rp : InstallSnapshotResponse, q ↦ rp ∗ isResp γ rp))))

/-- An `RPC` delivered to server `j`: a request (a fresh copy, owned) of one of the five kinds
the program sends (stage 2: TimeoutNow too; stage 3: InstallSnapshot, with its snapshot stream as
the RPC's `Reader`, every other kind with a nil `Reader`), valid, and a response channel for one
response of responder `j`. (Stage 3: `snapP`, the FSMs' snapshot meaning, is a parameter.) -/
def rpcP (γ : GNames) (snapP : Nat → List w8 → IProp GF) (j : SID) (v : RPC) : IProp GF :=
  iprop((⌜v.Reader' = interface.nil⌝ ∗
    (aeRpcP γ j v ∨
     (∃ (p : Loc) (rq : RequestVoteRequest) (c : SID) (T li lt : Nat) (γc : ChanNames),
        ⌜v.Command' = interface.mkOk (go.GoType.PointerType RequestVoteRequest.ty) #p⌝ ∗
        p ↦ rq ∗ rvReq γ rq c T li lt ∗
        isChanBag (V := RPCResponse) γc v.RespChan'
          (rpcRespP RequestVoteResponse.ty (fun q => iprop(∃ rp : RequestVoteResponse, q ↦ rp ∗ rvResp γ rp j c T)))) ∨
     (∃ (p : Loc) (rq : RequestPreVoteRequest) (c : SID) (T : Nat) (γc : ChanNames),
        ⌜v.Command' = interface.mkOk (go.GoType.PointerType RequestPreVoteRequest.ty) #p⌝ ∗
        p ↦ rq ∗ pvReq rq c T ∗
        isChanBag (V := RPCResponse) γc v.RespChan'
          (rpcRespP RequestPreVoteResponse.ty (fun q => iprop(∃ rp : RequestPreVoteResponse, q ↦ rp ∗ pvResp γ rp T)))) ∨
     (∃ (p : Loc) (rq : TimeoutNowRequest) (c : SID) (γc : ChanNames),
        ⌜v.Command' = interface.mkOk (go.GoType.PointerType TimeoutNowRequest.ty) #p⌝ ∗
        p ↦ rq ∗ tnReq rq c ∗
        isChanBag (V := RPCResponse) γc v.RespChan'
          (rpcRespOkP TimeoutNowResponse.ty
            (fun q => iprop(∃ rp : TimeoutNowResponse, q ↦ rp ∗
              ∃ id ad : List w8, rp.RPCHeader'.ID' ↦*□ id ∗ rp.RPCHeader'.Addr' ↦*□ ad)))))) ∨
    isRpcP γ snapP j v)

/-- Server `j`'s RPC channel. -/
def isRpcChan (γ : GNames) (snapP : Nat → List w8 → IProp GF) (j : SID) (ch : Loc) : IProp GF :=
  iprop(∃ γc, isChanBag (V := RPC) γc ch (rpcP γ snapP j))

instance isRpcChan_persistent γ snapP j ch : Persistent (isRpcChan (GF := GF) γ snapP j ch) := by
  unfold isRpcChan; infer_instance

/-! ## The heartbeat handler (stage 2) -/

/-- An `RPC` the transport hands to server `j`'s heartbeat handler: a heartbeat (`isHb`) of
`aeRpcP`. -/
def hbRpcP (γ : GNames) (j : SID) (v : RPC) : IProp GF :=
  iprop(⌜v.Reader' = interface.nil⌝ ∗
    ∃ (p : Loc) (rq : AppendEntriesRequest) (snd : SID) (T pt : Nat) (lci : Nat) (ss : Snap)
        (γc : ChanNames),
        ⌜v.Command' = interface.mkOk (go.GoType.PointerType AppendEntriesRequest.ty) #p⌝ ∗
        p ↦ rq ∗ aeReq γ rq snd T 0 pt [] lci ss ∗ ⌜lci = 0⌝ ∗
        isChanBag (V := RPCResponse) γc v.RespChan'
          (rpcRespP AppendEntriesResponse.ty
            (fun q => iprop(∃ rp : AppendEntriesResponse, q ↦ rp ∗
              aeResp γ rp j T 0 (isHb 0 [] lci) ss))))

/-- **The heartbeat handler contract** (persistent) of `cb`, server `j`'s handler
(`Raft.processHeartbeat`, registered by `NewRaft` with `SetHeartbeatHandler`): called on any
goroutine (the transport's, concurrently with `j`'s main loop) with a heartbeat `RPC` for `j`, it
sends at most one response on the RPC's response channel and returns. processHeartbeat changes no
protocol state (fix `ae71703`): it answers a heartbeat of `j`'s current term while `j` follows
(success, the witness from its term read), a stale one with `j`'s term, and refuses any other
with an error. It takes the calling thread's quarter token `rtok tid` and gives it back
(processHeartbeat's `setLeader` notifies the observers under `observersLock.RLock`). -/
def hbHandler (γ : GNames) (j : SID) (cb : GoFunc) : IProp GF :=
  iprop(□ ∀ (v : RPC) (tid : Nat) (Φ : val → IProp GF), hbRpcP γ j v -∗ rtok tid -∗
    (rtok tid -∗ Φ #()) -∗
    WP (App (Val #cb) (Val #v)) {{ Φ }})

instance hbHandler_persistent γ j cb : Persistent (hbHandler (GF := GF) γ j cb) := by
  unfold hbHandler; infer_instance

/-- (stage 2, law E) **Introducing `hbHandler`** from the callback's triple (the `Φ`-form of
`{{ hbRpcP γ j v ∗ rtok tid }} cb v {{ RET #(); rtok tid }}`, as a spec file states it). -/
theorem hbHandler_intro (γ : GNames) (j : SID) (cb : GoFunc) :
    (□ ∀ (v : RPC) (tid : Nat) (Φ : val → IProp GF), hbRpcP γ j v -∗ rtok tid -∗
      ▷ (rtok tid -∗ Φ #()) -∗ WP (App (Val #cb) (Val #v)) {{ Φ }}) ⊢ hbHandler (GF := GF) γ j cb := by
  unfold hbHandler
  iintro #H
  imodintro
  iintro %v %tid %Φ Hv Ht HΦ
  iapply H $$ %v %tid %Φ Hv Ht
  inext
  iexact HΦ

/-! ## Pipelines (stage 2) -/

/-- (stage 2) A pipelined request's outcome as the pipeline's consumer sees it (`Response()`):
the response struct the sender lent (zero, `Success = false`, if the call failed: pipelineDecode
reads it without calling `Error()`), success meaning `j` acknowledged `llog T [1..k]` in `T` (or
the request was a heartbeat). -/
def pipeResp (γ : GNames) (rp : AppendEntriesResponse) (j : SID) (T k : Nat) (hb : Prop) :
    IProp GF :=
  iprop(⌜rp.Success' = false⌝ ∨ ⌜hb⌝ ∨ ackIs γ j T k)

/-- (stage 2) **A future** `fi` on a pipeline of term `T` to `j`'s consumer channel (an
`AppendFuture`): `Request()` returns the request (read-only, valid, of term `T`), `Response()` the
response struct (owned by the receiver, `pipeResp`), `Start()` some time. -/
def pipeFut (γ : GNames) (j : SID) (T : Nat) (fi : GoInterface) : IProp GF :=
  iprop(∃ (fI : GoInterfaceOk) (args resp : Loc) (rq : AppendEntriesRequest) (snd : SID)
      (prev pt : Nat) (ents : RLog) (lci : Nat) (ss : Snap) (rp : AppendEntriesResponse),
    ⌜fi = GoInterface.ok fI⌝ ∗ args ↦□ rq ∗ aeReq γ rq snd T prev pt ents lci ss ∗
    resp ↦ rp ∗ pipeResp γ rp j T (prev + ents.length) (isHb prev ents lci) ∗
    □ (∀ Φ : val → IProp GF, Φ #args -∗
        WP (App (Val #(methods fI.ty go!"Request" fI.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, Φ #resp -∗
        WP (App (Val #(methods fI.ty go!"Response" fI.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, (∀ t : time.Time, Φ #t) -∗
        WP (App (Val #(methods fI.ty go!"Start" fI.v)) (Val #())) {{ Φ }}))

/-- (stage 2) **The pipeline contract** of `x` (an `AppendPipeline` to voter `j` used by the
replication goroutine of term `T`, persistent; the term is a ghost parameter fixed when the
pipeline is made, so that the decoder learns acknowledgements of `T`, which the commitment of `T`
holds): `AppendEntries(args, resp)` takes a valid request of term `T` (read-only from now on) and a response struct
with `Success = false` (lent until its future arrives; raft's is `new(AppendEntriesResponse)`: a
failed call leaves it as it was) and returns a future (ignored by raft) or an error
(`ErrPipelineClosed`); each request sent comes back as one future on the consumer channel
(`Consumer()`, a bag of `pipeFut`); `Close()` (idempotent) returns nil. raft needs no order of
the futures (each response's facts are about its own request). -/
def isPipeline (x : GoInterfaceOk) (γ : GNames) (j : SID) (T : Nat) : IProp GF :=
  iprop(
    □ (∀ (args resp : Loc) (rq : AppendEntriesRequest) (rp0 : AppendEntriesResponse) (snd : SID)
          (prev pt : Nat) (ents : RLog) (lci : Nat) (ss : Snap) (Φ : val → IProp GF),
        args ↦□ rq -∗ aeReq γ rq snd T prev pt ents lci ss -∗ resp ↦ rp0 -∗ ⌜rp0.Success' = false⌝ -∗
        (∀ (fi err : GoInterface), (⌜err = interface.nil⌝ ∨ errOk err) -∗ Φ (PairV #fi #err)) -∗
        WP (App (App (Val #(methods x.ty go!"AppendEntries" x.v)) (Val #args)) (Val #resp))
          {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        (∀ ch : Loc, (∃ γc : ChanNames, isChanBag (V := GoInterface) γc ch (pipeFut γ j T)) -∗ Φ #ch) -∗
        WP (App (Val #(methods x.ty go!"Consumer" x.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, Φ #interface.nil -∗
        WP (App (Val #(methods x.ty go!"Close" x.v)) (Val #())) {{ Φ }}))

instance isPipeline_persistent x γ j T : Persistent (isPipeline (GF := GF) x γ j T) := by
  unfold isPipeline; infer_instance

/-! ## The transport -/

/-- **The transport contract** of `x`, server `i`'s transport in protocol `γ`: its consumer is
`rpcCh`; a call to a voter `j` delivers a valid request to `j` (on `j`'s RPC channel or, for a
heartbeat, to `j`'s registered heartbeat handler) and returns `j`'s response (with `j`'s facts) or
an error with an `Error()` method (`errOk`). (Stage 2) `SetHeartbeatHandler(cb)` takes the
handler's contract (`hbHandler`); `AppendEntriesPipeline` returns a pipeline (`isPipeline`) or an
error; `TimeoutNow` is a call as the others (no protocol facts; its error, D25, has no `Format` method, `errNoFmt`: the caller formats it with `%v`). Every call lends the calling
thread's quarter token `rtok tid` (inproc's `call` may run the callee's heartbeat handler on it;
raft's callers hold one: the replication, heartbeat, election and transfer goroutines). (Stage 3)
`InstallSnapshot(id, j, args, resp, data)` delivers a valid install request with the snapshot stream
`data` (`snapStream`; `snapP` is the FSMs' snapshot meaning, a parameter) and returns the response or
some non-nil error. -/
def isTransport (x : GoInterfaceOk) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID)
    (rpcCh : Loc) : IProp GF :=
  iprop(
    isRpcChan γ snapP i rpcCh ∗
    □ (∀ Φ : val → IProp GF, Φ #rpcCh -∗
        WP (App (Val #(methods x.ty go!"Consumer" x.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, Φ #(i : GoString) -∗
        WP (App (Val #(methods x.ty go!"LocalAddr" x.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (id addr : GoString) (Φ : val → IProp GF), (∀ s : GoSlice, s ↦* (addr : List w8) -∗ Φ #s) -∗
        WP (App (App (Val #(methods x.ty go!"EncodePeer" x.v)) (Val #id)) (Val #addr)) {{ Φ }}) ∗
    □ (∀ (buf : GoSlice) (dq : DFrac) (b : List w8) (Φ : val → IProp GF),
        buf ↦*{dq} b -∗ (buf ↦*{dq} b -∗ Φ #(b : GoString)) -∗
        WP (App (Val #(methods x.ty go!"DecodePeer" x.v)) (Val #buf)) {{ Φ }}) ∗
    □ (∀ (cb : GoFunc) (Φ : val → IProp GF), hbHandler γ i cb -∗ Φ #() -∗
        WP (App (Val #(methods x.ty go!"SetHeartbeatHandler" x.v)) (Val #cb)) {{ Φ }}) ∗
    □ (∀ (id : GoString) (j : SID) (T : Nat) (Φ : val → IProp GF),
        isSrv γ j -∗
        (∀ (p : GoInterface) (err : GoInterface),
          ((⌜err = interface.nil⌝ ∗ ∃ pI : GoInterfaceOk, ⌜p = GoInterface.ok pI⌝ ∗ isPipeline pI γ j T) ∨
           (errOk err ∗ ∃ c, isRaftErr c err)) -∗
          Φ (PairV #p #err)) -∗
        WP (App (App (Val #(methods x.ty go!"AppendEntriesPipeline" x.v)) (Val #id))
          (Val #(j : GoString))) {{ Φ }}) ∗
    □ (∀ (id : GoString) (j : SID) (args resp : Loc) (rq : AppendEntriesRequest)
          (rp0 : AppendEntriesResponse) (dq : DFrac) (snd : SID) (T prev pt : Nat) (ents : RLog) (lci : Nat)
          (ss : Snap) (tid : Nat) (Φ : val → IProp GF),
        isSrv γ j -∗ args ↦{dq} rq -∗ aeReq γ rq snd T prev pt ents lci ss -∗ resp ↦ rp0 -∗
        rtok tid -∗
        (∀ err : GoInterface, args ↦{dq} rq -∗ rtok tid -∗
          ((⌜err = interface.nil⌝ ∗ ∃ rp : AppendEntriesResponse, resp ↦ rp ∗
              aeResp γ rp j T (prev + ents.length) (isHb prev ents lci) ss) ∨
           (errOk err ∗ ∃ rp : AppendEntriesResponse, resp ↦ rp)) -∗ Φ #err) -∗
        WP (App (App (App (App (Val #(methods x.ty go!"AppendEntries" x.v)) (Val #id))
          (Val #(j : GoString))) (Val #args)) (Val #resp)) {{ Φ }}) ∗
    □ (∀ (id : GoString) (j : SID) (args resp : Loc) (rq : RequestVoteRequest)
          (rp0 : RequestVoteResponse) (dq : DFrac) (c : SID) (T li lt : Nat) (tid : Nat)
          (Φ : val → IProp GF),
        isSrv γ j -∗ args ↦{dq} rq -∗ rvReq γ rq c T li lt -∗ resp ↦ rp0 -∗ rtok tid -∗
        (∀ err : GoInterface, args ↦{dq} rq -∗ rtok tid -∗
          ((⌜err = interface.nil⌝ ∗ ∃ rp : RequestVoteResponse, resp ↦ rp ∗ rvResp γ rp j c T) ∨
           (errOk err ∗ ∃ rp : RequestVoteResponse, resp ↦ rp)) -∗ Φ #err) -∗
        WP (App (App (App (App (Val #(methods x.ty go!"RequestVote" x.v)) (Val #id))
          (Val #(j : GoString))) (Val #args)) (Val #resp)) {{ Φ }}) ∗
    □ (∀ (id : GoString) (j : SID) (args resp : Loc) (rq : RequestPreVoteRequest)
          (rp0 : RequestPreVoteResponse) (dq : DFrac) (c : SID) (T : Nat) (tid : Nat)
          (Φ : val → IProp GF),
        isSrv γ j -∗ args ↦{dq} rq -∗ pvReq rq c T -∗ resp ↦ rp0 -∗ rtok tid -∗
        (∀ err : GoInterface, args ↦{dq} rq -∗ rtok tid -∗
          ((⌜err = interface.nil⌝ ∗ ∃ rp : RequestPreVoteResponse, resp ↦ rp ∗ pvResp γ rp T) ∨
           (errOk err ∗ ∃ rp : RequestPreVoteResponse, resp ↦ rp)) -∗ Φ #err) -∗
        WP (App (App (App (App (Val #(methods x.ty go!"RequestPreVote" x.v)) (Val #id))
          (Val #(j : GoString))) (Val #args)) (Val #resp)) {{ Φ }}) ∗
    □ (∀ (id : GoString) (j : SID) (args resp : Loc) (rq : InstallSnapshotRequest)
          (rp0 : InstallSnapshotResponse) (dq : DFrac) (snd : SID) (T s st : Nat) (b : List w8)
          (data : GoInterfaceOk) (tid : Nat) (Φ : val → IProp GF),
        isSrv γ j -∗ args ↦{dq} rq -∗ isReq γ rq snd j T s st b -∗ resp ↦ rp0 -∗
        snapStream data snapP s b -∗ rtok tid -∗
        (∀ err : GoInterface, args ↦{dq} rq -∗ rtok tid -∗
          ((⌜err = interface.nil⌝ ∗ ∃ rp : InstallSnapshotResponse, resp ↦ rp ∗ isResp γ rp) ∨
           (⌜err ≠ interface.nil⌝ ∗ ∃ rp : InstallSnapshotResponse, resp ↦ rp)) -∗ Φ #err) -∗
        WP (App (App (App (App (App (Val #(methods x.ty go!"InstallSnapshot" x.v)) (Val #id))
          (Val #(j : GoString))) (Val #args)) (Val #resp)) (Val #(GoInterface.ok data))) {{ Φ }}) ∗
    □ (∀ (id : GoString) (j : SID) (args resp : Loc) (rq : TimeoutNowRequest)
          (rp0 : TimeoutNowResponse) (dq : DFrac) (c : SID) (tid : Nat) (Φ : val → IProp GF),
        isSrv γ j -∗ args ↦{dq} rq -∗ tnReq rq c -∗ resp ↦ rp0 -∗ rtok tid -∗
        (∀ err : GoInterface, args ↦{dq} rq -∗ rtok tid -∗
          ((⌜err = interface.nil⌝ ∗ ∃ rp : TimeoutNowResponse, resp ↦ rp) ∨
           (errOk err ∗ ⌜errNoFmt (GF := GF) err⌝ ∗ ∃ rp : TimeoutNowResponse, resp ↦ rp)) -∗ Φ #err) -∗
        WP (App (App (App (App (Val #(methods x.ty go!"TimeoutNow" x.v)) (Val #id))
          (Val #(j : GoString))) (Val #args)) (Val #resp)) {{ Φ }}))

instance isTransport_persistent x γ snapP i ch :
    Persistent (isTransport (GF := GF) x γ snapP i ch) := by
  unfold isTransport; infer_instance

end contracts

end github_com.hashicorp.raft

end Perennial
