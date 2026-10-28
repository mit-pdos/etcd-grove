/-
**The streams' protocol** (rafthttp stage 5a, D38d; `notes/rafthttp-plan.md`). Lean-first.

A stream is pulled: the reader B sends `GET /raft/stream/{msgapp|message}/<B>` to the writer A,
whose handler hands the response writer to A's stream writer, which writes the frames of many
messages into the one response. A message's one-shot part cannot cross the wire, and the
pipeline's deposit per ticket (`Pipe.lean`) does not do for many messages, so:

* **Tokens.** B owns the authority of a ghost map `γw` from frame indices; it withdraws the `i`-th
  frame's deposit (`streamDeposit`: `inv (O st ∨ i ↪[γw] ())`) with the token `i ↪[γw] ()`, which
  it inserts once (B reads the frames in order: `streamRd`).
* **The registry.** A must deposit for B's `γw`, and B must know that A's deposits are: the
  request's ticket names the connection (`streamReg`: `γk ↪□ (γw, type, B)` in `Rh.γreg`, its
  authority in an invariant). B registers when it allocates the ticket, fresh for the registry's
  finite domain (`stream_ticket_alloc`), so an entry has one value and both sides agree on it.
* **Chains.** What A writes is a prefix of a chain of frames of the stream's codec
  (`StreamCodec`: msgappv2's `V2Frame A B`, or the message codec's `msgFrame`) from the codec's
  initial state, each frame a link heartbeat or a message to B with `□ P` and its deposit
  (`frameDep`, `streamSent`). Frames are self-delimiting (`StreamCodec.uniq`), so two chains whose
  bytes extend one another are prefixes of one another (`Chain.agree`): the reader's `i`-th
  decoded frame is the writer's `i`-th (`streamSent_frame`), and what it reads next is compatible
  with a frame (`streamSent_compat`, the msgappv2 decoder's premise).

`streamResp` is a `200` response's protocol for a stream request; `raftProto` (`Pipe.lean`) takes
it for every `GET` (rafthttp's other `GET`, the prober's, is not translated).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Pipe
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Codecs and chains (pure) -/

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- **A stream's codec** (pure): its state, initial state, and frames (`F s w bs s'`: from `s`, the
bytes `bs` carry the wire content `w` and lead to `s'`), self-delimiting and non-empty. -/
structure StreamCodec where
  S : Type
  init : S
  F : S → MsgWire → List w8 → S → Prop
  uniq : ∀ {s : S} {w1 w2 : MsgWire} {b1 b2 x y : List w8} {s1 s2 : S},
    F s w1 b1 s1 → F s w2 b2 s2 → b1 ++ x = b2 ++ y → w1 = w2 ∧ b1 = b2 ∧ s1 = s2 ∧ x = y
  nonempty : ∀ {s : S} {w : MsgWire} {b : List w8} {s' : S}, F s w b s' → b ≠ []

/-- The message codec's frame (`messageEncoder`'s): an encoding of a message of the content,
below `2^63` bytes, after its length. -/
def MsgFrameOf (w : MsgWire) (bs : List w8) : Prop :=
  ∃ (st : MsgSt) (mbs : List w8), wireOf st = w ∧ MsgWireOk st mbs ∧ mbs.length < 2 ^ 63 ∧
    bs = msgFrame mbs

theorem MsgFrameOf.uniq {w1 w2 : MsgWire} {b1 b2 x y : List w8} (h1 : MsgFrameOf w1 b1)
    (h2 : MsgFrameOf w2 b2) (h : b1 ++ x = b2 ++ y) : w1 = w2 ∧ b1 = b2 ∧ x = y := by
  obtain ⟨s1, m1, rfl, hm1, hl1, rfl⟩ := h1
  obtain ⟨s2, m2, rfl, hm2, hl2, rfl⟩ := h2
  obtain ⟨rfl, rfl⟩ := chunk_eq hl1 hl2 (by simpa only [msgFrame, List.append_assoc] using h)
  exact ⟨Option.some.inj (hm1.2.symm.trans hm2.2), rfl, rfl⟩

/-- The message encoder's frame, and the decoder's, is the message codec's. -/
theorem MsgFrameOf.of_wire {st : MsgSt} {bs : List w8} (h : MsgWireOk st bs)
    (hl : bs.length < 2 ^ 63) : MsgFrameOf (wireOf st) (msgFrame bs) :=
  ⟨st, bs, rfl, h, hl, rfl⟩

/-- **The message stream's codec** (`messageEncoder`/`messageDecoder`): no state. -/
def msgCodec : StreamCodec where
  S := Unit
  init := ()
  F _ w bs _ := MsgFrameOf w bs
  uniq h1 h2 h := by
    obtain ⟨hw, hb, hx⟩ := MsgFrameOf.uniq h1 h2 h
    exact ⟨hw, hb, rfl, hx⟩
  nonempty h := by
    obtain ⟨_, _, _, _, _, rfl⟩ := h
    intro he
    have hl := congrArg List.length he
    simp [msgFrame, u64Be_length] at hl

/-- **The msgappv2 stream's codec** on the connection from `frm` to `to`: from the zero state
(`newMsgAppV2Encoder`'s and `newMsgAppV2Decoder`'s). -/
def v2Codec (frm to : w64) : StreamCodec where
  S := V2St
  init := ⟨W64 0, W64 0⟩
  F := V2Frame frm to
  uniq h1 h2 h := V2Frame.unique h1 h2 h
  nonempty h := by
    rcases h with ⟨-, rfl, -⟩ | ⟨_, -, -, -, rfl, -⟩ | ⟨_, _, -, -, -, rfl, -⟩ <;> simp

/-- **A chain of frames** from `s` to `s'`: each frame from the state the previous one leads to. -/
inductive Chain (C : StreamCodec) : C.S → List (MsgWire × List w8) → C.S → Prop
  | nil (s : C.S) : Chain C s [] s
  | cons {s : C.S} {w : MsgWire} {b : List w8} {s' : C.S} {fs : List (MsgWire × List w8)}
      {s'' : C.S} : C.F s w b s' → Chain C s' fs s'' → Chain C s ((w, b) :: fs) s''

/-- A chain's bytes. -/
def chainBytes (fs : List (MsgWire × List w8)) : List w8 := (fs.map Prod.snd).flatten

@[simp] theorem chainBytes_nil : chainBytes [] = [] := rfl

@[simp] theorem chainBytes_cons (f : MsgWire × List w8) (fs : List (MsgWire × List w8)) :
    chainBytes (f :: fs) = f.2 ++ chainBytes fs := rfl

theorem chainBytes_append (fs gs : List (MsgWire × List w8)) :
    chainBytes (fs ++ gs) = chainBytes fs ++ chainBytes gs := by
  simp [chainBytes]

theorem Chain.append {C : StreamCodec} {s s' s'' : C.S} {fs gs : List (MsgWire × List w8)}
    (h1 : Chain C s fs s') (h2 : Chain C s' gs s'') : Chain C s (fs ++ gs) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hf _ ih => exact Chain.cons hf (ih h2)

/-- A frame added at a chain's end. -/
theorem Chain.snoc {C : StreamCodec} {s s' s'' : C.S} {fs : List (MsgWire × List w8)}
    {w : MsgWire} {b : List w8} (h : Chain C s fs s') (hf : C.F s' w b s'') :
    Chain C s (fs ++ [(w, b)]) s'' :=
  h.append (Chain.cons hf (Chain.nil _))

/-- **Two chains from one state whose bytes extend one another are prefixes of one another.** -/
theorem Chain.agree {C : StreamCodec} {s s1 s2 : C.S} {f1 f2 : List (MsgWire × List w8)}
    {x y : List w8} (h1 : Chain C s f1 s1) (h2 : Chain C s f2 s2)
    (h : chainBytes f1 ++ x = chainBytes f2 ++ y) :
    (∃ g, f2 = f1 ++ g ∧ Chain C s1 g s2 ∧ x = chainBytes g ++ y) ∨
    (∃ g, f1 = f2 ++ g ∧ Chain C s2 g s1 ∧ y = chainBytes g ++ x) := by
  induction h1 generalizing f2 x y with
  | nil s =>
    left
    exact ⟨f2, rfl, h2, by simpa using h⟩
  | @cons s w b s' fs s'' hf hfs ih =>
    cases h2 with
    | nil =>
      right
      exact ⟨(w, b) :: fs, rfl, Chain.cons hf hfs, by simpa using h.symm⟩
    | @cons _ w2 b2 s'2 fs2 _ hf2 hfs2 =>
      simp only [chainBytes_cons, List.append_assoc] at h
      obtain ⟨rfl, rfl, rfl, hr⟩ := C.uniq hf hf2 h
      rcases ih hfs2 hr with ⟨g, rfl, hg, hx⟩ | ⟨g, rfl, hg, hy⟩
      · exact Or.inl ⟨g, rfl, hg, hx⟩
      · exact Or.inr ⟨g, rfl, hg, hy⟩

/-- The states a chain leads to from one state over the same frames agree. -/
theorem Chain.det {C : StreamCodec} {s s1 s2 : C.S} {fs : List (MsgWire × List w8)}
    (h1 : Chain C s fs s1) (h2 : Chain C s fs s2) : s1 = s2 := by
  induction h1 with
  | nil => cases h2; rfl
  | cons hf _ ih =>
    cases h2 with
    | cons hf2 hfs2 =>
      obtain ⟨-, -, rfl, -⟩ := C.uniq hf hf2 (x := []) (y := []) rfl
      exact ih hfs2

/-- A chain's bytes are empty only for the empty chain. -/
theorem Chain.bytes_nil {C : StreamCodec} {s s' : C.S} {g : List (MsgWire × List w8)}
    (h : Chain C s g s') (hb : chainBytes g = []) : g = [] := by
  cases h with
  | nil => rfl
  | cons hf _ =>
    simp only [chainBytes_cons, List.append_eq_nil_iff] at hb
    exact absurd hb.1 (C.nonempty hf)

/-- **The reader's next frame** (pure): a reader having decoded the chain `fr` (to `s`), knowing
that what it has read and some `ys` more are a prefix of the bytes of some chain `fr'` from the
same state, knows `ys` is empty or compatible with a frame from `s`. -/
theorem Chain.compat {C : StreamCodec} {s0 s s' : C.S} {fr fr' : List (MsgWire × List w8)}
    {ys z : List w8} (h : Chain C s0 fr s) (h' : Chain C s0 fr' s')
    (hp : chainBytes fr ++ ys ++ z = chainBytes fr') :
    ys = [] ∨ ∃ (w : MsgWire) (bs : List w8) (s1 : C.S) (z1 z2 : List w8),
      C.F s w bs s1 ∧ ys ++ z1 = bs ++ z2 := by
  rcases h.agree h' (x := ys ++ z) (y := []) (by simpa [List.append_assoc] using hp) with
    ⟨g, rfl, hg, hx⟩ | ⟨g, rfl, hg, hy⟩
  · cases hg with
    | nil =>
      left
      simp at hx
      exact hx.1
    | @cons _ w b s1 _ _ hf _ =>
      right
      exact ⟨w, b, s1, z, chainBytes _, hf, by simpa using hx⟩
  · left
    have hl := congrArg List.length hy
    simp at hl
    have : ys.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this

/-- **The reader's decoded frame is the chain's** (pure): a reader having decoded the chain `fr`
(to `s`) and then a frame `(w, bs)` from `s`, knowing that the bytes so far are a prefix of the
bytes of some chain `fr'` from the same state, finds that frame at `fr'`'s index `fr.length`. -/
theorem Chain.frame {C : StreamCodec} {s0 s s1 s' : C.S} {fr fr' : List (MsgWire × List w8)}
    {w : MsgWire} {bs z : List w8} (h : Chain C s0 fr s) (hf : C.F s w bs s1)
    (h' : Chain C s0 fr' s') (hp : chainBytes fr ++ bs ++ z = chainBytes fr') :
    fr'[fr.length]? = some (w, bs) := by
  have hc := h.snoc hf
  rcases hc.agree h' (x := z) (y := []) (by simpa [chainBytes_append] using hp) with
    ⟨g, rfl, -, -⟩ | ⟨g, hg, hgc, hy⟩
  · simp
  · -- `fr'` is no longer: then `g`'s bytes are empty, so `g` is
    have hl := congrArg List.length hy
    simp at hl
    have hgb : chainBytes g = [] := List.length_eq_zero_iff.mp (by omega)
    have := hgc.bytes_nil hgb
    subst this
    simp only [List.append_nil] at hg
    rw [← hg]
    simp

end pure

/-! ## The registry, the deposits, the protocol -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def streamN : Namespace := nroot.@"rafthttp_stream"

/-- A stream type's endpoint (`streamType.endpoint`: `path.Join(RaftStreamPrefix, ...)`). -/
def StreamTy.endpoint : StreamTy → GoString
  | .msgAppV2 => go!"/raft/stream/msgapp"
  | .message => go!"/raft/stream/message"

/-- The codec of a stream of type `t` from `frm` to `to`. -/
def StreamTy.codec : StreamTy → w64 → w64 → StreamCodec
  | .msgAppV2, frm, to => v2Codec frm to
  | .message, _, _ => msgCodec

/-- The path of the stream of type `t` read by `rid` (`streamReader.dial`'s
`path.Join(t.endpoint(), rid.String())`, `streamPath_join`). -/
def streamPath (t : StreamTy) (rid : w64) : GoString := t.endpoint ++ go!"/" ++ types.idStr rid

/-- The prober's path (`ProbingPrefix`'s value, `"/raft/probing"`; rafthttp stage 6c). -/
def probingPath : GoString := go!"/raft/probing"

/-- A stream endpoint's segments. -/
def StreamTy.segs : StreamTy → List (List w8)
  | .msgAppV2 => [go!"raft", go!"stream", go!"msgapp"]
  | .message => [go!"raft", go!"stream", go!"message"]

theorem StreamTy.segs_plain (t : StreamTy) : ∀ s ∈ t.segs, path.plainSeg s := by
  cases t <;> decide

theorem StreamTy.endpoint_segs (t : StreamTy) : t.endpoint = path.segsPath t.segs := by
  cases t <;> decide

/-- `RaftStreamPrefix = path.Join(RaftPrefix, "stream")` (`http.go`). -/
theorem raftStreamPrefix_join : path.joinModel [go!"/raft", go!"stream"] = go!"/raft/stream" := by
  decide

/-- `t.endpoint() = path.Join(RaftStreamPrefix, ...)` (`stream.go`). -/
theorem StreamTy.endpoint_join (t : StreamTy) :
    path.joinModel [go!"/raft/stream", (t.segs.getLast? ).getD []] = t.endpoint := by
  cases t <;> decide

/-- **The stream's path**: `path.Join(t.endpoint(), rid.String())`, of the segments
`/raft/stream/<type>/<rid>`. -/
theorem streamPath_segs (t : StreamTy) (rid : w64) :
    streamPath t rid = path.segsPath (t.segs ++ [types.idStr rid]) := by
  rw [streamPath, path.segsPath_snoc, StreamTy.endpoint_segs]; rfl

theorem streamPath_join (t : StreamTy) (rid : w64) :
    path.joinModel [t.endpoint, types.idStr rid] = streamPath t rid := by
  rw [StreamTy.endpoint_segs, streamPath_segs]
  exact path.joinModel_segs _ _ (by cases t <;> simp [StreamTy.segs]) t.segs_plain
    (types.idStr_plain rid)

/-- **The stream handler's reading of the path**: its `Base` is the reader's id string. -/
theorem streamPath_base (t : StreamTy) (rid : w64) :
    path.baseModel (streamPath t rid) = types.idStr rid := by
  show path.baseModel (t.endpoint ++ [path.slash] ++ types.idStr rid) = _
  exact path.baseModel_seg _ _ (types.idStr_plain rid)

/-- **The stream handler's reading of the path**: its `Dir` is the endpoint. -/
theorem streamPath_dir (t : StreamTy) (rid : w64) :
    path.dirModel (streamPath t rid) = t.endpoint := by
  show path.dirModel (t.endpoint ++ [path.slash] ++ types.idStr rid) = _
  rw [StreamTy.endpoint_segs]
  exact path.dirModel_segs _ _ (by cases t <;> simp [StreamTy.segs]) t.segs_plain
    (types.idStr_plain rid)

/-- **The registry** (an invariant): its authority. -/
def streamRegInv (Rh : RaftHttp GF) : IProp GF :=
  inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth Rh.γreg 1 m)

instance streamRegInv_persistent (Rh : RaftHttp GF) : Persistent (streamRegInv Rh) := by
  unfold streamRegInv; infer_instance

/-- The network's registry (`netNames_alloc`'s) is `netRh`'s. -/
theorem streamRegInv_netRh (γn : NetNames GF) :
    inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth γn.reg 1 m) ⊢
      streamRegInv (netRh γn) := by
  iintro H
  unfold streamRegInv netRh
  iexact H

/-- **The ticket `γk`'s connection is `c`** (persistent). -/
def streamReg (Rh : RaftHttp GF) (γk : GName) (c : StreamKey) : IProp GF :=
  ghostMapElem Rh.γreg γk DFrac.discard c

instance streamReg_persistent (Rh : RaftHttp GF) (γk : GName) (c : StreamKey) :
    Persistent (streamReg Rh γk c) := by
  unfold streamReg; infer_instance

/-- **The `i`-th frame's deposit** for the reader of tokens `γw` (persistent): the message's
one-shot part, until the reader takes it with its token `i`. -/
def streamDeposit (N : NetPayload GF) (γw : GName) (i : Nat) (st : MsgSt) : IProp GF :=
  inv streamN iprop(N.O st ∨ ghostMapElem γw i (DFrac.own 1) ())

instance streamDeposit_persistent (N : NetPayload GF) (γw : GName) (i : Nat) (st : MsgSt) :
    Persistent (streamDeposit N γw i st) := by
  unfold streamDeposit; infer_instance

/-- **What the `i`-th frame of content `w` carries** (persistent): nothing for a link heartbeat
(the reader drops it), else a message of that content to `rid`, not a snapshot, without
responses, with `□ P` and its deposit. -/
def frameDep (N : NetPayload GF) (γw : GName) (rid : w64) (i : Nat) (w : MsgWire) : IProp GF :=
  iprop(⌜isHB w.msg⌝ ∨ ∃ st : MsgSt, ⌜wireOf st = w ∧ st.msg.To' = rid ∧
    st.msg.Type' ≠ MsgSnap ∧ st.resps = []⌝ ∗ □ N.P st ∗ streamDeposit N γw i st)

instance frameDep_persistent (N : NetPayload GF) (γw : GName) (rid : w64) (i : Nat)
    (w : MsgWire) : Persistent (frameDep N γw rid i w) := by
  unfold frameDep; infer_instance

/-- **The bytes `w` of a stream** of codec `C` to `rid` with the tokens `γw` (persistent): a
prefix of a chain from the initial state, each frame carrying its `frameDep`. -/
def streamSent (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64) (w : List w8) :
    IProp GF :=
  iprop(∃ (fr : List (MsgWire × List w8)) (s : C.S), ⌜Chain C C.init fr s ∧ w <+: chainBytes fr⌝ ∗
    [∗list] i ↦ f ∈ fr, frameDep N γw rid i f.1)

instance streamSent_persistent (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64)
    (w : List w8) : Persistent (streamSent C N γw rid w) := by
  unfold streamSent; infer_instance

/-- **A stream request of ticket `γk`** (persistent): its connection registered, its path the
stream's, (stage 6d) its reader a member other than the one owning the request's host, (D22
J-T, W8) its `X-PeerURLs` header the reader's peer URLs (the stream handler passes them to
`AddRemote` when the reader is no peer). -/
def streamReq (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) : IProp GF :=
  iprop(∃ c : StreamKey, streamReg Rh γk c ∗ ⌜R.path = streamPath c.2.1 c.2.2 ∧
    Rh.member c.2.2 ∧ c.2.2 ≠ Rh.owner R.host ∧ peerURLsHdrOk Rh c.2.2 R.hdr⌝)

instance streamReq_persistent (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    Persistent (streamReq Rh R γk) := by
  unfold streamReq; infer_instance

/-- **A stream response's protocol** (persistent): a `200`'s bytes are those of the stream of the
request's registered connection, from the member owning the request's host to its reader. -/
def streamResp (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64) (w : List w8) :
    IProp GF :=
  iprop(⌜st = W64 200⌝ → ∃ c : StreamKey, streamReg Rh γk c ∗
    streamSent (c.2.1.codec (Rh.owner R.host) c.2.2) Rh.γn.N c.1 c.2.2 w)

instance streamResp_persistent (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64)
    (w : List w8) : Persistent (streamResp Rh R γk st w) := by
  unfold streamResp; infer_instance

/-- **A raft member's response headers** (2026-10-23, rafthttp stage 5e): `X-Server-Version` unset
or a version that parses (the stream reader's `serverVersion` parses it with `semver.MustParse`;
the handlers set it to `version.Version` or not at all). -/
def verHdrOk (hs : List (GoString × GoString)) : Prop :=
  http.hdrGet hs go!"X-Server-Version" = "" ∨ apply.semverValid (http.hdrGet hs go!"X-Server-Version")

theorem verHdrOk_nil : verHdrOk [] := Or.inl rfl

/-- The empty Go string (as a Lean literal, `""`) is the empty byte list. -/
theorem goString_empty : (("" : String) : GoString) = [] := by
  simp [stringToGoString]

/-- Setting another header keeps `X-Server-Version`. -/
theorem verHdrOk_set (hs : List (GoString × GoString)) (k v : GoString)
    (hk : http.canonKey k ≠ http.canonKey go!"X-Server-Version") (h : verHdrOk hs) :
    verHdrOk (http.hdrSet hs k v) := by
  unfold verHdrOk at *
  rw [http.hdrGet_hdrSet_ne _ _ _ _ hk]
  exact h

/-- The snapshot handler's path (`RaftSnapshotPrefix`'s value, `"/raft/snapshot"`; rafthttp stage
6c). -/
def snapPath : GoString := go!"/raft/snapshot"

/-- **A snapshot request** (rafthttp stage 6c; defined 2026-10-24, stage 7b, D42, was opaque): a
`POST` to the snapshot path from another member (`fromOkAt`, as a pipeline request's), with a
streamed body (`snapStreamed`), whose contract is `snapSReq`'s. -/
def snapReq (Rh : RaftHttp GF) (R : http.HReq) (_γk : GName) : IProp GF :=
  iprop(⌜fromOkAt Rh (Rh.owner R.host) R.hdr⌝)

instance snapReq_persistent (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    Persistent (snapReq Rh R γk) := by
  unfold snapReq; infer_instance

/-- **The raft protocol's streamed requests** (D42): the snapshot's `POST`s. -/
def snapStreamed (R : http.HReq) : Prop := R.meth = go!"POST" ∧ R.path = snapPath

/-- **A snapshot request's body** (persistent; D42, stage 7b): every prefix of its stream is
comparable with the frame of an encoding `bs` of a message `st` (`Pre`), and every complete stream
is that frame followed by a bbolt image of some `D` (`Φ`), `st` a `MsgSnap` of a snapshot of index
`i` for the member owning the request's host, without responses; with `□ N.P st`, the deposit of
its one-shot part under the request's ticket (`pipeDeposit`, as a pipeline request's: the handler
withdraws it once) and the image's certificate `□ N.img i D`. The sender's body is
`io.MultiReader` of the envelope's buffer and the merged message's reader (`readerStreams`), whose
stream contract is this one; what the handler decodes of the prefix is `st`, and what
`SaveDBFrom` saves of the rest an image of `D`. -/
def snapSReq (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (Pre Φ : List w8 → Prop) :
    IProp GF :=
  iprop(∃ (st : MsgSt) (bs : List w8) (sn : SnapshotM) (D : backend.Data),
    ⌜MsgWireOk st bs ∧ bs.length < 2 ^ 63 ∧ st.msg.To' = Rh.owner R.host ∧
      st.msg.Type' = MsgSnap ∧ st.snap = some sn ∧ st.resps = [] ∧
      (∀ x, Pre x → x <+: msgFrame bs ∨ msgFrame bs <+: x) ∧
      (∀ x, Φ x → ∃ t, x = msgFrame bs ++ t ∧ backend.boltImage t D)⌝ ∗
    □ Rh.γn.N.P st ∗ pipeDeposit Rh.γn.N γk st ∗ □ Rh.γn.N.img sn.Metadata'.Index' D)

instance snapSReq_persistent (Rh : RaftHttp GF) (R : http.HReq) (γk : GName)
    (Pre Φ : List w8 → Prop) : Persistent (snapSReq Rh R γk Pre Φ) := by
  unfold snapSReq; infer_instance

/-- **A raft member's address's protocol** (stage 4: the pipeline's part; stage 5a: the streams';
stage 6c: the prober's): a `POST` to `/raft` is a pipeline request, a `GET` of another path than
the prober's (`probingPath`) a stream request; a `/raft` response is not a `403` (the status
`errMemberRemoved` is reported for, which no member of a static cluster answers; 2026-10-24,
stage 7d: nor a snapshot response, whose handler's statuses are `204`, `400`, `405`, `412`, `500`
and a `writerToResponse`'s, none here), and a `200` of
another path than the prober's is a stream's (`streamResp`; the pipeline answers `204`), a
`POST` to the snapshot path a snapshot sender's (`snapReq`), (D42) with a streamed body
(`snapStreamed`, its contract `snapSReq`); its response headers are `verHdrOk`. The prober's `GET`s (`addPeerToProber`'s axiom) and their
answers (`probing.NewHandler`'s) are anything else. -/
def raftProto (Rh : RaftHttp GF) : http.Proto GF where
  req R γk := iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk))
  req_pers R γk := by infer_instance
  resp R γk st w := iprop(⌜(R.path = go!"/raft" ∨ R.path = snapPath → st ≠ W64 403) ∧ st ≠ W64 410⌝ ∗
    (⌜R.path ≠ probingPath⌝ → streamResp Rh R γk st w))
  resp_pers R γk st w := by infer_instance
  rhdr _ hs := verHdrOk hs
  streamed R := snapStreamed R
  sreq R γk Pre Φ := snapSReq Rh R γk Pre Φ
  sreq_pers R γk Pre Φ := by infer_instance

/-- The raft network's HTTP network: every address's protocol is a raft member's. -/
def raftHttpNet (Rh : RaftHttp GF) : http.HttpNet GF := ⟨fun _ => raftProto Rh⟩

/-- **The reader's tokens** (exclusive): the authority of `γw`, holding indices below `n` only
(the frames read so far). -/
def streamRd (γw : GName) (n : Nat) : IProp GF :=
  iprop(∃ m : GMap Nat Unit, ghostMapAuth γw 1 m ∗ ⌜∀ j, (m.lookup j).isSome → j < n⌝)

end defs

/-! ## Lemmas -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A response other than a `200` carries nothing of a stream. -/
theorem streamResp_not200 (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64)
    (w : List w8) (h : st ≠ W64 200) : ⊢ streamResp Rh R γk st w := by
  unfold streamResp
  iintro %h'
  exact absurd h' h

/-- **A member's response of a status other than `403` and `200`** is in its protocol. -/
theorem raftProto_resp_of (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64)
    (w : List w8) (h403 : st ≠ W64 403) (h200 : st ≠ W64 200) (h410 : st ≠ W64 410) :
    ⊢ (raftProto Rh).resp R γk st w := by
  show ⊢ iprop(⌜(R.path = go!"/raft" ∨ R.path = snapPath → st ≠ W64 403) ∧ st ≠ W64 410⌝ ∗
    (⌜R.path ≠ probingPath⌝ → streamResp Rh R γk st w))
  isplitr
  · ipureintro; exact ⟨fun _ => h403, h410⟩
  · iintro -; iapply streamResp_not200 Rh R γk st w h200

/-- Nothing sent is a stream's bytes. -/
theorem streamSent_nil (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64) :
    ⊢ streamSent C N γw rid [] := by
  unfold streamSent
  iexists [], C.init
  isplitr
  · ipureintro; exact ⟨Chain.nil _, List.nil_prefix⟩
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **A stream request's `200`, before any byte** (the stream handler's `WriteHeader(200)`): in the
protocol, for a request registered as a stream's, of a path other than `/raft` and the
snapshot's. -/
theorem raftProto_resp_stream_200 (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (c : StreamKey)
    (hp : R.path ≠ go!"/raft" ∧ R.path ≠ snapPath) :
    ⊢ streamReg Rh γk c -∗ (raftProto Rh).resp R γk (W64 200) [] := by
  iintro #Hreg
  simp only [raftProto]
  isplitr
  · ipureintro; exact ⟨fun h => h.elim (absurd · hp.1) (absurd · hp.2), by decide⟩
  iintro -
  unfold streamResp
  iintro -
  iexists c
  iframe #
  iapply streamSent_nil

/-- A stream's path is not `/raft`. -/
theorem streamPath_ne_raft (t : StreamTy) (rid : w64) : streamPath t rid ≠ go!"/raft" := by
  intro h
  have := congrArg List.length h
  cases t <;> simp [streamPath, StreamTy.endpoint] at this <;> omega

/-- A stream's path is not the snapshot's. -/
theorem streamPath_ne_snap (t : StreamTy) (rid : w64) : streamPath t rid ≠ snapPath := by
  intro h
  have := congrArg (List.take 13) h
  cases t <;> simp [streamPath, StreamTy.endpoint, snapPath] at this

/-- A member's `/raft` or snapshot response is not a `403`. -/
theorem raftProto_resp_403 (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64)
    (w : List w8) :
    (raftProto Rh).resp R γk st w ⊢ ⌜R.path = go!"/raft" ∨ R.path = snapPath → st ≠ W64 403⌝ := by
  show iprop(⌜(R.path = go!"/raft" ∨ R.path = snapPath → st ≠ W64 403) ∧ st ≠ W64 410⌝ ∗
    (⌜R.path ≠ probingPath⌝ → streamResp Rh R γk st w)) ⊢ _
  iintro ⟨%h, -⟩
  ipureintro; exact h.1

/-- A member's response is never a `410` (2026-10-23, rafthttp stage 6: no member is removed,
`netRaftOk`'s `IsIDRemoved` is `false`, so the stream handler does not answer it). -/
theorem raftProto_resp_410 (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64)
    (w : List w8) : (raftProto Rh).resp R γk st w ⊢ ⌜st ≠ W64 410⌝ := by
  show iprop(⌜(R.path = go!"/raft" ∨ R.path = snapPath → st ≠ W64 403) ∧ st ≠ W64 410⌝ ∗
    (⌜R.path ≠ probingPath⌝ → streamResp Rh R γk st w)) ⊢ _
  iintro ⟨%h, -⟩
  ipureintro; exact h.2

/-- A pipeline request is in a member's protocol. -/
theorem raftProto_req_of_pipe (Rh : RaftHttp GF) (R : http.HReq) (γk : GName)
    (h : R.meth = go!"POST") (hp : R.path = go!"/raft") :
    pipeReq Rh R γk ⊢ (raftProto Rh).req R γk := by
  show pipeReq Rh R γk ⊢ iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk))
  iintro #Hp
  isplitr
  · iintro -; iexact Hp
  isplitr
  · iintro %hg
    rw [h] at hg
    exact absurd hg.1 (by decide)
  · iintro %hs
    rw [hp] at hs
    exact absurd hs.2 (by simp [snapPath])

/-- A snapshot request is in a member's protocol (D42, stage 7d). -/
theorem raftProto_req_of_snap (Rh : RaftHttp GF) (R : http.HReq) (γk : GName)
    (h : R.meth = go!"POST") (hp : R.path = snapPath) :
    snapReq Rh R γk ⊢ (raftProto Rh).req R γk := by
  show snapReq Rh R γk ⊢ iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk))
  iintro #Hs
  isplitr
  · iintro %hr
    rw [hp] at hr
    exact absurd hr.2 (by simp [snapPath])
  isplitr
  · iintro %hg
    rw [h] at hg
    exact absurd hg.1 (by decide)
  · iintro -; iexact Hs

/-- A member's protocol of a `POST` to `/raft`: a pipeline request. -/
theorem raftProto_req_pipe (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    (raftProto Rh).req R γk ⊢ ⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk := by
  show iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk)) ⊢ _
  iintro ⟨Hp, -, -⟩
  iexact Hp

/-- A member's protocol of a `GET` of another path than the prober's: a stream request. -/
theorem raftProto_req_stream (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    (raftProto Rh).req R γk ⊢ ⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk := by
  show iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk)) ⊢ _
  iintro ⟨-, Hs, -⟩
  iexact Hs

/-- A stream request is in a member's protocol. -/
theorem raftProto_req_of_stream (Rh : RaftHttp GF) (R : http.HReq) (γk : GName)
    (h : R.meth = go!"GET") : streamReq Rh R γk ⊢ (raftProto Rh).req R γk := by
  show streamReq Rh R γk ⊢ iprop((⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk) ∗
    (⌜R.meth = go!"GET" ∧ R.path ≠ probingPath⌝ → streamReq Rh R γk) ∗
    (⌜R.meth = go!"POST" ∧ R.path = snapPath⌝ → snapReq Rh R γk))
  iintro #Hs
  isplitr
  · iintro %hp
    rw [h] at hp
    exact absurd hp.1 (by decide)
  isplitr
  · iintro -; iexact Hs
  · iintro %hp
    rw [h] at hp
    exact absurd hp.1 (by decide)

/-- A stream's path is not the prober's. -/
theorem streamPath_ne_probing (t : StreamTy) (rid : w64) : streamPath t rid ≠ probingPath := by
  intro h
  have := congrArg List.length h
  cases t <;> simp [streamPath, StreamTy.endpoint, probingPath] at this <;> omega

/-- **A response to the prober's path** of a status other than `410`: in a member's protocol. -/
theorem raftProto_resp_probing (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) (st : w64)
    (w : List w8) (hp : R.path = probingPath) (h410 : st ≠ W64 410) :
    ⊢ (raftProto Rh).resp R γk st w := by
  simp only [raftProto]
  isplitr
  · ipureintro
    refine ⟨fun h => ?_, h410⟩
    rw [hp] at h
    exact absurd h (by simp [probingPath, snapPath])
  iintro %h
  exact absurd hp h

/-- **Allocate a stream request's ticket**, registered with the connection of a fresh `γw`, of
type `t` and reader `rid`; the reader's tokens at `0`. -/
theorem stream_ticket_alloc (Rh : RaftHttp GF) (t : StreamTy) (rid : w64) (E : CoPset)
    (HE : ↑streamRegN ⊆ E) :
    ⊢ streamRegInv Rh ={E}=∗ ∃ γk γw, http.reqTicket γk ∗ streamReg Rh γk (γw, t, rid) ∗
      streamRd γw 0 := by
  iintro #Hinv
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γw, Hw⟩
  unfold streamRegInv
  iinv Hinv with ⟨%m, >Ha⟩ Hclose
  obtain ⟨l, hl⟩ := m.finite
  imod dghostVar_alloc_strong (GF := GF) () (· ∉ l) (pred_infinite_not_mem l) with ⟨%γk, %Hγk, Ht⟩
  have Hm : m.lookup γk = none := by
    cases h : m.lookup γk with
    | none => rfl
    | some _ => exact absurd (hl γk (by simp [h])) Hγk
  imod ghost_map_insert_persist γk (γw, t, rid) Hm $$ Ha with ⟨Ha, #Hr⟩
  imod Hclose $$ [Ha] with -
  · inext; iexists _; iexact Ha
  imodintro
  iexists γk, γw
  isplitl [Ht]
  · unfold http.reqTicket; iexact Ht
  isplitr
  · unfold streamReg; iexact Hr
  · unfold streamRd
    iexists ∅
    isplitl [Hw]
    · iexact Hw
    · ipureintro; intro j hj; simp at hj

/-- **One connection per ticket**: two registrations of a ticket agree. -/
theorem streamReg_agree (Rh : RaftHttp GF) (γk : GName) (c c' : StreamKey) :
    ⊢ streamReg Rh γk c -∗ streamReg Rh γk c' -∗ ⌜c = c'⌝ := by
  unfold streamReg
  iintro H1 H2
  iapply ghostMapElem_agree $$ H1 H2

/-- **Deposit** a message's one-shot part as the `i`-th frame's. -/
theorem stream_deposit (N : NetPayload GF) (γw : GName) (i : Nat) (st : MsgSt) (E : CoPset) :
    ⊢ N.O st ={E}=∗ streamDeposit N γw i st := by
  iintro HO
  unfold streamDeposit
  iapply inv_alloc
  inext
  ileft; iexact HO

/-- **Withdraw** the `n`-th frame's deposit with the reader's tokens at `n` (and a later credit):
the one-shot part, the tokens at `n + 1`. -/
theorem stream_withdraw (N : NetPayload GF) (γw : GName) (n : Nat) (st : MsgSt) (E : CoPset)
    (HE : ↑streamN ⊆ E) :
    ⊢ streamDeposit N γw n st -∗ streamRd γw n -∗ £ 1 ={E}=∗ N.O st ∗ streamRd γw (n + 1) := by
  iintro #Hd Hrd Hlc
  unfold streamRd
  icases Hrd with ⟨%m, Ha, %Hm⟩
  have Hn : m.lookup n = none := by
    cases h : m.lookup n with
    | none => rfl
    | some _ => exact absurd (Hm n (by simp [h])) (Nat.lt_irrefl n)
  imod ghost_map_insert n () Hn $$ Ha with ⟨Ha, Htok⟩
  unfold streamDeposit
  iinv Hd with Hc Hclose
  imod lc_fupd_elim_later $$ Hlc Hc with Hc
  icases Hc with (HO | Htok')
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    imodintro
    isplitl [HO]
    · iexact HO
    · iexists _
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        intro j hj
        by_cases hjn : j = n
        · omega
        · have : (m.insert n ()).lookup j = m.lookup j := GMap.lookup_insert_ne m () (Ne.symm hjn)
          rw [this] at hj
          have := Hm j hj
          omega
  · ihave %Hbad := ghostMapElem_valid_2 n γw _ _ () () $$ Htok Htok'
    exfalso
    exact absurd (DFrac.valid_own_op Hbad.1) (by decide)

/-- The reader's tokens move past a frame it does not withdraw (a heartbeat, a dropped one). -/
theorem streamRd_skip (γw : GName) (n : Nat) : ⊢ streamRd (GF := GF) γw n -∗ streamRd γw (n + 1) := by
  unfold streamRd
  iintro ⟨%m, Ha, %Hm⟩
  iexists m
  isplitl [Ha]
  · iexact Ha
  · ipureintro; intro j hj; have := Hm j hj; omega

/-- **The writer's next frame**: having written the chain `fr` (with its frames' facts), any prefix
of `fr` and one more frame carrying its `frameDep` is a stream's bytes. -/
theorem streamSent_extend (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64)
    (fr : List (MsgWire × List w8)) (s s' : C.S) (w : MsgWire) (b : List w8) (k : Nat)
    (Hfr : Chain C C.init fr s) (Hf : C.F s w b s') :
    ⊢ ([∗list] i ↦ f ∈ fr, frameDep N γw rid i f.1) -∗ frameDep N γw rid fr.length w -∗
      streamSent C N γw rid (chainBytes fr ++ b.take k) := by
  iintro #Hfs #Hd
  unfold streamSent
  iexists fr ++ [(w, b)], s'
  isplitr
  · ipureintro
    refine ⟨Hfr.snoc Hf, ?_⟩
    rw [chainBytes_append]
    exact List.prefix_append_right_inj _ |>.mpr (by simpa using List.take_prefix k b)
  · iapply (BigSepL.bigSepL_snoc (Φ := fun i (f : MsgWire × List w8) => frameDep N γw rid i f.1)).2
    isplitl
    · iexact Hfs
    · iexact Hd

/-- **The written chain's bytes are a stream's.** -/
theorem streamSent_chain (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64)
    (fr : List (MsgWire × List w8)) (s : C.S) (Hfr : Chain C C.init fr s) :
    ⊢ ([∗list] i ↦ f ∈ fr, frameDep N γw rid i f.1) -∗ streamSent C N γw rid (chainBytes fr) := by
  iintro #Hfs
  unfold streamSent
  iexists fr, s
  isplitr
  · ipureintro; exact ⟨Hfr, List.prefix_refl _⟩
  · iexact Hfs

/-- **What the reader knows of its next bytes**: having decoded the chain `fr` (to `s`), any `ys`
it may read next, if a stream's bytes, are empty or compatible with a frame from `s`. -/
theorem streamSent_compat (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64)
    (fr : List (MsgWire × List w8)) (s : C.S) (ys : List w8) (Hfr : Chain C C.init fr s) :
    ⊢ streamSent C N γw rid (chainBytes fr ++ ys) -∗
      ⌜ys = [] ∨ ∃ (w : MsgWire) (bs : List w8) (s1 : C.S) (z1 z2 : List w8),
        C.F s w bs s1 ∧ ys ++ z1 = bs ++ z2⌝ := by
  unfold streamSent
  iintro ⟨%fr', %s', %Hc, -⟩
  ipureintro
  obtain ⟨Hc', z, hz⟩ := Hc
  exact Hfr.compat Hc' hz

/-- **The msgappv2 decoder's premise** from a stream's bytes. -/
theorem streamSent_v2Compat (N : NetPayload GF) (γw : GName) (frm to : w64)
    (fr : List (MsgWire × List w8)) (s : V2St) (ys : List w8)
    (Hfr : Chain (v2Codec frm to) (v2Codec frm to).init fr s) :
    ⊢ streamSent (v2Codec frm to) N γw to (chainBytes fr ++ ys) -∗ ⌜V2Compat frm to s ys⌝ := by
  iintro Hs
  ihave %H := streamSent_compat _ N γw to fr s ys Hfr $$ Hs
  ipureintro
  rcases H with rfl | ⟨w, bs, s1, z1, z2, hf, he⟩
  · exact ⟨hbWire, [W8 0], s, [W8 0], [], Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨w, bs, s1, z1, z2, hf, he⟩

/-- **The reader's decoded frame carries its `frameDep`**: having decoded the chain `fr` (to `s`)
and then a frame `(w, bs)` from `s`, if its bytes so far are a stream's, the frame's facts at
index `fr.length`. -/
theorem streamSent_frame (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64)
    (fr : List (MsgWire × List w8)) (s s1 : C.S) (w : MsgWire) (bs : List w8)
    (Hfr : Chain C C.init fr s) (Hf : C.F s w bs s1) :
    ⊢ streamSent C N γw rid (chainBytes fr ++ bs) -∗ frameDep N γw rid fr.length w := by
  unfold streamSent
  iintro ⟨%fr', %s', %Hc, #Hfs⟩
  obtain ⟨Hc', z, hz⟩ := Hc
  have Hi := Hfr.frame Hf Hc' (by simpa [List.append_assoc] using hz)
  obtain ⟨hlt, Heq⟩ := List.getElem?_eq_some_iff.mp Hi
  ihave Hd := BigSepL.bigSepL_lookup (Φ := fun i f => frameDep N γw rid i f.1) Hi $$ Hfs
  simp only
  iexact Hd

end lemmas

end EtcdGrove
end Perennial
