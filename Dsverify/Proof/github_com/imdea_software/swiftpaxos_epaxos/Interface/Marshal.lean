/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Interface/Marshal.lean (notes/dsv-epaxos.md).
Changed: the streams are dsv-bufio's `*bufio.Writer`/`*bufio.Reader` over Perennial's `io`
contracts (`EtcdGrove.bufio.ownBufWriter`/`ownBufReader`, `Spec/bufio/`), not the lab harness's
`bufio.ownWriter`/`ownReader`; the writer's and the reader's parameters are bundled (`BufWr`,
`BufRd`); `nextIs` is stated over a persistent fact of the stream state (`BufRd.F`, given back by
`bufio.ownBufReader_fact`; for a connection `▷ protoPrefix`, `net.connReader_proto`), up to a
later; an `Unmarshal`'s error is only non-`nil` (the lab's `net.rpc.errAny` is the harness's);
`epaxos.putVarint.spec` and the packages' initialization facts are `Interface/Varint.lean`'s.

The marshalers of the messages on the replicas' paths (`state`, `replica/defs`, `epaxos`), grouped
here (one `def <pkg>.<Type>.<Method>.spec : Prop` per method):

* **Marshal** to an `io.Writer` holding a `*bufio.Writer` `bw` (`wrOwn bw wr sent pend err`, the
  writer `wr : BufWr`): given `□ Q (sent ++ pend ++ enc v)` **when the writer is healthy**
  (`err = nil`; with a sticky error nothing is written, so nothing is needed: the code keeps
  writing after errors, and `sent ++ pend` may then end mid-message), the writer has accepted a
  prefix of `enc v` after what it had (`wroteSome`): all of it when its final error is `nil`, none
  once it has a sticky error. The marshalers ignore `Write`'s errors (Go code), so the caller
  learns the outcome from the writer's error only (`Flush`). The receiver is read with any
  fraction.
* **Unmarshal** from an `io.Reader` holding a `*bufio.Reader` `br` (`rdOwn br rd R`, the reader
  `rd : BufRd`), when the stream after `R` is a prefix of an encoding (`nextIs rd R enc wf`:
  whatever the reader has been delivered, by the stream fact `rd.F`, continues `R` with a prefix
  of some `enc v ++ _` with `wf v`): on `nil` the reader has returned exactly `enc v` more, for a
  `v` with `wf v`, which the target now holds in fresh heap values (its slices owned; command
  values read-only); on an error some bytes were consumed and the target holds some value. The
  epaxos messages' `Unmarshal` asserts `rr.(byteReader)`: a `*bufio.Reader` has `ReadByte`, so the
  assertion succeeds and no reader is wrapped around it.
* **The `rpc.Serializable` dispatch** (`r.RPC.Get(code)`'s prototypes, `SendMsg`'s `msg`): a
  protocol message kind `k` (`MsgKind`, code 9..17) has the Go type `k.ty`; `msgObj obj m dq`: the
  interface `obj` holds a pointer to a value of `m`'s kind with image `m`. The laws
  `Serializable.New.spec`, `Serializable.Marshal.spec`, `Serializable.Unmarshal.spec` state what
  the dynamic calls do on such objects (the per-type specs, through the method tables).
* **Varints**: the epaxos unmarshalers call the package-local `readVarint` (`epaxos/varint.go`, a
  byte-identical copy of `encoding/binary`'s): `epaxos.readVarint.spec`, proved in
  `wire/Varint/ReadVarint.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Varint
public import Proof.bufio.Own

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Message kinds -/

/-- The protocol message kinds (their rpc codes 9..17, `epaxos.New`'s registration order). -/
inductive MsgKind where
  | prepare | prepareReply | preAccept | preAcceptReply | accept | acceptReply | commit
  | tryPreAccept | tryPreAcceptReply
deriving DecidableEq

def MsgKind.all : List MsgKind :=
  [.prepare, .prepareReply, .preAccept, .preAcceptReply, .accept, .acceptReply, .commit,
    .tryPreAccept, .tryPreAcceptReply]

/-- The kind's rpc code. -/
def MsgKind.code : MsgKind → w8
  | .prepare => W8 9 | .prepareReply => W8 10 | .preAccept => W8 11 | .preAcceptReply => W8 12
  | .accept => W8 13 | .acceptReply => W8 14 | .commit => W8 15 | .tryPreAccept => W8 16
  | .tryPreAcceptReply => W8 17

/-- The kind of a protocol message (`none` for the beacons). -/
def model.Msg.kind : Msg → Option MsgKind
  | .prepare _ => some .prepare | .prepareReply _ => some .prepareReply
  | .preAccept _ => some .preAccept | .preAcceptReply _ => some .preAcceptReply
  | .accept _ => some .accept | .acceptReply _ => some .acceptReply
  | .commit _ => some .commit | .tryPreAccept _ => some .tryPreAccept
  | .tryPreAcceptReply _ => some .tryPreAcceptReply
  | .beacon _ | .beaconReply _ => none

theorem model.Msg.kind_code (m : Msg) (k : MsgKind) (h : m.kind = some k) : m.code = k.code := by
  cases m <;> cases k <;> simp_all [Msg.kind, Msg.code, MsgKind.code]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions]

/-- The Go type of a kind's message. -/
def MsgKind.ty : MsgKind → go.GoType
  | .prepare => epaxos.Prepare.ty | .prepareReply => epaxos.PrepareReply.ty
  | .preAccept => epaxos.PreAccept.ty | .preAcceptReply => epaxos.PreAcceptReply.ty
  | .accept => epaxos.Accept.ty | .acceptReply => epaxos.AcceptReply.ty
  | .commit => epaxos.Commit.ty | .tryPreAccept => epaxos.TryPreAccept.ty
  | .tryPreAcceptReply => epaxos.TryPreAcceptReply.ty

/-! ## Streams -/

/-- A `*bufio.Writer` as an `io.Writer`. -/
def bwIface (bw : Loc) : GoInterface := interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw

/-- A `*bufio.Reader` as an `io.Reader` (or `io.ByteReader`, `byteReader`). -/
def brIface (br : Loc) : GoInterface := interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br

/-- The parameters of a `*bufio.Writer` (`EtcdGrove.bufio.ownBufWriter`): the underlying writer
`wi` by the contract `io.writerOk wi J Q Ew`, the buffer's size `sz`; `Q` closed under prefixes
(a connection's protocol: `ProtoPrefixClosed`), which the marshalers' partial writes need. -/
structure BufWr (GF : BundledGFunctors) where
  wi : GoInterfaceOk
  J : List w8 → IProp GF
  Q : List w8 → IProp GF
  Ew : GoInterface → IProp GF
  sz : Nat
  Q_pre : ∀ x y : List w8, Q (x ++ y) ⊢ Q x

/-- The writer `bw` with parameters `wr`, having sent `sent`, buffering `pend`, error `err`. -/
abbrev wrOwn (bw : Loc) (wr : BufWr GF) (sent pend : List w8) (err : GoInterface) : IProp GF :=
  EtcdGrove.bufio.ownBufWriter bw wr.wi wr.J wr.Q wr.Ew wr.sz sent pend err

/-- The parameters of a `*bufio.Reader` (`EtcdGrove.bufio.ownBufReader`): the underlying reader
`ri` by the contract `io.readerOk ri Pre S E`, reads of a non-empty buffer allowed everywhere
(`Pre_pos`; a connection's `Pre` is `0 < m`), and a persistent, prefix-closed fact `F` of the
stream states `S` (`bufio.ownBufReader_fact`'s premises: for a connection
`▷ protoPrefix P cn`, `net.connReader_proto`). -/
structure BufRd (GF : BundledGFunctors) where
  ri : GoInterfaceOk
  Pre : List w8 → Nat → Prop
  S : List w8 → IProp GF
  E : List w8 → GoInterface → IProp GF
  F : List w8 → IProp GF
  F_pers : ∀ r, Persistent (F r)
  F_of : ∀ r, S r ⊢ S r ∗ F r
  F_pre : ∀ x y : List w8, F (x ++ y) ⊢ F x
  Pre_pos : ∀ r m, 0 < m → Pre r m

instance BufRd.F_persistent (rd : BufRd GF) (r : List w8) : Persistent (rd.F r) := rd.F_pers r

/-- The reader `br` with parameters `rd`, having returned `R`. -/
abbrev rdOwn (br : Loc) (rd : BufRd GF) (R : List w8) : IProp GF :=
  EtcdGrove.bufio.ownBufReader br rd.ri rd.Pre rd.S rd.E R

/-- A writer that had sent `sent` and buffered `pend` (error `err`), given `new`, now has sent
`sent'` and buffers `pend'` with error `e`: it accepted a prefix of `new`, all of it if `e` is
`nil`, none if `err` was not. -/
def wroteSome (sent pend new sent' pend' : List w8) (err e : GoInterface) : Prop :=
  sent <+: sent' ∧ sent ++ pend <+: sent' ++ pend' ∧ sent' ++ pend' <+: sent ++ pend ++ new ∧
    (e = interface.nil → sent' ++ pend' = sent ++ pend ++ new) ∧
    (err ≠ interface.nil → e = err ∧ sent' ++ pend' = sent ++ pend)

/-- The stream the reader `rd` has returned `R` of continues with a prefix of an encoding
`enc v ++ _` of some `v` with `wf v`, as far as it has been delivered (a step later; persistent;
see the file header). -/
def nextIs {A : Type} (rd : BufRd GF) (R : List w8) (enc : A → List w8) (wf : A → Prop) :
    IProp GF :=
  iprop(□ ∀ r : List w8, rd.F r -∗
    ▷ ⌜R <+: r → ∃ (v : A) (ext : List w8), wf v ∧ r.drop R.length <+: enc v ++ ext⌝)

instance nextIs_persistent {A : Type} (rd : BufRd GF) (R : List w8) (enc : A → List w8)
    (wf : A → Prop) : Persistent (nextIs rd R enc wf) := by
  unfold nextIs; infer_instance

/-- The spec of a `Marshal(w)` (the method value `fn`, package `pkg`) writing `bs`, holding
`Rs` (the receiver's resources, returned). The protocol of the new stream is needed only on a
healthy writer (`err = nil`; see the file header). -/
def marshalTriple (pkg : IProp GF) (fn : val) (Rs : IProp GF) (bs : List w8) : Prop :=
  ∀ (bw : Loc) (wr : BufWr GF) (sent pend : List w8) (err : GoInterface),
  {{ pkg ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wrOwn bw wr sent pend err ∗
      (⌜err = interface.nil⌝ -∗ □ wr.Q (sent ++ pend ++ bs)) ∗ Rs }}
    (App (Val fn) (Val #(bwIface bw)))
  {{ RET #(); Rs ∗ ∃ (sent' pend' : List w8) (e : GoInterface),
      ⌜wroteSome sent pend bs sent' pend' err e⌝ ∗ wrOwn bw wr sent' pend' e }}

/-- The spec of an `Unmarshal(r)` (the method value `fn`, package `pkg`) reading an encoding
`enc v` (with `wf v`): from `Rpre` (the target), on `nil` `Rok v`, on an error `Rerr`. -/
def unmarshalTriple {A : Type} (pkg : IProp GF) (fn : val) (Rpre : IProp GF)
    (enc : A → List w8) (wf : A → Prop) (Rok : A → IProp GF) (Rerr : IProp GF) : Prop :=
  ∀ (br : Loc) (rd : BufRd GF) (R : List w8),
  {{ pkg ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ rdOwn br rd R ∗ nextIs rd R enc wf ∗
      Rpre }}
    (App (Val fn) (Val #(brIface br)))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ v : A, ⌜wf v⌝ ∗ rdOwn br rd (R ++ enc v) ∗ Rok v) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ data : List w8, rdOwn br rd (R ++ data) ∗ Rerr) }}

/-! ## Heap images -/

/-- An `[]int32` slice holding `ds`. -/
def ownDeps (sl : GoSlice) (ds : List w32) (dq : DFrac) : IProp GF := sl ↦*{dq} ds

def ownPrepare (l : Loc) (m : Prepare) (dq : DFrac) : IProp GF :=
  l ↦{dq} epaxos.Prepare.mk m.leaderId m.replica m.inst m.ballot

def ownPrepareReply (l : Loc) (m : PrepareReply) (dq : DFrac) (dq1 : DFrac := dq)
    (dq2 : DFrac := dq) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦{dq} epaxos.PrepareReply.mk m.acceptorId m.replica m.inst m.ballot
      m.vballot m.status cs m.seq ds ∗ ownCmds cs m.command dq1 ∗ ownDeps ds m.deps dq2)

def ownPreAccept (l : Loc) (m : PreAccept) (dq : DFrac) (dq1 : DFrac := dq)
    (dq2 : DFrac := dq) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦{dq} epaxos.PreAccept.mk m.leaderId m.replica m.inst m.ballot cs
      m.seq ds ∗ ownCmds cs m.command dq1 ∗ ownDeps ds m.deps dq2)

def ownPreAcceptReply (l : Loc) (m : PreAcceptReply) (dq : DFrac) (dq1 : DFrac := dq)
    (dq2 : DFrac := dq) : IProp GF :=
  iprop(∃ ds cds : GoSlice, l ↦{dq} epaxos.PreAcceptReply.mk m.replica m.inst m.ballot m.vballot
      m.seq ds cds m.status ∗ ownDeps ds m.deps dq1 ∗ ownDeps cds m.committedDeps dq2)

def ownAccept (l : Loc) (m : Accept) (dq : DFrac) (dq1 : DFrac := dq)
    (dq2 : DFrac := dq) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦{dq} epaxos.Accept.mk m.leaderId m.replica m.inst m.ballot cs
      m.seq ds ∗ ownCmds cs m.command dq1 ∗ ownDeps ds m.deps dq2)

def ownAcceptReply (l : Loc) (m : AcceptReply) (dq : DFrac) : IProp GF :=
  l ↦{dq} epaxos.AcceptReply.mk m.replica m.inst m.ballot

def ownCommit (l : Loc) (m : Commit) (dq : DFrac) (dq1 : DFrac := dq)
    (dq2 : DFrac := dq) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦{dq} epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs
      m.seq ds ∗ ownCmds cs m.command dq1 ∗ ownDeps ds m.deps dq2)

def ownTryPreAccept (l : Loc) (m : TryPreAccept) (dq : DFrac) (dq1 : DFrac := dq)
    (dq2 : DFrac := dq) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦{dq} epaxos.TryPreAccept.mk m.leaderId m.replica m.inst m.ballot cs
      m.seq ds ∗ ownCmds cs m.command dq1 ∗ ownDeps ds m.deps dq2)

def ownTryPreAcceptReply (l : Loc) (m : TryPreAcceptReply) (dq : DFrac) : IProp GF :=
  l ↦{dq} epaxos.TryPreAcceptReply.mk m.acceptorId m.replica m.inst m.ballot m.vballot
    m.conflictReplica m.conflictInstance m.conflictStatus

/-- The protocol message `m` at `l` (`False` for the beacons, which are not `Serializable`s):
the struct at `dq`, its first slice (`Command`; `Deps` for a `PreAcceptReply`) at `dq1`, its
second slice (`Deps`; `CommittedDeps` for a `PreAcceptReply`) at `dq2` (both `dq` by default;
kinds without slices ignore them). -/
def ownMsg (l : Loc) (m : Msg) (dq : DFrac) (dq1 : DFrac := dq) (dq2 : DFrac := dq) :
    IProp GF :=
  match m with
  | .prepare x => ownPrepare l x dq
  | .prepareReply x => ownPrepareReply l x dq dq1 dq2
  | .preAccept x => ownPreAccept l x dq dq1 dq2
  | .preAcceptReply x => ownPreAcceptReply l x dq dq1 dq2
  | .accept x => ownAccept l x dq dq1 dq2
  | .acceptReply x => ownAcceptReply l x dq
  | .commit x => ownCommit l x dq dq1 dq2
  | .tryPreAccept x => ownTryPreAccept l x dq dq1 dq2
  | .tryPreAcceptReply x => ownTryPreAcceptReply l x dq
  | .beacon _ | .beaconReply _ => iprop(False)

/-- Some value of kind `k`'s Go type at `l` (a target before `Unmarshal`, or after a failed
one). -/
def ownAny (l : Loc) (k : MsgKind) : IProp GF :=
  match k with
  | .prepare => iprop(∃ v : epaxos.Prepare, l ↦ v)
  | .prepareReply => iprop(∃ v : epaxos.PrepareReply, l ↦ v)
  | .preAccept => iprop(∃ v : epaxos.PreAccept, l ↦ v)
  | .preAcceptReply => iprop(∃ v : epaxos.PreAcceptReply, l ↦ v)
  | .accept => iprop(∃ v : epaxos.Accept, l ↦ v)
  | .acceptReply => iprop(∃ v : epaxos.AcceptReply, l ↦ v)
  | .commit => iprop(∃ v : epaxos.Commit, l ↦ v)
  | .tryPreAccept => iprop(∃ v : epaxos.TryPreAccept, l ↦ v)
  | .tryPreAcceptReply => iprop(∃ v : epaxos.TryPreAcceptReply, l ↦ v)

/-- The `rpc.Serializable` `obj` holds a pointer to the protocol message `m` (its heap image:
the struct at `dq`, its slices at `dq1`, `dq2`, see `ownMsg`; all `dq` by default). -/
def msgObj (obj : GoInterface) (m : Msg) (dq : DFrac) (dq1 : DFrac := dq) (dq2 : DFrac := dq) :
    IProp GF :=
  iprop(∃ (k : MsgKind) (l : Loc), ⌜m.kind = some k ∧
    obj = interface.mkOk (go.GoType.PointerType k.ty) #l⌝ ∗ ownMsg l m dq dq1 dq2)

/-- A prototype of kind `k` (what `epaxos.New` registers: `new(T)`; only its type matters). -/
def protoObj (k : MsgKind) (obj : GoInterface) : Prop :=
  ∃ l : Loc, obj = interface.mkOk (go.GoType.PointerType k.ty) #l

/-! ## `epaxos`'s varints (`epaxos/varint.go`) -/

/-- `readVarint(r)` on a `*bufio.Reader` (as an `io.ByteReader`): reads one varint (as
`ReadByte`s). The stream continues with a varint encoding (`nextIs`), so the overflow error
(`errVarintOverflow`) is not reached; an error is the reader's (or `io.ErrUnexpectedEOF`). -/
def epaxos.readVarint.spec : Prop :=
  ∀ (br : Loc) (rd : BufRd GF) (R : List w8),
  {{ pkgInit_epaxos ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ rdOwn br rd R ∗
      nextIs rd R varintEnc (fun _ => True) }}
    (App (Val (@! epaxos.readVarint)) (Val #(brIface br)))
  {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
      (⌜err = interface.nil⌝ ∗ rdOwn br rd (R ++ varintEnc x)) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ data : List w8, rdOwn br rd (R ++ data)) }}

/-! ## `state` -/

/-- `(*Operation).Marshal`: one byte. -/
def state.Operation.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (op : w8),
  marshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Operation.ty @!! go!"Marshal") (l ↦{dq} op) [op]

def state.Operation.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (op0 : w8),
  unmarshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Operation.ty @!! go!"Unmarshal") (l ↦ op0)
    (fun op : w8 => [op]) (fun _ => True) (fun op => l ↦ op) iprop(∃ op : w8, l ↦ op)

/-- `(*Key).Marshal`: 8 bytes little-endian. -/
def state.Key.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (k : w64),
  marshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Key.ty @!! go!"Marshal") (l ↦{dq} k) (u64Le k)

def state.Key.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (k0 : w64),
  unmarshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Key.ty @!! go!"Unmarshal") (l ↦ k0)
    u64Le (fun _ => True) (fun k => l ↦ k) iprop(∃ k : w64, l ↦ k)

/-- `(*Value).Marshal` (non-nil receiver): `encValue` (its length field truncated to 16 bits). -/
def state.Value.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq dq' : DFrac) (sl : GoSlice) (v : List w8),
  marshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Value.ty @!! go!"Marshal")
    iprop(l ↦{dq} sl ∗ sl ↦*{dq'} v) (encValue v)

/-- `(*Value).Unmarshal`: a fresh slice. -/
def state.Value.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (sl0 : GoSlice),
  unmarshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Value.ty @!! go!"Unmarshal") (l ↦ sl0)
    encValue (fun v => v.length < 2 ^ 16) (fun v => iprop(∃ sl : GoSlice, l ↦ sl ∗ sl ↦* v))
    iprop(∃ sl : GoSlice, l ↦ sl)

/-- `(*Command).Marshal`. -/
def state.Command.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (cv : state.Command) (wc : WCmd),
  marshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Command.ty @!! go!"Marshal")
    iprop(l ↦{dq} cv ∗ cmdOk cv wc) (encCommand wc)

/-- `(*Command).Unmarshal`: the value in a fresh (read-only) slice. -/
def state.Command.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (cv0 : state.Command),
  unmarshalTriple (pkgInit_state (GF := GF))
    (l @!! go.GoType.PointerType state.Command.ty @!! go!"Unmarshal") (l ↦ cv0)
    encCommand cmdWf (fun wc => iprop(∃ cv : state.Command, l ↦ cv ∗ cmdOk cv wc))
    iprop(∃ cv : state.Command, l ↦ cv)

/-! ## `replica/defs` -/

/-- `defs.Propose` at `l` with these fields (its command's value read-only). -/
def ownPropose (l : Loc) (cmdId clientId : w32) (wc : WCmd) (ts : w64) (dq : DFrac) :
    IProp GF :=
  iprop(∃ cv : state.Command, l ↦{dq} replica.defs.Propose.mk cmdId clientId cv ts ∗ cmdOk cv wc)

/-- `defs.Propose`'s pure image. -/
structure ProposeV where
  cmdId : w32
  clientId : w32
  cmd : WCmd
  ts : w64

def ProposeV.enc (p : ProposeV) : List w8 := encPropose p.cmdId p.clientId p.cmd p.ts

def replica.defs.Propose.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (p : ProposeV),
  marshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.Propose.ty @!! go!"Marshal")
    (ownPropose l p.cmdId p.clientId p.cmd p.ts dq) p.enc

def replica.defs.Propose.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (v0 : replica.defs.Propose),
  unmarshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.Propose.ty @!! go!"Unmarshal") (l ↦ v0)
    ProposeV.enc (fun p => cmdWf p.cmd)
    (fun p => ownPropose l p.cmdId p.clientId p.cmd p.ts (DFrac.own 1))
    iprop(∃ v : replica.defs.Propose, l ↦ v)

/-- `defs.ProposeReplyTS`'s pure image. -/
structure ProposeReplyV where
  ok : w8
  cmdId : w32
  val : List w8
  ts : w64

def ProposeReplyV.enc (p : ProposeReplyV) : List w8 := encProposeReplyTS p.ok p.cmdId p.val p.ts

def replica.defs.ProposeReplyTS.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq dq' : DFrac) (p : ProposeReplyV) (sl : GoSlice),
  marshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.ProposeReplyTS.ty @!! go!"Marshal")
    iprop(l ↦{dq} replica.defs.ProposeReplyTS.mk p.ok p.cmdId sl p.ts ∗ sl ↦*{dq'} p.val) p.enc

def replica.defs.ProposeReplyTS.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (v0 : replica.defs.ProposeReplyTS),
  unmarshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.ProposeReplyTS.ty @!! go!"Unmarshal") (l ↦ v0)
    ProposeReplyV.enc (fun p => p.val.length < 2 ^ 16)
    (fun p => iprop(∃ sl : GoSlice, l ↦ replica.defs.ProposeReplyTS.mk p.ok p.cmdId sl p.ts ∗
      sl ↦* p.val))
    iprop(∃ v : replica.defs.ProposeReplyTS, l ↦ v)

def replica.defs.Beacon.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (ts : w64),
  marshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.Beacon.ty @!! go!"Marshal")
    (l ↦{dq} replica.defs.Beacon.mk ts) (encBeacon ts)

def replica.defs.Beacon.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (v0 : replica.defs.Beacon),
  unmarshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.Beacon.ty @!! go!"Unmarshal") (l ↦ v0)
    encBeacon (fun _ => True) (fun ts => l ↦ replica.defs.Beacon.mk ts)
    iprop(∃ v : replica.defs.Beacon, l ↦ v)

def replica.defs.BeaconReply.Marshal.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (ts : w64),
  marshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.BeaconReply.ty @!! go!"Marshal")
    (l ↦{dq} replica.defs.BeaconReply.mk ts) (encBeacon ts)

def replica.defs.BeaconReply.Unmarshal.spec : Prop :=
  ∀ (l : Loc) (v0 : replica.defs.BeaconReply),
  unmarshalTriple (pkgInit_defs (GF := GF))
    (l @!! go.GoType.PointerType replica.defs.BeaconReply.ty @!! go!"Unmarshal") (l ↦ v0)
    encBeacon (fun _ => True) (fun ts => l ↦ replica.defs.BeaconReply.mk ts)
    iprop(∃ v : replica.defs.BeaconReply, l ↦ v)

/-! ## `epaxos`: per kind (the nine types' `Marshal` / `Unmarshal` / `New`) -/

/-- `(*T).Marshal` for kind `k`'s type `T`, on a message of that kind: its body (the struct and
each slice read with any fractions). -/
def epaxos.Marshal.spec (k : MsgKind) : Prop :=
  ∀ (l : Loc) (dq dq1 dq2 : DFrac) (m : Msg), m.kind = some k →
  marshalTriple (pkgInit_epaxos (GF := GF))
    (l @!! go.GoType.PointerType k.ty @!! go!"Marshal") (ownMsg l m dq dq1 dq2) m.body

/-- `(*T).Unmarshal` for kind `k`'s type `T` (`rr` a `*bufio.Reader`: `rr.(byteReader)`
succeeds): a well-formed message of kind `k`, its slices fresh. -/
def epaxos.Unmarshal.spec (k : MsgKind) : Prop :=
  ∀ (l : Loc),
  unmarshalTriple (pkgInit_epaxos (GF := GF))
    (l @!! go.GoType.PointerType k.ty @!! go!"Unmarshal") (ownAny l k)
    Msg.body (fun m => m.kind = some k ∧ m.wf) (fun m => ownMsg l m (DFrac.own 1)) (ownAny l k)

/-- `(*T).New()` for kind `k`'s type `T`: a fresh zero `T`, as a `Serializable`. -/
def epaxos.New.spec (k : MsgKind) : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos }}
    (App (Val (l @!! go.GoType.PointerType k.ty @!! go!"New")) (Val #()))
  {{ (obj : GoInterface), RET #obj; ∃ l' : Loc,
      ⌜obj = interface.mkOk (go.GoType.PointerType k.ty) #l'⌝ ∗ ownAny l' k }}

/-! ## The `rpc.Serializable` dispatch -/

/-- `obj.Marshal(w)` through the interface, on a protocol message (`SendMsg`'s `msg`). -/
def Serializable.Marshal.spec : Prop :=
  ∀ (obj : GoInterface) (e : GoInterfaceOk) (m : Msg) (dq dq1 dq2 : DFrac), obj = interface.ok e →
  marshalTriple (pkgInit_epaxos (GF := GF))
    #(methods e.ty go!"Marshal" e.v) (msgObj obj m dq dq1 dq2) m.body

/-- `p.Obj.New()` through the interface, on a prototype of kind `k`. -/
def Serializable.New.spec : Prop :=
  ∀ (k : MsgKind) (obj : GoInterface) (e : GoInterfaceOk), obj = interface.ok e → protoObj k obj →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos }}
    (App (Val #(methods e.ty go!"New" e.v)) (Val #()))
  {{ (obj' : GoInterface), RET #obj'; ∃ l' : Loc,
      ⌜obj' = interface.mkOk (go.GoType.PointerType k.ty) #l'⌝ ∗ ownAny l' k }}

/-- `obj.Unmarshal(r)` through the interface, on a fresh object of kind `k`. -/
def Serializable.Unmarshal.spec : Prop :=
  ∀ (k : MsgKind) (l : Loc),
  unmarshalTriple (pkgInit_epaxos (GF := GF))
    #(methods (go.GoType.PointerType k.ty) go!"Unmarshal" #l) (ownAny l k)
    Msg.body (fun m => m.kind = some k ∧ m.wf)
    (fun m => msgObj (interface.mkOk (go.GoType.PointerType k.ty) #l) m (DFrac.own 1))
    (ownAny l k)

/-- The per-kind specs give the dispatch laws. -/
theorem Serializable_specs (hM : ∀ k, epaxos.Marshal.spec (GF := GF) k)
    (hU : ∀ k, epaxos.Unmarshal.spec (GF := GF) k)
    (hN : ∀ k, epaxos.New.spec (GF := GF) k) :
    Serializable.Marshal.spec (GF := GF) ∧ Serializable.New.spec (GF := GF) ∧
      Serializable.Unmarshal.spec (GF := GF) := by
  refine ⟨?_, ?_, ?_⟩
  · intro obj e m dq dq1 dq2 hobj bw wr sent pend err
    iintro %Φ ⟨#Hpkg, #Hpkg2, Hown, HQ, Hobj⟩ HΦ
    iunfold msgObj at Hobj
    icases Hobj with ⟨%k, %l, %Hk, Hm⟩
    obtain ⟨hk, rfl⟩ := Hk
    cases hobj
    iapply (hM k l dq dq1 dq2 m hk bw wr sent pend err) $$ [$Hpkg $Hpkg2 $Hown $HQ $Hm]
    inext
    iintro ⟨Hm, Hw⟩
    iapply HΦ
    iframe Hw
    iunfold msgObj
    iexists k, l
    iframe Hm
    ipureintro; exact ⟨hk, rfl⟩
  · intro k obj e hobj hp
    obtain ⟨l, rfl⟩ := hp
    cases hobj
    exact hN k l
  · intro k l
    intro br rd R
    iintro %Φ ⟨#Hpkg, #Hpkg2, Hown, #Hn, Hl⟩ HΦ
    iapply (hU k l br rd R) $$ [$Hpkg $Hpkg2 $Hown $Hn $Hl]
    inext
    iintro %err H
    iapply HΦ
    icases H with (⟨%he, %m, %hm, Hown, Hm⟩ | H)
    · ileft
      isplitr
      · ipureintro; exact he
      iexists m
      iframe Hown
      isplitr
      · ipureintro; exact hm
      iunfold msgObj
      iexists k, l
      iframe Hm
      ipureintro; exact ⟨hm.1, rfl⟩
    · iright; iexact H

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
