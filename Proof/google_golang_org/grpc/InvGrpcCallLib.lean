/-
**grpc's call protocol** (phase 7, S3.1; `notes/phase7-endstate.md` §1.4, the design
`plan-s3.md` §2.3-§2.4): one ghost protocol for every call, unary or stream, over which grpc's
transport, `clientStream` and `processRPC` are to be proved once (S3.2), and the connection's byte
protocols `grpcCliP`/`grpcSrvP` over frame sequences, with their parse laws. Definitions and proved
laws; no axiom, no opaque. Nothing links them yet: `grpcAddrAt` still points at the opaque
`grpcCliPI`/`grpcSrvPI` (`InvGrpcWire.lean`) until S3.2 proves `Invoke`, `NewStream` and `Serve`
over the model (W5).

**A call** (`CallParams`), fixed by its client when it opens the call: the wire parts of its two
messages, the metadata family `Md a md` an attempt to the address `a` may deliver (an `IProp`,
D6), the content `up i m` of its `i`-th request, the content `dn a md j m` of its `j`-th response
if it was dispatched to `a` at `md`, and what its end `o` carries (`fin a md o`; `o = some d`: a
handler's error description). The address index is SW1's (`streamDispIs γ a md`, `cliStreamIs`'
`Md a md` and `Dn a md`): a transparent retry may re-pick the address. `unaryParams` is a unary
call (one request carrying the deposit, one reply carrying `Φ`, a handler's error carrying `Ψe`),
`streamParams` a stream; `callAdmits ent γ a P` ties a call to a table entry.

**The call's invariant** `callInv κ P` (allocated by the client, `call_alloc`): the up queue `U` (the
client's half outside, `cliSendTok`), the server's received prefix `Ur` (`srvRecvTok`), each request
not yet received holding its content; the up end, open or closed after `U` (`upClosed`, with the
client's half then inside: a closed queue takes no more requests); the dispatch, unset or
`streamDispIs γ a md` with `□ P.Md a md`; the down queue `D` (`srvSendTok`), empty until dispatched,
and the client's received prefix `Dr` (`cliRecvTok`), each response not yet received holding its
content; the server's end, unset or `callEndIs κ n o` with `downClosed γ (D.take n)` and `P.fin a md o`
until the client takes it (`callFinTok`). A response pushed after the end stays unreceived (R3).
The laws: `call_push_up`, `call_take_up`, `call_close_up`, `call_dispatch`, `call_push_dn`,
`call_take_dn`, `call_end`, `call_end_closed`, `call_take_fin`; the dispatch's agreement is
`streamDispIs_agree` (`InvGrpcCall.lean`, SW1's form of §1.2's `streamMdIs_agree`).

**The call's names** (`CallNames`): the stream's (`StreamNames`, what users see) and two more, for the
end's status and the client's right to take it. `StreamNames` is trusted text with no name to spare,
and all ghost state at a name shares one camera (Perennial's `own`, values stored as `encodeO`), so
the status cannot live at a stream name already used for a value of another type.

**The head slot, keyed by the call** (the review of SW1, finding 3: a bridge's relay sits between
two connections, so what a call deposits must not be tied to one connection's freshness). The
call's server share for one attempt (`callDeposit ent fs κ a P`) sits in an invariant of the
attempt (`attInv α`, names `AttNames`), not in a connection's slot; the connection's slot
(`GooseLang/Ext/Net/Slot.lean`, used as it is) holds only the attempt's **ticket** (`attTicket α`),
keyed by the head and the names, `(fs, κ, α)`. Whoever holds the ticket either dispatches the
attempt (`att_claim`: the share) or refuses it (`att_refuse`: `attRefused α`, persistent); the
client takes the share back from a refused attempt (`att_takeRefused`) or, with the ticket a
withdrawal of a short head gave back, from a cancelled one (`att_cancel`). A relay claims the ticket
on its accepted connection and registers it on its dialed one (`callHead_relay`): the target then
claims or refuses the same attempt, and the facts of the frames it writes, stated over `κ` and `α`,
carry over to the first connection (`srvFrameOkAt_relay`, `grpcCliP_relay`).

**The bytes** (`InvGrpcWire.lean`'s model bytes). `grpcCliP Svc`: a prefix of the preface, or the
preface, a well-formed head `fs` that names an entry of `Svc` and opens the call `κ`
(`callHeadIs`), and frames `cliFramesOk`: a prefix of data frames carrying `upAt` facts, at most one
close (`upClosed` after them), and possibly a cancel. `grpcSrvP Svc`: a prefix of its preface, or
its preface and well-formed whole frames (`srvFrameWf`), each frame's fact stated at its position,
the number `j` of data frames before it (`srvFramesOk`): a data frame is `downAt κ j m` of an
encoding, a trailer whose status is an end (`trailerEnd`) is `callEndIs κ j o`, a `REFUSED_STREAM`
reset is `attRefused α`, for the call the connection's head opened (`callKeyOf`); a frame after a
trailer or a reset says nothing (R3). **Parse laws**: a reader of the client's bytes learns the head's
call and the facts of the frames it read (`cli_read_head`, `cli_read_data`, `cli_read_close`); a
reader of the server's bytes learns each frame's fact at its position (`srv_frames_read`,
`srvFramesOk_at`) and, on its own call's connection, the fact itself (`srvFrame_data`,
`srvFrame_trailer`, `srvFrame_reset`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

/-! ## Names and namespaces -/

/-- **A call's ghost names**: the stream's (what the call's users see), the end's status and the
client's right to take what the end carries. -/
structure CallNames where
  s : StreamNames
  fin : GName
  finTok : GName

instance CallNames.countable : Pos.Countable CallNames :=
  .ofInjective (fun κ => Pos.Countable.encode (κ.s, κ.fin, κ.finTok))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- **An attempt's ghost names**: its state, its ticket and its client's token. -/
structure AttNames where
  st : GName
  tk : GName
  cl : GName

instance AttNames.countable : Pos.Countable AttNames :=
  .ofInjective (fun α => Pos.Countable.encode (α.st, α.tk, α.cl))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- A head slot's key: the head's fields, the call's names and the attempt's. -/
abbrev CallKey : Type := List (GoString × GoString) × CallNames × AttNames

/-- The call library's namespace. -/
def grpcCallN : Namespace := nroot.@"grpccall"
/-- The invariant of the call `κ`. -/
def callN (κ : CallNames) : Namespace := (grpcCallN.@"call").@κ
/-- The invariant of the attempt `α`. -/
def attN (α : AttNames) : Namespace := (grpcCallN.@"att").@α

/-! ## Calls -/

section params
variable [GooseExts]
variable {GF : BundledGFunctors}

/-- **A wire part as a stream message type**, for the stream's tokens (which read only its model
and its `Countable` instance; the other fields are never used). -/
abbrev ProtoWire.msg (W : ProtoWire) : StreamMsg GF where
  ty := W.ty
  M := W.M
  cnt := W.cnt
  tree := W.tree
  send := fun _ _ => iprop(False)
  recv := fun _ _ => iprop(False)
  own := fun _ => iprop(False)

/-- The request's wire part of a table entry. -/
def GrpcSvcEntry.wq : GrpcSvcEntry GF → ProtoWire
  | .unary e => e.Wq
  | .stream e => e.Wq

/-- The response's wire part of a table entry. -/
def GrpcSvcEntry.wp : GrpcSvcEntry GF → ProtoWire
  | .unary e => e.Wp
  | .stream e => e.Wp

/-- **What one call carries** (see the file header). -/
structure CallParams (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  Md : GoString → GrpcMd → IProp GF
  up : Nat → Wq.M → IProp GF
  dn : GoString → GrpcMd → Nat → Wp.M → IProp GF
  fin : GoString → GrpcMd → Option GoString → IProp GF

/-- **A unary call** with the caller's spec `S`, reply content `Φ` and error content `Ψe`: one
request whose content is the deposit (`S` at every metadata an attempt may deliver, a step later,
after an update), one reply carrying `Φ`, a handler's error description carrying `Ψe`. `S` is the
caller's (the same at every address; the deposit converts it to the dispatching address's entry,
`callAdmits`). -/
def unaryParams (Wq Wp : ProtoWire) (Md : GoString → GrpcMd → IProp GF)
    (S : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF)
    (Φ : Wp.M → IProp GF) (Ψe : GoString → IProp GF) : CallParams GF where
  Wq := Wq
  Wp := Wp
  Md := Md
  up := fun i m => if i = 0 then iprop(▷ ∀ a md, Md a md -∗ |==> S md m Φ Ψe) else iprop(False)
  dn := fun _ _ j m' => if j = 0 then Φ m' else iprop(True)
  fin := fun _ _ o => match o with
    | some d => iprop(⌜d ∈ handlerDescs⌝ -∗ Ψe d)
    | none => iprop(True)

/-- **A stream** with the client's request content `up` and the response content `dn a md` at
each dispatch (its end carries nothing). -/
def streamParams (Wq Wp : ProtoWire) (Md : GoString → GrpcMd → IProp GF)
    (up : Nat → Wq.M → IProp GF) (dn : GoString → GrpcMd → Nat → Wp.M → IProp GF) :
    CallParams GF where
  Wq := Wq
  Wp := Wp
  Md := Md
  up := up
  dn := dn
  fin := fun _ _ _ => iprop(True)

/-- **The parameters an attempt to `a` of a call of the entry `ent` may have**: a unary call of
the entry's messages, or a stream of the entry's messages whose response content at `a` is the
entry's (the conversions of the contents are `callFacts`). -/
def callAdmits (ent : GrpcSvcEntry GF) (γ : StreamNames) (a : GoString) (P : CallParams GF) :
    Prop :=
  match ent with
  | .unary e => ∃ S Φ Ψe, P = unaryParams e.Wq e.Wp P.Md S Φ Ψe
  | .stream e => ∃ up dn, P = streamParams e.Wq e.Wp P.Md up dn ∧ dn a = fun md => e.dn md γ

/-- The call's request message type, for the stream's tokens. -/
abbrev CallParams.req (P : CallParams GF) : StreamMsg GF := P.Wq.msg

/-- The call's response message type, for the stream's tokens. -/
abbrev CallParams.rep (P : CallParams GF) : StreamMsg GF := P.Wp.msg

end params

/-! ## The call's ghost state -/

section call
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `j`-th response the server sent on the stream is `m` (persistent). -/
def downAt {Rep : StreamMsg GF} (γ : StreamNames) (j : Nat) (m : Rep.M) : IProp GF :=
  monoListIdxOwn γ.down j m

instance downAt_persistent {Rep : StreamMsg GF} (γ : StreamNames) (j : Nat) (m : Rep.M) :
    Persistent (downAt (GF := GF) γ j m) := by
  unfold downAt; infer_instance

/-- The server's right to dispatch the call (exclusive). -/
def callMdTok (κ : CallNames) : IProp GF :=
  dghostVar κ.s.md (DFrac.own (1 : Qp).half) (none : Option (GoString × GrpcMdCode))

/-- The server's right to end the call (exclusive). -/
def callEndTok (κ : CallNames) : IProp GF :=
  dghostVar κ.fin (DFrac.own (1 : Qp).half) (none : Option (Nat × Option GoString))

/-- The client's right to take what the call's end carries (exclusive). -/
def callFinTok (κ : CallNames) : IProp GF := token κ.finTok

/-- **The server ended the call after `n` responses, with `o`** (persistent; set once). -/
def callEndIs (κ : CallNames) (n : Nat) (o : Option GoString) : IProp GF :=
  dghostVar κ.fin DFrac.discard (some (n, o) : Option (Nat × Option GoString))

instance callEndIs_persistent (κ : CallNames) (n : Nat) (o : Option GoString) :
    Persistent (callEndIs (GF := GF) κ n o) := by
  unfold callEndIs; infer_instance

/-- The end's state, once dispatched to `a` at the code `c`: unset, or ended after `n` of the
responses `D` with `o`. -/
def callEndBody (κ : CallNames) (P : CallParams GF) (a : GoString) (c : GrpcMdCode)
    (D : List P.rep.M) : IProp GF :=
  iprop((dghostVar κ.fin (DFrac.own (1 : Qp).half) (none : Option (Nat × Option GoString)) ∗
      dghostVar κ.s.downEnd (DFrac.own 1) ([] : List P.rep.M)) ∨
    ∃ (n : Nat) (o : Option GoString), ⌜n ≤ D.length⌝ ∗ callEndIs κ n o ∗
      downClosed (Rep := P.rep) κ.s (D.take n) ∗ (P.fin a c.md o ∨ callFinTok κ))

/-- The dispatch's state: unset (no response yet), or dispatched to `a` at the code `c`, each
response not yet received holding its content. -/
def callDispBody (κ : CallNames) (P : CallParams GF) (D Dr : List P.rep.M) : IProp GF :=
  iprop((⌜D = []⌝ ∗ callMdTok κ ∗
      dghostVar κ.fin (DFrac.own (1 : Qp).half) (none : Option (Nat × Option GoString)) ∗
      dghostVar κ.s.downEnd (DFrac.own 1) ([] : List P.rep.M)) ∨
    ∃ (a : GoString) (c : GrpcMdCode),
      dghostVar κ.s.md DFrac.discard (some (a, c) : Option (GoString × GrpcMdCode)) ∗
      □ P.Md a c.md ∗
      ([∗list] k ↦ m ∈ D.drop Dr.length, P.dn a c.md (Dr.length + k) m) ∗
      callEndBody κ P a c D)

/-- The call's invariant's body (see the file header). -/
def callBody (κ : CallNames) (P : CallParams GF) : IProp GF :=
  iprop(∃ (U Ur : List P.req.M) (D Dr : List P.rep.M), ⌜Ur <+: U ∧ Dr <+: D⌝ ∗
    cliSendTok (Req := P.req) κ.s U ∗
    dghostVar κ.s.upRcv (DFrac.own (1 : Qp).half) Ur ∗
    ([∗list] k ↦ m ∈ U.drop Ur.length, P.up (Ur.length + k) m) ∗
    (dghostVar κ.s.upEnd (DFrac.own 1) ([] : List P.req.M) ∨
      cliSendTok (Req := P.req) κ.s U ∗ upClosed (Req := P.req) κ.s U) ∗
    srvSendTok (Rep := P.rep) κ.s D ∗
    dghostVar κ.s.downRcv (DFrac.own (1 : Qp).half) Dr ∗
    callDispBody κ P D Dr)

/-- **The call's invariant** (persistent). -/
def callInv (κ : CallNames) (P : CallParams GF) : IProp GF := inv (callN κ) (callBody κ P)

instance callInv_persistent (κ : CallNames) (P : CallParams GF) :
    Persistent (callInv κ P) := by
  unfold callInv; infer_instance

/-- **The server's share of a call** (exclusive): its tokens, both queues' at `[]`, the handler's
auxiliary name unset, and the rights to dispatch and to end. -/
def callSrvShare (κ : CallNames) (P : CallParams GF) : IProp GF :=
  iprop(srvRecvTok (Req := P.req) κ.s [] ∗ srvSendTok (Rep := P.rep) κ.s [] ∗
    streamAuxTok κ.s ∗ callMdTok κ ∗ callEndTok κ)

/-! ### Ghost helpers -/

section helpers
variable {A : Type} [Pos.Countable A]

theorem cl_dgv_halves (γ : GName) (a : A) :
    dghostVar (GF := GF) γ (DFrac.own 1) a ⊣⊢
      dghostVar γ (DFrac.own (1 : Qp).half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half) a := by
  have h := (dghostVar_dfractional (GF := GF) γ a).dfractional (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h

theorem cl_ml_halves (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ 1 l ⊣⊢
      monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  have h := (monoListAuthOwn_fractional (GF := GF) γ l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem cl_dgv_join (γ : GName) (a b : A) :
    dghostVar (GF := GF) γ (DFrac.own (1 : Qp).half) a ∗ dghostVar γ (DFrac.own (1 : Qp).half) b ⊢
      ⌜a = b⌝ ∗ dghostVar γ (DFrac.own 1) a := by
  have hag : dghostVar (GF := GF) γ (DFrac.own (1 : Qp).half) a ∗
      dghostVar γ (DFrac.own (1 : Qp).half) b ⊢ ⌜a = b⌝ := by
    iintro ⟨H1, H2⟩
    iapply dghostVar_agree γ a _ b _ $$ H1 H2
  refine (persistent_entails_left hag).trans ?_
  iintro ⟨⟨H1, H2⟩, %h⟩
  subst h
  isplitr
  · ipureintro; rfl
  iapply (cl_dgv_halves γ a).2
  isplitl [H1]
  · iexact H1
  · iexact H2

theorem cl_ml_join (γ : GName) (l1 l2 : List A) :
    monoListAuthOwn (GF := GF) γ (1 : Qp).half l1 ∗ monoListAuthOwn γ (1 : Qp).half l2 ⊢
      ⌜l1 = l2⌝ ∗ monoListAuthOwn γ 1 l1 := by
  have hag : monoListAuthOwn (GF := GF) γ (1 : Qp).half l1 ∗
      monoListAuthOwn γ (1 : Qp).half l2 ⊢ ⌜l1 = l2⌝ := by
    iintro ⟨H1, H2⟩
    icases monoListAuthOwn_agree γ _ _ l1 l2 $$ H1 H2 with %h
    ipureintro; exact h.2
  refine (persistent_entails_left hag).trans ?_
  iintro ⟨⟨H1, H2⟩, %h⟩
  subst h
  isplitr
  · ipureintro; rfl
  iapply (cl_ml_halves γ l1).2
  isplitl [H1]
  · iexact H1
  · iexact H2

/-- Three halves of a mono list's authority are too many. -/
theorem cl_ml_three (γ : GName) (l1 l2 l3 : List A) :
    monoListAuthOwn (GF := GF) γ (1 : Qp).half l1 ∗ monoListAuthOwn γ (1 : Qp).half l2 ∗
      monoListAuthOwn γ (1 : Qp).half l3 ⊢ False := by
  iintro ⟨H1, H2, H3⟩
  ihave ⟨%h, H12⟩ := cl_ml_join γ l1 l2 $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  icases monoListAuthOwn_agree γ _ _ l1 l3 $$ H12 H3 with %h'
  exfalso
  have h1 := h'.1
  simp only [Qp.le_iff, Qp.val_add, Qp.val_half, Qp.val_one] at h1
  grind

/-- A half of a ghost variable at `none` and a discarded one at `some` disagree. -/
theorem cl_dgv_none_some {B : Type} [Pos.Countable B] (γ : GName) (q : DFrac) (b : B) :
    dghostVar (GF := GF) γ q (none : Option B) ∗ dghostVar γ DFrac.discard (some b) ⊢ False := by
  iintro ⟨H1, H2⟩
  icases dghostVar_agree γ (none : Option B) q (some b) DFrac.discard $$ H1 H2 with %h
  cases h

/-- Set both halves of a ghost variable to `b` and discard them. -/
theorem cl_dgv_set_discard (γ : GName) (a1 a2 b : A) :
    dghostVar (GF := GF) γ (DFrac.own (1 : Qp).half) a1 ∗
      dghostVar γ (DFrac.own (1 : Qp).half) a2 ==∗
      dghostVar γ DFrac.discard b ∗ dghostVar γ DFrac.discard b := by
  iintro ⟨H1, H2⟩
  imod dghostVar_update_halves b γ a1 a2 $$ H1 H2 with ⟨H1, H2⟩
  imod dghostVar_persist γ _ b $$ H1 with H1
  imod dghostVar_persist γ _ b $$ H2 with H2
  imodintro
  isplitl [H1]
  · iexact H1
  · iexact H2

end helpers

/-! ### Pure list helpers -/

theorem cl_drop_snoc {X : Type} {l : List X} {n : Nat} (h : n ≤ l.length) (x : X) :
    (l ++ [x]).drop n = l.drop n ++ [x] :=
  List.drop_append_of_le_length h

theorem cl_drop_cons {X : Type} {l : List X} {n : Nat} {x : X} (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  have hn : n < l.length := by
    rcases Nat.lt_or_ge n l.length with hn | hn
    · exact hn
    · rw [List.getElem?_eq_none hn] at h; cases h
  rw [List.drop_eq_getElem_cons hn]
  rw [List.getElem?_eq_getElem hn] at h
  cases h; rfl

theorem cl_prefix_snoc {X : Type} {l L : List X} {x : X} (hp : l <+: L)
    (h : L[l.length]? = some x) : l ++ [x] <+: L := by
  obtain ⟨t, rfl⟩ := hp
  have : t[0]? = some x := by
    rw [List.getElem?_append_right (Nat.le_refl _)] at h
    simpa using h
  cases t with
  | nil => simp at this
  | cons y t =>
    simp at this; subst this
    exact ⟨t, by simp⟩

/-! ### The laws -/

/-- **Open a call** (its client): the call's invariant, the client's tokens, the right to take the
end's content, and the server's share (which the client deposits). -/
theorem call_alloc (E : CoPset) (P : CallParams GF) :
    ⊢ |={E}=> ∃ κ : CallNames, callInv κ P ∗ cliSendTok (Req := P.req) κ.s [] ∗
      cliRecvTok (Rep := P.rep) κ.s [] ∗ callFinTok κ ∗ callSrvShare κ P := by
  imod mono_list_own_alloc (GF := GF) ([] : List P.req.M) with ⟨%γup, Hup, #Hupl⟩
  imod dghostVar_alloc (GF := GF) ([] : List P.req.M) with ⟨%γupRcv, HupRcv⟩
  imod mono_list_own_alloc (GF := GF) ([] : List P.rep.M) with ⟨%γdown, Hdown, #Hdownl⟩
  imod dghostVar_alloc (GF := GF) ([] : List P.req.M) with ⟨%γupEnd, HupEnd⟩
  imod dghostVar_alloc (GF := GF) ([] : List P.rep.M) with ⟨%γdownRcv, HdownRcv⟩
  imod dghostVar_alloc (GF := GF) ([] : List P.rep.M) with ⟨%γdownEnd, HdownEnd⟩
  imod dghostVar_alloc (GF := GF) (none : Option (List GName)) with ⟨%γaux, Haux⟩
  imod dghostVar_alloc (GF := GF) (none : Option (GoString × GrpcMdCode)) with ⟨%γmd, Hmd⟩
  imod dghostVar_alloc (GF := GF) (none : Option (Nat × Option GoString)) with ⟨%γfin, Hfin⟩
  imod token_alloc (GF := GF) with ⟨%γft, Hft⟩
  let γ : StreamNames := ⟨γup, γupRcv, γdown, γupEnd, γdownRcv, γdownEnd, γaux, γmd⟩
  let κ : CallNames := ⟨γ, γfin, γft⟩
  icases (cl_ml_halves γup ([] : List P.req.M)).1 $$ Hup with ⟨Hup1, Hup2⟩
  icases (cl_ml_halves γdown ([] : List P.rep.M)).1 $$ Hdown with ⟨Hdown1, Hdown2⟩
  icases (cl_dgv_halves γupRcv ([] : List P.req.M)).1 $$ HupRcv with ⟨HupRcv1, HupRcv2⟩
  icases (cl_dgv_halves γdownRcv ([] : List P.rep.M)).1 $$ HdownRcv with ⟨HdownRcv1, HdownRcv2⟩
  icases (cl_dgv_halves γmd (none : Option (GoString × GrpcMdCode))).1 $$ Hmd with ⟨Hmd1, Hmd2⟩
  icases (cl_dgv_halves γfin (none : Option (Nat × Option GoString))).1 $$ Hfin with ⟨Hfin1, Hfin2⟩
  imod inv_alloc (callN κ) E (callBody κ P) $$
    [Hup1 HupRcv1 HupEnd Hdown1 HdownRcv1 Hmd1 Hfin1 HdownEnd] with #Hinv
  · inext
    unfold callBody
    iexists [], [], [], []
    isplitr
    · ipureintro; exact ⟨List.prefix_refl _, List.prefix_refl _⟩
    unfold cliSendTok srvSendTok
    iframe Hup1 HupRcv1 Hdown1 HdownRcv1
    isplitr
    · simp only [List.drop_nil]
      iapply BigSepL.bigSepL_nil.2
      itrivial
    isplitl [HupEnd]
    · ileft; iexact HupEnd
    unfold callDispBody callMdTok
    ileft
    iframe Hmd1 Hfin1 HdownEnd
    ipureintro; rfl
  imodintro
  iexists κ
  unfold callInv callFinTok callSrvShare cliSendTok cliRecvTok srvRecvTok srvSendTok streamAuxTok
    callMdTok callEndTok
  iframe Hinv Hup2 Hft Hdown2 Haux Hmd2 Hfin2
  isplitl [HdownRcv2]
  · iframe HdownRcv2 Hdownl
  · iframe HupRcv2 Hupl

/-- **Push a request** (the client, with the request's content): the up queue grows, and the
`i`-th request is `m` (`upAt`, what its data frame carries). -/
theorem call_push_up (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (U : List P.req.M) (m : P.req.M) :
    ⊢ callInv κ P -∗ cliSendTok (Req := P.req) κ.s U -∗ P.up U.length m -∗ £ 1 ={E}=∗
      cliSendTok (Req := P.req) κ.s (U ++ [m]) ∗ upAt (Req := P.req) κ.s U.length m := by
  iintro #Hi Hc Hm Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U', %Ur, %D, %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  icases Hend with (Hopen | ⟨Hu2, #Hcl⟩)
  · unfold cliSendTok
    ihave ⟨%hU, Hfull⟩ := cl_ml_join κ.s.up U U' $$ [Hc Hu]
    · isplitl [Hc]
      · iexact Hc
      · iexact Hu
    subst hU
    imod monoListAuthOwn_update_app [m] $$ Hfull with ⟨Hfull, #Hlb⟩
    icases (cl_ml_halves κ.s.up (U ++ [m])).1 $$ Hfull with ⟨Hc, Hu⟩
    ihave #Hat := monoListIdxOwn_get (γ := κ.s.up) U.length m (by simp) $$ Hlb
    have hle : Ur.length ≤ U.length := hpre.1.length_le
    imod Hclose $$ [Hu Hur Hups Hopen Hd Hdr Hdisp Hm] with -
    · inext
      unfold callBody
      iexists U ++ [m], Ur, D, Dr
      isplitr
      · ipureintro; exact ⟨hpre.1.trans (List.prefix_append _ _), hpre.2⟩
      unfold cliSendTok
      iframe Hu Hur Hd Hdr Hdisp
      isplitl [Hups Hm]
      · rw [cl_drop_snoc hle]
        iapply BigSepL.bigSepL_snoc.2
        iframe Hups
        have : Ur.length + (U.drop Ur.length).length = U.length := by
          simp only [List.length_drop]; omega
        rw [this]
        iexact Hm
      · ileft; iexact Hopen
    imodintro
    unfold upAt
    iframe Hc Hat
  · iexfalso
    unfold cliSendTok
    iapply cl_ml_three κ.s.up U U' U' $$ [Hc Hu Hu2]
    iframe Hc Hu Hu2

/-- **Receive a request** (the server, with the next position's request `m`): the request's
content. -/
theorem call_take_up (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (Ur : List P.req.M) (m : P.req.M) :
    ⊢ callInv κ P -∗ srvRecvTok (Req := P.req) κ.s Ur -∗ upAt (Req := P.req) κ.s Ur.length m -∗
      £ 1 ={E}=∗ srvRecvTok (Req := P.req) κ.s (Ur ++ [m]) ∗ P.up Ur.length m := by
  iintro #Hi Hs #Hat Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur', %D, %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  unfold srvRecvTok
  icases Hs with ⟨Hs, -⟩
  ihave ⟨%hUr, Hfull⟩ := cl_dgv_join κ.s.upRcv Ur Ur' $$ [Hs Hur]
  · isplitl [Hs]
    · iexact Hs
    · iexact Hur
  subst hUr
  unfold cliSendTok
  icases mono_list_auth_idx_lookup κ.s.up _ U Ur.length m $$ [Hu] [Hat] with %hm
  · iexact Hu
  · unfold upAt; iexact Hat
  have hpre' : Ur ++ [m] <+: U := cl_prefix_snoc hpre.1 hm
  rw [cl_drop_cons hm]
  icases BigSepL.bigSepL_cons.1 $$ Hups with ⟨Hm, Hups⟩
  imod dghostVar_update (Ur ++ [m]) κ.s.upRcv Ur $$ Hfull with Hfull
  icases (cl_dgv_halves κ.s.upRcv (Ur ++ [m])).1 $$ Hfull with ⟨Hs, Hur⟩
  ihave #HlbU := monoListLbOwn_get κ.s.up _ U $$ Hu
  ihave #Hlb := monoListLbOwn_le (γ := κ.s.up) (Ur ++ [m]) hpre' $$ HlbU
  imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hdisp] with -
  · inext
    unfold callBody
    iexists U, Ur ++ [m], D, Dr
    isplitr
    · ipureintro; exact ⟨hpre', hpre.2⟩
    unfold cliSendTok
    iframe Hu Hur Hend Hd Hdr Hdisp
    simp only [List.length_append, List.length_singleton]
    iapply (BigSepL.bigSepL_mono_of_forall (fun {k x} => by
      rw [show Ur.length + (k + 1) = Ur.length + 1 + k by omega])) $$ Hups
  imodintro
  iframe Hs Hlb
  iexact Hm

/-- The server's received requests and the client's close agree: a received prefix as long as the
closed queue is it. -/
theorem srvRecvTok_upClosed_eq {Req : StreamMsg GF} (γ : StreamNames) (Ur L : List Req.M)
    (h : Ur.length = L.length) :
    srvRecvTok (Req := Req) γ Ur ∗ upLb (Req := Req) γ L ⊢ srvRecvTok γ Ur ∗ ⌜Ur = L⌝ := by
  unfold srvRecvTok upLb
  iintro ⟨⟨Hh, #Hlb⟩, #HL⟩
  icases mono_list_lb_valid γ.up Ur L $$ Hlb HL with %hp
  iframe Hh Hlb
  ipureintro
  rcases hp with hp | hp
  · exact hp.eq_of_length h
  · exact (hp.eq_of_length h.symm).symm

/-- **Close the up queue** (the client, with its sender token, which it gives up): the queue is
closed after `U`. -/
theorem call_close_up (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (U : List P.req.M) :
    ⊢ callInv κ P -∗ cliSendTok (Req := P.req) κ.s U -∗ £ 1 ={E}=∗
      upClosed (Req := P.req) κ.s U ∗ upLb (Req := P.req) κ.s U := by
  iintro #Hi Hc Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U', %Ur, %D, %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  unfold cliSendTok
  icases Hend with (Hopen | ⟨Hu2, -⟩)
  · ihave ⟨%hU, Hfull⟩ := cl_ml_join κ.s.up U U' $$ [Hc Hu]
    · isplitl [Hc]
      · iexact Hc
      · iexact Hu
    subst hU
    icases (cl_ml_halves κ.s.up U).1 $$ Hfull with ⟨Hc, Hu⟩
    ihave #Hlb := monoListLbOwn_get κ.s.up _ U $$ Hc
    imod dghostVar_update U κ.s.upEnd ([] : List P.req.M) $$ Hopen with Hopen
    imod dghostVar_persist κ.s.upEnd 1 U $$ Hopen with #Hcl
    imod Hclose $$ [Hu Hur Hups Hc Hd Hdr Hdisp] with -
    · inext
      unfold callBody
      iexists U, Ur, D, Dr
      isplitr
      · ipureintro; exact hpre
      unfold cliSendTok upClosed
      iframe Hu Hur Hups Hd Hdr Hdisp
      iright
      iframe Hc Hcl
    imodintro
    unfold upClosed upLb
    iframe Hcl Hlb
  · iexfalso
    iapply cl_ml_three κ.s.up U U' U' $$ [Hc Hu Hu2]
    iframe Hc Hu Hu2

/-- **Dispatch the call** (the server, with its right to, at the address `a` and the metadata code
`c` it made of the head, and the metadata family's fact there): both ends' dispatch fact. -/
theorem call_dispatch (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (a : GoString) (c : GrpcMdCode) :
    ⊢ callInv κ P -∗ callMdTok κ -∗ □ P.Md a c.md -∗ £ 1 ={E}=∗ streamDispIs (GF := GF) κ.s a c.md := by
  iintro #Hi Hm #HMd Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur, %D, %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  iunfold callDispBody at Hdisp
  unfold callMdTok
  icases Hdisp with (⟨%hD, Hm', Hfin, HdE⟩ | ⟨%a', %c', #Hd', -⟩)
  · imod cl_dgv_set_discard κ.s.md _ _ (some (a, c) : Option (GoString × GrpcMdCode)) $$ [Hm Hm']
      with ⟨#H1, -⟩
    · isplitl [Hm]
      · iexact Hm
      · iexact Hm'
    subst hD
    have hDr : Dr = [] := List.prefix_nil.mp hpre.2
    subst hDr
    imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hfin HdE] with -
    · inext
      unfold callBody
      iexists U, Ur, [], []
      isplitr
      · ipureintro; exact hpre
      iframe Hu Hur Hups Hend Hd Hdr
      unfold callDispBody
      iright
      iexists a, c
      iframe H1 HMd
      isplitr
      · simp only [List.drop_nil]
        iapply BigSepL.bigSepL_nil.2
        itrivial
      unfold callEndBody
      ileft
      iframe Hfin HdE
    imodintro
    unfold streamDispIs
    iexists c
    iframe H1
    ipureintro; rfl
  · iexfalso
    iapply cl_dgv_none_some κ.s.md _ (a', c') $$ [Hm Hd']
    iframe Hm Hd'

/-- The end's state survives a push. -/
theorem callEndBody_snoc (κ : CallNames) (P : CallParams GF) (a : GoString) (c : GrpcMdCode)
    (D : List P.rep.M) (m : P.rep.M) :
    callEndBody κ P a c D ⊢ callEndBody κ P a c (D ++ [m]) := by
  unfold callEndBody
  iintro (H | ⟨%n, %o, %hn, #HE, #Hdc, Hf⟩)
  · ileft; iexact H
  · iright
    iexists n, o
    rw [List.take_append_of_le_length hn]
    iframe HE Hdc Hf
    ipureintro; simp only [List.length_append, List.length_singleton]; omega

/-- **Push a response** (the server, on the dispatched call, with the response's content at the
dispatch): the down queue grows, and the `j`-th response is `m` (`downAt`, what its data frame
carries). -/
theorem call_push_dn (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (D : List P.rep.M) (a : GoString) (md : GrpcMd) (m : P.rep.M) :
    ⊢ callInv κ P -∗ srvSendTok (Rep := P.rep) κ.s D -∗ streamDispIs (GF := GF) κ.s a md -∗
      P.dn a md D.length m -∗ £ 1 ={E}=∗
      srvSendTok (Rep := P.rep) κ.s (D ++ [m]) ∗ downAt (Rep := P.rep) κ.s D.length m := by
  iintro #Hi Hs #Hdisp0 Hm Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur, %D', %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  unfold srvSendTok
  ihave ⟨%hD, Hfull⟩ := cl_ml_join κ.s.down D D' $$ [Hs Hd]
  · isplitl [Hs]
    · iexact Hs
    · iexact Hd
  subst hD
  unfold streamDispIs
  icases Hdisp0 with ⟨%c0, %hc0, #H0⟩
  iunfold callDispBody at Hdisp
  icases Hdisp with (⟨-, Hm', -, -⟩ | ⟨%a', %c', #Hd', #HMd, Hdn, Hendb⟩)
  · iexfalso
    unfold callMdTok
    iapply cl_dgv_none_some κ.s.md _ (a, c0) $$ [Hm' H0]
    iframe Hm' H0
  icases dghostVar_agree κ.s.md (some (a, c0) : Option (GoString × GrpcMdCode)) _ (some (a', c')) _
    $$ H0 Hd' with %hag
  cases hag
  subst hc0
  imod monoListAuthOwn_update_app [m] $$ Hfull with ⟨Hfull, #Hlb⟩
  icases (cl_ml_halves κ.s.down (D ++ [m])).1 $$ Hfull with ⟨Hs, Hd⟩
  ihave #Hat := monoListIdxOwn_get (γ := κ.s.down) D.length m (by simp) $$ Hlb
  ihave Hendb := callEndBody_snoc κ P a c0 D m $$ Hendb
  have hle : Dr.length ≤ D.length := hpre.2.length_le
  imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hdn Hendb Hm] with -
  · inext
    unfold callBody
    iexists U, Ur, D ++ [m], Dr
    isplitr
    · ipureintro; exact ⟨hpre.1, hpre.2.trans (List.prefix_append _ _)⟩
    unfold srvSendTok
    iframe Hu Hur Hups Hend Hd Hdr
    unfold callDispBody
    iright
    iexists a, c0
    iframe Hd' HMd Hendb
    rw [cl_drop_snoc hle]
    iapply BigSepL.bigSepL_snoc.2
    iframe Hdn
    have : Dr.length + (D.drop Dr.length).length = D.length := by
      simp only [List.length_drop]; omega
    rw [this]
    iexact Hm
  imodintro
  unfold downAt
  iframe Hs Hat

/-- **Receive a response** (the client, with the next position's response `m`): the dispatch and
the response's content at it. -/
theorem call_take_dn (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (Dr : List P.rep.M) (m : P.rep.M) :
    ⊢ callInv κ P -∗ cliRecvTok (Rep := P.rep) κ.s Dr -∗ downAt (Rep := P.rep) κ.s Dr.length m -∗
      £ 1 ={E}=∗ cliRecvTok (Rep := P.rep) κ.s (Dr ++ [m]) ∗
        ∃ (a : GoString) (md : GrpcMd), streamDispIs (GF := GF) κ.s a md ∗ □ P.Md a md ∗
          P.dn a md Dr.length m := by
  iintro #Hi Hr #Hat Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur, %D, %Dr', %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  unfold cliRecvTok
  icases Hr with ⟨Hr, -⟩
  ihave ⟨%hDr, Hfull⟩ := cl_dgv_join κ.s.downRcv Dr Dr' $$ [Hr Hdr]
  · isplitl [Hr]
    · iexact Hr
    · iexact Hdr
  subst hDr
  unfold srvSendTok
  icases mono_list_auth_idx_lookup κ.s.down _ D Dr.length m $$ [Hd] [Hat] with %hm
  · iexact Hd
  · unfold downAt; iexact Hat
  have hpre' : Dr ++ [m] <+: D := cl_prefix_snoc hpre.2 hm
  iunfold callDispBody at Hdisp
  icases Hdisp with (⟨%hD, -, -, -⟩ | ⟨%a, %c, #Hd', #HMd, Hdn, Hendb⟩)
  · subst hD; simp at hm
  rw [cl_drop_cons hm]
  icases BigSepL.bigSepL_cons.1 $$ Hdn with ⟨Hm, Hdn⟩
  imod dghostVar_update (Dr ++ [m]) κ.s.downRcv Dr $$ Hfull with Hfull
  icases (cl_dgv_halves κ.s.downRcv (Dr ++ [m])).1 $$ Hfull with ⟨Hr, Hdr⟩
  ihave #HlbD := monoListLbOwn_get κ.s.down _ D $$ Hd
  ihave #Hlb := monoListLbOwn_le (γ := κ.s.down) (Dr ++ [m]) hpre' $$ HlbD
  imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hdn Hendb] with -
  · inext
    unfold callBody
    iexists U, Ur, D, Dr ++ [m]
    isplitr
    · ipureintro; exact ⟨hpre.1, hpre'⟩
    unfold srvSendTok
    iframe Hu Hur Hups Hend Hd Hdr
    unfold callDispBody
    iright
    iexists a, c
    iframe Hd' HMd Hendb
    simp only [List.length_append, List.length_singleton]
    iapply (BigSepL.bigSepL_mono_of_forall (fun {k x} => by
      rw [show Dr.length + (k + 1) = Dr.length + 1 + k by omega])) $$ Hdn
  imodintro
  iframe Hr Hlb
  iexists a, c.md
  iframe HMd
  isplitr
  · unfold streamDispIs
    iexists c
    iframe Hd'
    ipureintro; rfl
  · iexact Hm

/-- **End the call** (the server, with its right to, after `n` of its responses `D`, with the end's
content at the dispatch): the end, persistent. Pushes after the end are allowed (R3). -/
theorem call_end (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (D : List P.rep.M) (n : Nat) (hn : n ≤ D.length) (o : Option GoString) (a : GoString)
    (md : GrpcMd) :
    ⊢ callInv κ P -∗ callEndTok κ -∗ srvSendTok (Rep := P.rep) κ.s D -∗
      streamDispIs (GF := GF) κ.s a md -∗ P.fin a md o -∗ £ 1 ={E}=∗
      srvSendTok (Rep := P.rep) κ.s D ∗ callEndIs κ n o := by
  iintro #Hi He Hs #Hdisp0 Hf Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur, %D', %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  unfold srvSendTok
  ihave ⟨%hD, Hfull⟩ := cl_ml_join κ.s.down D D' $$ [Hs Hd]
  · isplitl [Hs]
    · iexact Hs
    · iexact Hd
  subst hD
  icases (cl_ml_halves κ.s.down D).1 $$ Hfull with ⟨Hs, Hd⟩
  unfold streamDispIs
  icases Hdisp0 with ⟨%c0, %hc0, #H0⟩
  iunfold callDispBody at Hdisp
  icases Hdisp with (⟨-, Hm', -, -⟩ | ⟨%a', %c', #Hd', #HMd, Hdn, Hendb⟩)
  · iexfalso
    unfold callMdTok
    iapply cl_dgv_none_some κ.s.md _ (a, c0) $$ [Hm' H0]
    iframe Hm' H0
  icases dghostVar_agree κ.s.md (some (a, c0) : Option (GoString × GrpcMdCode)) _ (some (a', c')) _
    $$ H0 Hd' with %hag
  cases hag
  subst hc0
  iunfold callEndBody at Hendb
  unfold callEndTok
  icases Hendb with (⟨Hfin, HdE⟩ | ⟨%n', %o', -, #HE', -⟩)
  · imod cl_dgv_set_discard κ.fin _ _ (some (n, o) : Option (Nat × Option GoString)) $$ [He Hfin]
      with ⟨#HE, -⟩
    · isplitl [He]
      · iexact He
      · iexact Hfin
    imod dghostVar_update (D.take n) κ.s.downEnd ([] : List P.rep.M) $$ HdE with HdE
    imod dghostVar_persist κ.s.downEnd 1 (D.take n) $$ HdE with #Hdc
    imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hdn Hf] with -
    · inext
      unfold callBody
      iexists U, Ur, D, Dr
      isplitr
      · ipureintro; exact hpre
      unfold srvSendTok
      iframe Hu Hur Hups Hend Hd Hdr
      unfold callDispBody
      iright
      iexists a, c0
      iframe Hd' HMd Hdn
      unfold callEndBody
      iright
      iexists n, o
      unfold callEndIs downClosed
      iframe HE Hdc
      isplitr
      · ipureintro; exact hn
      ileft; iexact Hf
    imodintro
    unfold callEndIs
    iframe Hs HE
  · iexfalso
    unfold callEndIs
    iapply cl_dgv_none_some κ.fin _ (n', o') $$ [He HE']
    iframe He HE'

/-- **The end closes the down queue** (the client, having received the `n` responses before the
end): the server's handler returned after them (`downClosed`). -/
theorem call_end_closed (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (Dr : List P.rep.M) (n : Nat) (hn : Dr.length = n) (o : Option GoString) :
    ⊢ callInv κ P -∗ callEndIs κ n o -∗ cliRecvTok (Rep := P.rep) κ.s Dr -∗ £ 1 ={E}=∗
      cliRecvTok (Rep := P.rep) κ.s Dr ∗ downClosed (Rep := P.rep) κ.s Dr := by
  iintro #Hi #HE Hr Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur, %D, %Dr', %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  unfold cliRecvTok
  icases Hr with ⟨Hr, #HrLb⟩
  ihave ⟨%hDr, Hfull⟩ := cl_dgv_join κ.s.downRcv Dr Dr' $$ [Hr Hdr]
  · isplitl [Hr]
    · iexact Hr
    · iexact Hdr
  subst hDr
  icases (cl_dgv_halves κ.s.downRcv Dr).1 $$ Hfull with ⟨Hr, Hdr⟩
  iunfold callDispBody at Hdisp
  unfold callEndIs
  icases Hdisp with (⟨%hD, Hm', Hfin, HdE⟩ | ⟨%a, %c, #Hd', #HMd, Hdn, Hendb⟩)
  · iexfalso
    iapply cl_dgv_none_some κ.fin _ (n, o) $$ [Hfin HE]
    iframe Hfin HE
  iunfold callEndBody at Hendb
  icases Hendb with (⟨Hfin, HdE⟩ | ⟨%n', %o', %hn', #HE', #Hdc, Hf⟩)
  · iexfalso
    iapply cl_dgv_none_some κ.fin _ (n, o) $$ [Hfin HE]
    iframe Hfin HE
  unfold callEndIs
  icases dghostVar_agree κ.fin (some (n, o) : Option (Nat × Option GoString)) _ (some (n', o')) _
    $$ HE HE' with %hag
  cases hag
  subst hn
  have hDt : D.take Dr.length = Dr := (List.prefix_iff_eq_take.mp hpre.2).symm
  imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hdn Hf] with -
  · inext
    unfold callBody
    iexists U, Ur, D, Dr
    isplitr
    · ipureintro; exact hpre
    iframe Hu Hur Hups Hend Hd Hdr
    unfold callDispBody
    iright
    iexists a, c
    iframe Hd' HMd Hdn
    unfold callEndBody
    iright
    iexists Dr.length, o
    unfold callEndIs
    iframe HE Hdc Hf
    ipureintro; exact hn'
  imodintro
  isplitl [Hr]
  · iframe Hr HrLb
  · have hdc : downClosed (GF := GF) (Rep := P.rep) κ.s (D.take Dr.length) =
        downClosed κ.s Dr := by rw [hDt]
    rw [← hdc]
    iexact Hdc

/-- **Take what the end carries** (the client, with its right to, once): the dispatch and the end's
content at it. -/
theorem call_take_fin (E : CoPset) (κ : CallNames) (P : CallParams GF) (hE : ↑(callN κ) ⊆ E)
    (n : Nat) (o : Option GoString) :
    ⊢ callInv κ P -∗ callFinTok κ -∗ callEndIs κ n o -∗ £ 1 ={E}=∗
      ∃ (a : GoString) (md : GrpcMd), streamDispIs (GF := GF) κ.s a md ∗ □ P.Md a md ∗
        P.fin a md o := by
  iintro #Hi Ht #HE Hlc
  unfold callInv
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(callN κ)) (P := callBody κ P)) $$ Hlc Hb with Hb
  iunfold callBody at Hb
  icases Hb with ⟨%U, %Ur, %D, %Dr, %hpre, Hu, Hur, Hups, Hend, Hd, Hdr, Hdisp⟩
  iunfold callDispBody at Hdisp
  unfold callEndIs
  icases Hdisp with (⟨%hD, Hm', Hfin, HdE⟩ | ⟨%a, %c, #Hd', #HMd, Hdn, Hendb⟩)
  · iexfalso
    iapply cl_dgv_none_some κ.fin _ (n, o) $$ [Hfin HE]
    iframe Hfin HE
  iunfold callEndBody at Hendb
  icases Hendb with (⟨Hfin, HdE⟩ | ⟨%n', %o', %hn', #HE', #Hdc, (Hf | Ht')⟩)
  · iexfalso
    iapply cl_dgv_none_some κ.fin _ (n, o) $$ [Hfin HE]
    iframe Hfin HE
  · unfold callEndIs
    icases dghostVar_agree κ.fin (some (n, o) : Option (Nat × Option GoString)) _ (some (n', o')) _
      $$ HE HE' with %hag
    cases hag
    imod Hclose $$ [Hu Hur Hups Hend Hd Hdr Hdn Ht] with -
    · inext
      unfold callBody
      iexists U, Ur, D, Dr
      isplitr
      · ipureintro; exact hpre
      iframe Hu Hur Hups Hend Hd Hdr
      unfold callDispBody
      iright
      iexists a, c
      iframe Hd' HMd Hdn
      unfold callEndBody
      iright
      iexists n, o
      unfold callEndIs
      iframe HE Hdc
      isplitr
      · ipureintro; exact hn'
      iright; iexact Ht
    imodintro
    iexists a, c.md
    iframe HMd Hf
    unfold streamDispIs
    iexists c
    iframe Hd'
    ipureintro; rfl
  · iexfalso
    unfold callFinTok
    iapply token_exclusive $$ Ht Ht'

/-! ## The attempt: the call's deposit, keyed by the call -/

/-- **An attempt's ticket** (exclusive): the right to dispatch or refuse it. -/
def attTicket (α : AttNames) : IProp GF := token α.tk

/-- **An attempt's client token** (exclusive): the right to take the deposit back. -/
def attCliTok (α : AttNames) : IProp GF := token α.cl

/-- **The attempt `α` was refused** (persistent): it is never dispatched. -/
def attRefused (α : AttNames) : IProp GF := monoListLbOwn (A := Bool) α.st [false]

instance attRefused_persistent (α : AttNames) : Persistent (attRefused (GF := GF) α) := by
  unfold attRefused; infer_instance

/-- An attempt's states: open (the deposit here, the ticket outside); dispatched; refused (the
deposit here until the client takes it); cancelled (by the client, with the ticket). -/
def attBody (α : AttNames) (D : IProp GF) : IProp GF :=
  iprop((D ∗ monoListAuthOwn (A := Bool) α.st 1 []) ∨
    (token α.tk ∗ monoListAuthOwn (A := Bool) α.st 1 [true]) ∨
    (token α.tk ∗ monoListAuthOwn (A := Bool) α.st 1 [false] ∗ (D ∨ token α.cl)) ∨
    (token α.tk ∗ token α.cl ∗ monoListAuthOwn (A := Bool) α.st 1 []))

/-- **The attempt's invariant** (persistent). -/
def attInv (α : AttNames) (D : IProp GF) : IProp GF := inv (attN α) (attBody α D)

instance attInv_persistent (α : AttNames) (D : IProp GF) : Persistent (attInv α D) := by
  unfold attInv; infer_instance

theorem att_alloc (E : CoPset) (D : IProp GF) :
    ⊢ D ={E}=∗ ∃ α : AttNames, attInv α D ∗ attTicket α ∗ attCliTok α := by
  iintro HD
  imod mono_list_own_alloc (GF := GF) ([] : List Bool) with ⟨%γst, Hst, -⟩
  imod token_alloc (GF := GF) with ⟨%γtk, Htk⟩
  imod token_alloc (GF := GF) with ⟨%γcl, Hcl⟩
  let α : AttNames := ⟨γst, γtk, γcl⟩
  imod inv_alloc (attN α) E (attBody α D) $$ [HD Hst] with #Hinv
  · inext
    unfold attBody
    ileft
    iframe HD Hst
  imodintro
  iexists α
  unfold attInv attTicket attCliTok
  iframe Hinv Htk Hcl

/-- **Dispatch an attempt** (the ticket's holder): the deposit. -/
theorem att_claim (E : CoPset) (α : AttNames) (D : IProp GF) (hE : ↑(attN α) ⊆ E) :
    ⊢ attInv α D -∗ attTicket α -∗ £ 1 ={E}=∗ D := by
  iintro #Hi Ht Hlc
  unfold attInv attTicket
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(attN α)) (P := attBody α D)) $$ Hlc Hb with Hb
  iunfold attBody at Hb
  icases Hb with (⟨HD, Hst⟩ | ⟨Ht', -⟩ | ⟨Ht', -⟩ | ⟨Ht', -⟩)
  · imod monoListAuthOwn_update [true] List.nil_prefix $$ Hst with ⟨Hst, -⟩
    imod Hclose $$ [Ht Hst] with -
    · inext
      unfold attBody
      iright; ileft
      iframe Ht Hst
    imodintro
    iexact HD
  all_goals (iexfalso; iapply token_exclusive $$ Ht Ht')

/-- **Refuse an attempt** (the ticket's holder): it is never dispatched. -/
theorem att_refuse (E : CoPset) (α : AttNames) (D : IProp GF) (hE : ↑(attN α) ⊆ E) :
    ⊢ attInv α D -∗ attTicket α -∗ £ 1 ={E}=∗ attRefused α := by
  iintro #Hi Ht Hlc
  unfold attInv attTicket
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(attN α)) (P := attBody α D)) $$ Hlc Hb with Hb
  iunfold attBody at Hb
  icases Hb with (⟨HD, Hst⟩ | ⟨Ht', -⟩ | ⟨Ht', -⟩ | ⟨Ht', -⟩)
  · imod monoListAuthOwn_update [false] List.nil_prefix $$ Hst with ⟨Hst, #Hlb⟩
    imod Hclose $$ [Ht Hst HD] with -
    · inext
      unfold attBody
      iright; iright; ileft
      iframe Ht Hst
      ileft; iexact HD
    imodintro
    unfold attRefused
    iexact Hlb
  all_goals (iexfalso; iapply token_exclusive $$ Ht Ht')

/-- **Take the deposit back from a refused attempt** (its client, once). -/
theorem att_takeRefused (E : CoPset) (α : AttNames) (D : IProp GF) (hE : ↑(attN α) ⊆ E) :
    ⊢ attInv α D -∗ attCliTok α -∗ attRefused α -∗ £ 1 ={E}=∗ D := by
  iintro #Hi Hc #Hr Hlc
  unfold attInv attCliTok attRefused
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(attN α)) (P := attBody α D)) $$ Hlc Hb with Hb
  iunfold attBody at Hb
  icases Hb with (⟨-, Hst⟩ | ⟨-, Hst⟩ | ⟨Ht, Hst, (HD | Hc')⟩ | ⟨-, Hc', -⟩)
  · icases mono_list_auth_lb_valid α.st _ _ _ $$ Hst Hr with %h
    exfalso; exact absurd (List.prefix_nil.mp h.2) (by simp)
  · icases mono_list_auth_lb_valid α.st _ _ _ $$ Hst Hr with %h
    exfalso; simp at h
  · imod Hclose $$ [Ht Hst Hc] with -
    · inext
      unfold attBody
      iright; iright; ileft
      iframe Ht Hst
      iright; iexact Hc
    imodintro
    iexact HD
  · iexfalso; iapply token_exclusive $$ Hc Hc'
  · iexfalso; iapply token_exclusive $$ Hc Hc'

/-- **Cancel an attempt** (its client, with the ticket a withdrawal gave back): the deposit. -/
theorem att_cancel (E : CoPset) (α : AttNames) (D : IProp GF) (hE : ↑(attN α) ⊆ E) :
    ⊢ attInv α D -∗ attCliTok α -∗ attTicket α -∗ £ 1 ={E}=∗ D := by
  iintro #Hi Hc Ht Hlc
  unfold attInv attCliTok attTicket
  iinv Hi with Hb Hclose
  imod (lc_fupd_elim_later (GF := GF) (E := E \ ↑(attN α)) (P := attBody α D)) $$ Hlc Hb with Hb
  iunfold attBody at Hb
  icases Hb with (⟨HD, Hst⟩ | ⟨Ht', -⟩ | ⟨Ht', -⟩ | ⟨Ht', -⟩)
  · imod Hclose $$ [Ht Hc Hst] with -
    · inext
      unfold attBody
      iright; iright; iright
      iframe Ht Hc Hst
    imodintro
    iexact HD
  all_goals (iexfalso; iapply token_exclusive $$ Ht Ht')

end call

/-! ## The head slot and the connection's protocols -/

/-- **The client wrote its whole head** after the preface: after this the server may claim. -/
def headReady (fs : List (GoString × GoString)) (W : List w8) : Prop :=
  clientPrefaceBytes ++ headFrame fs <+: W

theorem headReady_ready (fs : List (GoString × GoString)) : SlotReady (headReady fs) where
  mono _ _ ha hab := List.IsPrefix.trans ha hab

/-- **The end a trailer's fields state**: `none` for status `0`; a handler's description for a
`grpc-message` whose decoding is one (`handlerDescs`); otherwise none. -/
def trailerEnd (fs : List (GoString × GoString)) : Option (Option GoString) :=
  if fieldLast fs go!"grpc-status" = some go!"0" then some none
  else match fieldLast fs go!"grpc-message" with
    | some v => if grpcMsgDecode v ∈ handlerDescs then some (some (grpcMsgDecode v)) else none
    | none => none

/-- **A server frame the model writes is well formed**: its header lists within the limit (F1), a
message below `2 ^ 32` bytes, a code that fits its `uint32`, an oversized marker of a header or
trailer block. -/
def srvFrameWf : SrvFrame → Prop
  | .header fs => headerListOk fs
  | .data bs => bs.length < 2 ^ 32
  | .trailer fs => headerListOk fs
  | .reset c => c < 2 ^ 32
  | .oversized k => k = frameHeader ∨ k = frameTrailer

/-- Where the next frame's fact is stated after a frame at `j`: after a data frame, `j + 1`; after
a trailer or a reset, nowhere (frames after the end say nothing, R3). -/
def srvFrameStep : SrvFrame → Nat → Option Nat
  | .data _, j => some (j + 1)
  | .header _, j => some j
  | .oversized _, j => some j
  | .trailer _, _ => none
  | .reset _, _ => none

/-- The position after the frames `F` from `j` (`none` past a trailer or a reset). -/
def srvFramesPos : Nat → List SrvFrame → Option Nat
  | j, [] => some j
  | j, f :: F => (srvFrameStep f j).bind fun j' => srvFramesPos j' F

/-! ### Parsing the frames -/

/-- A data frame followed by anything, a prefix of another followed by anything, is that frame. -/
theorem dataFrame_append_prefix {a b r r' : List w8} (ha : a.length < 2 ^ 32)
    (hb : b.length < 2 ^ 32) (h : dataFrame a ++ r <+: dataFrame b ++ r') : a = b ∧ r <+: r' := by
  obtain ⟨z, hz⟩ := h
  simp only [dataFrame, grpcMsgHdr, List.cons_append, List.cons.injEq, _root_.true_and,
    List.append_assoc] at hz
  obtain ⟨hl, hz⟩ := be32_append_inj ha hb hz
  have hab := (List.append_inj hz hl).1
  subst hab
  exact ⟨rfl, ⟨z, List.append_cancel_left hz⟩⟩

/-- A data frame is no prefix of what a client writes after its data frames. -/
theorem dataFrame_ne_ctl (a y c x : List w8) (hc : c = [] ∨ c = closeFrame)
    (hx : x = [] ∨ x = cancelFrame) : ¬ (dataFrame a ++ y <+: c ++ x) := by
  intro h
  rcases hc with rfl | rfl <;> rcases hx with rfl | rfl <;>
    simp (config := { decide := true }) [dataFrame, closeFrame, cancelFrame, frameData, frameClose,
      frameCancel] at h

/-- **The data frames a reader read are a prefix of the writer's.** -/
theorem dataFrames_prefix : ∀ (A B : List (List w8)) (c x : List w8),
    (∀ bs ∈ A, bs.length < 2 ^ 32) → (∀ bs ∈ B, bs.length < 2 ^ 32) →
    (c = [] ∨ c = closeFrame) → (x = [] ∨ x = cancelFrame) →
    (A.map dataFrame).flatten <+: (B.map dataFrame).flatten ++ c ++ x → A <+: B
  | [], _, _, _, _, _, _, _, _ => List.nil_prefix
  | a :: A, [], c, x, _, _, hc, hx, h => by
    exfalso
    simp only [List.map_cons, List.flatten_cons, List.map_nil, List.flatten_nil,
      List.nil_append] at h
    exact dataFrame_ne_ctl a _ c x hc hx h
  | a :: A, b :: B, c, x, hA, hB, hc, hx, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := dataFrame_append_prefix (hA a (by simp)) (hB b (by simp)) h
    rw [← List.append_assoc] at h'
    exact (List.prefix_cons_inj a).2 (dataFrames_prefix A B c x
      (fun bs hm => hA bs (by simp [hm])) (fun bs hm => hB bs (by simp [hm])) hc hx h')

set_option linter.unusedSimpArgs false in
/-- **A close a reader read follows all of the writer's data frames.** -/
theorem dataFrames_close : ∀ (A B : List (List w8)) (c x : List w8),
    (∀ bs ∈ A, bs.length < 2 ^ 32) → (∀ bs ∈ B, bs.length < 2 ^ 32) →
    (c = [] ∨ c = closeFrame) → (x = [] ∨ x = cancelFrame) →
    (A.map dataFrame).flatten ++ closeFrame <+: (B.map dataFrame).flatten ++ c ++ x →
    A = B ∧ c = closeFrame
  | [], [], c, x, _, _, hc, hx, h => by
    simp only [List.map_nil, List.flatten_nil, List.nil_append] at h
    rcases hc with rfl | rfl <;> rcases hx with rfl | rfl <;>
      simp (config := { decide := true }) [closeFrame, cancelFrame, frameClose, frameCancel] at h ⊢
  | [], b :: B, c, x, _, _, _, _, h => by
    exfalso
    simp (config := { decide := true }) [dataFrame, closeFrame, frameData, frameClose] at h
  | a :: A, [], c, x, _, _, hc, hx, h => by
    exfalso
    simp only [List.map_cons, List.flatten_cons, List.map_nil, List.flatten_nil,
      List.nil_append, List.append_assoc] at h
    exact dataFrame_ne_ctl a _ c x hc hx h
  | a :: A, b :: B, c, x, hA, hB, hc, hx, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := dataFrame_append_prefix (hA a (by simp)) (hB b (by simp)) h
    rw [← List.append_assoc (List.map dataFrame B).flatten] at h'
    obtain ⟨h1, h2⟩ := dataFrames_close A B c x (fun bs hm => hA bs (by simp [hm]))
      (fun bs hm => hB bs (by simp [hm])) hc hx h'
    exact ⟨by rw [h1], h2⟩

/-- A server frame's kind byte. -/
def srvFrameKind : SrvFrame → w8
  | .header _ => frameHeader
  | .data _ => frameData
  | .trailer _ => frameTrailer
  | .reset _ => frameReset
  | .oversized k => k

theorem srvFrameBytes_cons (f : SrvFrame) :
    srvFrameBytes f = srvFrameKind f :: (srvFrameBytes f).tail := by
  cases f <;> rfl

/-- A header list within the limit has a block length within it. -/
theorem headerBlock_len_le {fs : List (GoString × GoString)} (h : headerListOk fs) :
    4 + (fs.map fun f => 8 + f.1.length + f.2.length).sum ≤ maxHeaderBlock := by
  unfold headerListOk at h
  have h24 : ∀ l : List (GoString × GoString),
      (l.map fun f => 8 + f.1.length + f.2.length).sum + 24 * l.length =
        (l.map fun f => 32 + f.1.length + f.2.length).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  have := h24 fs
  cases fs with
  | nil => simp [maxHeaderBlock]
  | cons a l => simp only [List.length_cons] at this; omega

theorem maxHeaderBlock_succ_lt : maxHeaderBlock + 1 < 2 ^ 32 := by
  unfold maxHeaderBlock; decide

/-- A header block within the limit is no oversized marker of its kind. -/
theorem headerBlock_ne_oversized {k : w8} {fs : List (GoString × GoString)} (h : headerListOk fs)
    {r r' : List w8} :
    ¬ (headerBlock k fs ++ r <+: (k :: be32 (maxHeaderBlock + 1)) ++ r') ∧
      ¬ ((k :: be32 (maxHeaderBlock + 1)) ++ r <+: headerBlock k fs ++ r') := by
  have hl := headerBlock_len_le h
  have hlt : 4 + (fs.map fun f => 8 + f.1.length + f.2.length).sum < 2 ^ 32 := by
    have := maxHeaderBlock_succ_lt; omega
  constructor
  · rintro ⟨z, hz⟩
    simp only [headerBlock, List.cons_append, List.cons.injEq, _root_.true_and, List.append_assoc] at hz
    have := (be32_append_inj hlt maxHeaderBlock_succ_lt hz).1
    omega
  · rintro ⟨z, hz⟩
    simp only [headerBlock, List.cons_append, List.cons.injEq, _root_.true_and, List.append_assoc] at hz
    have := (be32_append_inj maxHeaderBlock_succ_lt hlt hz).1
    omega

theorem headerBlock_append_prefix {k : w8} {fs fs' : List (GoString × GoString)} {r r' : List w8}
    (h : headerListOk fs) (h' : headerListOk fs')
    (hp : headerBlock k fs ++ r <+: headerBlock k fs' ++ r') : fs = fs' ∧ r <+: r' := by
  obtain ⟨z, hz⟩ := hp
  rw [List.append_assoc] at hz
  obtain ⟨rfl, h2⟩ := headerBlock_append_inj (headOk_of_listOk h) (headOk_of_listOk h') hz
  exact ⟨rfl, ⟨z, h2⟩⟩

/-- **A well-formed server frame is determined by its bytes.** -/
theorem srvFrame_append_prefix (f g : SrvFrame) (hf : srvFrameWf f) (hg : srvFrameWf g)
    {r r' : List w8} (h : srvFrameBytes f ++ r <+: srvFrameBytes g ++ r') : f = g ∧ r <+: r' := by
  have hk : srvFrameKind f = srvFrameKind g := by
    have h' := h
    rw [srvFrameBytes_cons f, srvFrameBytes_cons g] at h'
    simp only [List.cons_append, List.cons_prefix_cons] at h'
    exact h'.1
  cases f with
  | header fs =>
    cases g with
    | header fs' =>
      obtain ⟨rfl, h2⟩ := headerBlock_append_prefix hf hg h
      exact ⟨rfl, h2⟩
    | oversized k =>
      simp only [srvFrameKind] at hk
      subst hk
      exact absurd h (headerBlock_ne_oversized hf).1
    | _ => simp only [srvFrameKind] at hk; exact absurd hk (by decide)
  | trailer fs =>
    cases g with
    | trailer fs' =>
      obtain ⟨rfl, h2⟩ := headerBlock_append_prefix hf hg h
      exact ⟨rfl, h2⟩
    | oversized k =>
      simp only [srvFrameKind] at hk
      subst hk
      exact absurd h (headerBlock_ne_oversized hf).1
    | _ => simp only [srvFrameKind] at hk; exact absurd hk (by decide)
  | data bs =>
    cases g with
    | data bs' =>
      obtain ⟨rfl, h2⟩ := dataFrame_append_prefix hf hg h
      exact ⟨rfl, h2⟩
    | oversized k =>
      simp only [srvFrameKind, srvFrameWf] at hk hg
      rcases hg with rfl | rfl <;> exact absurd hk (by decide)
    | _ => simp only [srvFrameKind] at hk; exact absurd hk (by decide)
  | reset c =>
    cases g with
    | reset c' =>
      obtain ⟨z, hz⟩ := h
      simp only [srvFrameBytes, List.cons_append, List.cons.injEq, _root_.true_and,
        List.append_assoc] at hz
      obtain ⟨rfl, hz⟩ := be32_append_inj hf hg hz
      exact ⟨rfl, ⟨z, List.append_cancel_left hz⟩⟩
    | oversized k =>
      simp only [srvFrameKind, srvFrameWf] at hk hg
      rcases hg with rfl | rfl <;> exact absurd hk (by decide)
    | _ => simp only [srvFrameKind] at hk; exact absurd hk (by decide)
  | oversized k =>
    simp only [srvFrameWf] at hf
    cases g with
    | oversized k' =>
      simp only [srvFrameKind] at hk
      subst hk
      obtain ⟨z, hz⟩ := h
      simp only [srvFrameBytes, List.cons_append, List.cons.injEq, _root_.true_and,
        List.append_assoc, List.append_cancel_left_eq] at hz
      exact ⟨rfl, ⟨z, by simpa using hz⟩⟩
    | header fs' =>
      simp only [srvFrameKind] at hk
      subst hk
      exact absurd h (headerBlock_ne_oversized hg).2
    | trailer fs' =>
      simp only [srvFrameKind] at hk
      subst hk
      exact absurd h (headerBlock_ne_oversized hg).2
    | _ =>
      simp only [srvFrameKind] at hk
      rcases hf with rfl | rfl <;> exact absurd hk (by decide)

/-- **The well-formed frames a reader read are a prefix of the writer's.** -/
theorem srvFrames_prefix : ∀ (F G : List SrvFrame), (∀ f ∈ F, srvFrameWf f) →
    (∀ g ∈ G, srvFrameWf g) → (F.map srvFrameBytes).flatten <+: (G.map srvFrameBytes).flatten →
    F <+: G
  | [], _, _, _, _ => List.nil_prefix
  | f :: F, [], _, _, h => by
    exfalso
    simp only [List.map_cons, List.flatten_cons, List.map_nil, List.flatten_nil,
      List.prefix_nil] at h
    rw [srvFrameBytes_cons f] at h
    simp at h
  | f :: F, g :: G, hF, hG, h => by
    simp only [List.map_cons, List.flatten_cons] at h
    obtain ⟨rfl, h'⟩ := srvFrame_append_prefix f g (hF f (by simp)) (hG g (by simp)) h
    exact (List.prefix_cons_inj f).2 (srvFrames_prefix F G (fun x hx => hF x (by simp [hx]))
      (fun x hx => hG x (by simp [hx])) h')

section head
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [HasExt netExt] [π : NetProtoGS] [σs : NetSlotGS]

/-- **What the deposit's server learns of its call, per kind** (`callAdmits`, with the
conversions): for a unary call, the caller's spec converts to the entry's; for a stream, the
client's request content converts to the entry's, and the entry's specification holds at every
attempt metadata. -/
def callFacts (ent : GrpcSvcEntry GF) (κ : CallNames) (a : GoString) (P : CallParams GF) :
    IProp GF :=
  match ent with
  | .unary e => iprop(∃ (S : GrpcMd → e.Wq.M → (e.Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF)
        (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF),
      ⌜P = unaryParams e.Wq e.Wp P.Md S Φ Ψe⌝ ∗
      □ (∀ md m Φ' Ψe', S md m Φ' Ψe' ==∗ e.spec md m Φ' Ψe'))
  | .stream e => iprop(∃ (up : Nat → e.Wq.M → IProp GF)
        (dn : GoString → GrpcMd → Nat → e.Wp.M → IProp GF),
      ⌜P = streamParams e.Wq e.Wp P.Md up dn ∧ dn a = fun md => e.dn md κ.s⌝ ∗
      (□ ∀ i m, up i m ==∗ e.up i m) ∗ (□ ∀ md, P.Md a md -∗ e.spec md κ.s (e.dn md κ.s)))

theorem callFacts_admits (ent : GrpcSvcEntry GF) (κ : CallNames) (a : GoString)
    (P : CallParams GF) : callFacts ent κ a P ⊢ ⌜callAdmits ent κ.s a P⌝ := by
  cases ent with
  | unary e =>
    unfold callFacts callAdmits
    iintro ⟨%S, %Φ, %Ψe, %h, -⟩
    ipureintro; exact ⟨S, Φ, Ψe, h⟩
  | stream e =>
    unfold callFacts callAdmits
    iintro ⟨%up, %dn, %h, -⟩
    ipureintro; exact ⟨up, dn, h⟩

/-- **What the server claims when it dispatches an attempt to `a` of the call `κ` with the head
`fs`** (exclusive): its share of the call, the call's invariant, the metadata family's fact at
every metadata it may make of the head, and the kind's facts. -/
def callDeposit (ent : GrpcSvcEntry GF) (fs : List (GoString × GoString)) (κ : CallNames)
    (a : GoString) (P : CallParams GF) : IProp GF :=
  iprop(callSrvShare κ P ∗ callInv κ P ∗ (□ ∀ md, ⌜grpcFieldsMd fs md⌝ -∗ □ P.Md a md) ∗
    callFacts ent κ a P)

/-- **The client's head `fs` on `cn` opens the call `κ` of the entry `ent`** (persistent): the head
names `ent`, and the connection's slot, keyed by the head and the names and claimable once the
whole head was written, holds the ticket of an attempt whose invariant holds the deposit. -/
def callHeadIs (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString)) (κ : CallNames)
    (ent : GrpcSvcEntry GF) : IProp GF :=
  iprop(∃ (name : GoString) (sl : SlotNames) (α : AttNames) (a : GoString) (P : CallParams GF),
    ⌜pathOf fs = some name ∧ Svc name = some ent⌝ ∗
    depSlotOf (Gg := hG.goose_globalGS) cn sl ((fs, κ, α) : CallKey) ∗
    depSlotInv (Gg := hG.goose_globalGS) cn sl (headReady fs) (attTicket α)
      (fun _ : Unit => iprop(True)) ∗
    attInv α (callDeposit ent fs κ a P))

instance callHeadIs_persistent Svc cn fs κ ent :
    Persistent (callHeadIs (GF := GF) Svc cn fs κ ent) := by
  unfold callHeadIs; infer_instance

/-- **The connection `cn` carries the attempt `α` of the call `κ`, whose head `fs` names `ent`**
(persistent): what a frame's fact is stated over. -/
def callKeyOf (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString)) (κ : CallNames)
    (α : AttNames) (ent : GrpcSvcEntry GF) : IProp GF :=
  iprop((∃ sl : SlotNames, depSlotOf (Gg := hG.goose_globalGS) cn sl ((fs, κ, α) : CallKey)) ∗
    ⌜∃ name, pathOf fs = some name ∧ Svc name = some ent⌝)

instance callKeyOf_persistent Svc cn fs κ α ent :
    Persistent (callKeyOf (GF := GF) Svc cn fs κ α ent) := by
  unfold callKeyOf; infer_instance

/-- A connection carries one attempt of one call. -/
theorem callKeyOf_agree (Svc : GrpcSvc GF) (cn : Nat) (fs fs' : List (GoString × GoString))
    (κ κ' : CallNames) (α α' : AttNames) (ent ent' : GrpcSvcEntry GF) :
    callKeyOf Svc cn fs κ α ent ∗ callKeyOf Svc cn fs' κ' α' ent' ⊢
      ⌜fs = fs' ∧ κ = κ' ∧ α = α' ∧ ent = ent'⌝ := by
  unfold callKeyOf
  iintro ⟨⟨⟨%sl, #H1⟩, %h1⟩, ⟨%sl', #H2⟩, %h2⟩
  icases depSlotOf_agree (Gg := hG.goose_globalGS) cn sl sl' ((fs, κ, α) : CallKey)
    ((fs', κ', α') : CallKey) $$ H1 H2 with %h
  ipureintro
  obtain ⟨-, hk⟩ := h
  simp only [Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  obtain ⟨n1, hp1, hs1⟩ := h1
  obtain ⟨n2, hp2, hs2⟩ := h2
  rw [hp1] at hp2
  cases hp2
  rw [hs1] at hs2
  cases hs2
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem callHeadIs_key (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (ent : GrpcSvcEntry GF) :
    callHeadIs Svc cn fs κ ent ⊢ ∃ α, callKeyOf Svc cn fs κ α ent := by
  unfold callHeadIs callKeyOf
  iintro ⟨%name, %sl, %α, %a, %P, %h, #Hs, -⟩
  iexists α
  isplitl
  · iexists sl; iexact Hs
  · ipureintro; exact ⟨name, h⟩

/-- A connection's heads open one call. -/
theorem callHeadIs_agree (Svc : GrpcSvc GF) (cn : Nat) (fs fs' : List (GoString × GoString))
    (κ κ' : CallNames) (ent ent' : GrpcSvcEntry GF) :
    callHeadIs Svc cn fs κ ent ∗ callHeadIs Svc cn fs' κ' ent' ⊢ ⌜fs = fs' ∧ κ = κ' ∧ ent = ent'⌝ := by
  iintro ⟨H1, H2⟩
  icases callHeadIs_key Svc cn fs κ ent $$ H1 with ⟨%α, #K1⟩
  icases callHeadIs_key Svc cn fs' κ' ent' $$ H2 with ⟨%α', #K2⟩
  icases callKeyOf_agree Svc cn fs fs' κ κ' α α' ent ent' $$ [K1 K2] with %h
  · iframe K1 K2
  ipureintro
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-! ### The head slot's laws -/

/-- **Open an attempt on a connection** (its dialer, with the fresh token its `Dial` gave and the
deposit, before it writes the head): the head's fact, the slot, its token and the attempt's. -/
theorem callHead_open (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (Svc : GrpcSvc GF) (cn : Nat)
    (fs : List (GoString × GoString)) (κ : CallNames) (ent : GrpcSvcEntry GF) (a : GoString)
    (P : CallParams GF) (name : GoString) (h : pathOf fs = some name ∧ Svc name = some ent) :
    ⊢ depSlotsCtx (Gg := hG.goose_globalGS) -∗ connFresh (Gg := hG.goose_globalGS) cn false -∗
      callDeposit ent fs κ a P ={E}=∗ ∃ (sl : SlotNames) (α : AttNames),
        callHeadIs Svc cn fs κ ent ∗ callKeyOf Svc cn fs κ α ent ∗
        depSlotInv (Gg := hG.goose_globalGS) cn sl (headReady fs) (attTicket α)
          (fun _ : Unit => iprop(True)) ∗
        token sl.t ∗ attInv α (callDeposit ent fs κ a P) ∗ attCliTok α := by
  iintro #Hctx Hf HD
  imod att_alloc E (callDeposit ent fs κ a P) $$ HD with ⟨%α, #Ha, Ht, Hc⟩
  imod depSlot_register (Gg := hG.goose_globalGS) E hE cn ((fs, κ, α) : CallKey) (headReady fs)
    (attTicket α) (fun _ : Unit => iprop(True)) $$ Hctx Hf Ht with ⟨%sl, #Hs, #Hi, Hst⟩
  imodintro
  iexists sl, α
  iframe Hi Ha Hst Hc
  isplitl []
  · unfold callHeadIs
    iexists name, sl, α, a, P
    iframe Hs Hi Ha
    ipureintro; exact h
  · unfold callKeyOf
    isplitl
    · iexists sl; iexact Hs
    · ipureintro; exact ⟨name, h⟩

/-- **Withdraw an attempt whose head was written short** (its dialer, with the slot's token and its
`sendTok` frozen at a `W` that is no whole head, which it gives up): the deposit. -/
theorem callHead_withdraw (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (cn : Nat)
    (fs : List (GoString × GoString)) (sl : SlotNames) (α : AttNames) (D : IProp GF)
    (hA : ↑(attN α) ⊆ E) (Pc : Net.Proto GF) (W : List w8) (hW : ¬ headReady fs W) :
    ⊢ depSlotInv (Gg := hG.goose_globalGS) cn sl (headReady fs) (attTicket α)
        (fun _ : Unit => iprop(True)) -∗ token sl.t -∗
      sendTok (Gg := hG.goose_globalGS) cn false Pc W -∗ attInv α D -∗ attCliTok α -∗ £ 1 -∗ £ 1
      ={E}=∗ D := by
  iintro #Hs Ht Hw #Ha Hc Hl1 Hl2
  imod depSlot_withdraw (Gg := hG.goose_globalGS) E hE cn sl (headReady_ready fs) Pc W hW
    (attTicket α) (fun _ : Unit => iprop(True)) $$ Hs Ht Hw Hl1 with Htk
  iapply att_cancel E α D hA $$ Ha Hc Htk Hl2

/-- **Claim the attempt a connection's head opens** (its acceptor, with its fresh token, once the
whole head was written): the attempt's key, its invariant and its ticket. -/
theorem callHead_claim (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (Svc : GrpcSvc GF) (cn : Nat)
    (fs : List (GoString × GoString)) (κ : CallNames) (ent : GrpcSvcEntry GF) (W : List w8)
    (hW : headReady fs W) :
    ⊢ depSlotsCtx (Gg := hG.goose_globalGS) -∗ callHeadIs Svc cn fs κ ent -∗
      connFresh (Gg := hG.goose_globalGS) cn true -∗ sentLb (Gg := hG.goose_globalGS) cn false W -∗
      £ 1 ={E}=∗ ∃ (α : AttNames) (a : GoString) (P : CallParams GF),
        callKeyOf Svc cn fs κ α ent ∗ attInv α (callDeposit ent fs κ a P) ∗ attTicket α := by
  iintro #Hctx #Hh Hf #Hlb Hlc
  unfold callHeadIs
  icases Hh with ⟨%name, %sl, %α, %a, %P, %h, #Hs, #Hi, #Ha⟩
  imod depSlot_claim (Gg := hG.goose_globalGS) (O := Unit) E hE cn sl (headReady_ready fs) W hW
    (attTicket α) (fun _ : Unit => iprop(True)) $$ Hctx Hi Hf Hlb Hlc with ⟨Ht, -⟩
  imodintro
  iexists α, a, P
  iframe Ha Ht
  unfold callKeyOf
  isplitl
  · iexists sl; iexact Hs
  · ipureintro; exact ⟨name, h⟩

/-- **Relay a call** (a byte relay, the acceptor of `cn0` and the dialer of `cn1`, once the whole
head was written on `cn0`): the same attempt is opened on `cn1`, and both connections carry it. -/
theorem callHead_relay (E : CoPset) (hE : (↑netSlotN : CoPset) ⊆ E) (Svc : GrpcSvc GF)
    (cn0 cn1 : Nat) (fs : List (GoString × GoString)) (κ : CallNames) (ent : GrpcSvcEntry GF)
    (W : List w8) (hW : headReady fs W) :
    ⊢ depSlotsCtx (Gg := hG.goose_globalGS) -∗ callHeadIs Svc cn0 fs κ ent -∗
      connFresh (Gg := hG.goose_globalGS) cn0 true -∗ sentLb (Gg := hG.goose_globalGS) cn0 false W -∗
      connFresh (Gg := hG.goose_globalGS) cn1 false -∗ £ 1 ={E}=∗
      ∃ (α : AttNames) (sl1 : SlotNames), callHeadIs Svc cn1 fs κ ent ∗
        callKeyOf Svc cn0 fs κ α ent ∗ callKeyOf Svc cn1 fs κ α ent ∗
        depSlotInv (Gg := hG.goose_globalGS) cn1 sl1 (headReady fs) (attTicket α)
          (fun _ : Unit => iprop(True)) ∗ token sl1.t := by
  iintro #Hctx #Hh Hf0 #Hlb Hf1 Hlc
  unfold callHeadIs
  icases Hh with ⟨%name, %sl, %α, %a, %P, %h, #Hs, #Hi, #Ha⟩
  imod depSlot_claim (Gg := hG.goose_globalGS) (O := Unit) E hE cn0 sl (headReady_ready fs) W hW
    (attTicket α) (fun _ : Unit => iprop(True)) $$ Hctx Hi Hf0 Hlb Hlc with ⟨Ht, -⟩
  imod depSlot_register (Gg := hG.goose_globalGS) E hE cn1 ((fs, κ, α) : CallKey) (headReady fs)
    (attTicket α) (fun _ : Unit => iprop(True)) $$ Hctx Hf1 Ht with ⟨%sl1, #Hs1, #Hi1, Hst⟩
  imodintro
  iexists α, sl1
  isplitl []
  · iexists name, sl1, α, a, P
    isplitl []
    · ipureintro; exact h
    iframe Hs1 Hi1 Ha
  unfold callKeyOf
  isplitl []
  · isplitl
    · iexists sl; iexact Hs
    · ipureintro; exact ⟨name, h⟩
  isplitl []
  · isplitl
    · iexists sl1; iexact Hs1
    · ipureintro; exact ⟨name, h⟩
  iframe Hi1 Hst

/-! ### The client's bytes -/

/-- **The frames a client writes after its head on the call `γ`** (persistent): a prefix of data
frames, each a message of the up queue at its position, at most one close after them (the queue
closed after as many requests), and possibly a cancel. -/
def cliFramesOk (γ : StreamNames) (Wq : ProtoWire) (rest : List w8) : IProp GF :=
  iprop(□ ∃ (ds : List (List w8)) (c x : List w8),
    ⌜rest <+: (ds.map dataFrame).flatten ++ c ++ x ∧ (∀ bs ∈ ds, bs.length < 2 ^ 32) ∧
      (x = [] ∨ x = cancelFrame)⌝ ∗
    (□ [∗list] i ↦ bs ∈ ds, ∃ m : Wq.M, upAt (Req := ProtoWire.msg (GF := GF) Wq) γ i m ∗
      ⌜protoEncodes Wq.ty (Wq.tree m) bs⌝) ∗
    (⌜c = []⌝ ∨ ⌜c = closeFrame⌝ ∗ ∃ L : List Wq.M,
      upClosed (Req := ProtoWire.msg (GF := GF) Wq) γ L ∗
      upLb (Req := ProtoWire.msg (GF := GF) Wq) γ L ∗ ⌜L.length = ds.length⌝))

instance cliFramesOk_persistent γ Wq rest : Persistent (cliFramesOk (GF := GF) γ Wq rest) := by
  unfold cliFramesOk; infer_instance

/-- **What a client writes** on a connection to an address serving `Svc`: a prefix of the preface,
or the preface, a well-formed head that opens a call of an entry of `Svc`, and the call's frames. -/
def grpcCliP (Svc : GrpcSvc GF) : Net.Proto GF := fun cn W =>
  iprop(⌜W <+: clientPrefaceBytes⌝ ∨
    ∃ (fs : List (GoString × GoString)) (κ : CallNames) (ent : GrpcSvcEntry GF) (rest : List w8),
      ⌜W = clientPrefaceBytes ++ headFrame fs ++ rest ∧ headOk fs⌝ ∗
      callHeadIs Svc cn fs κ ent ∗ cliFramesOk κ.s ent.wq rest)

instance grpcCliP_persistent Svc cn W : Persistent (grpcCliP (GF := GF) Svc cn W) := by
  unfold grpcCliP; infer_instance

/-! ### The server's bytes -/

/-- **What a server frame at the position `j` says** (`j` data frames before it; see the file
header). -/
def srvFrameOkAt (Svc : GrpcSvc GF) (cn j : Nat) : SrvFrame → IProp GF
  | .data bs => iprop(□ ∃ (fs : List (GoString × GoString)) (κ : CallNames) (α : AttNames)
      (ent : GrpcSvcEntry GF) (m : ent.wp.M), callKeyOf Svc cn fs κ α ent ∗
      downAt (Rep := ProtoWire.msg (GF := GF) ent.wp) κ.s j m ∗
      ⌜protoEncodes ent.wp.ty (ent.wp.tree m) bs⌝)
  | .trailer fs' => iprop(□ ∀ o, ⌜trailerEnd fs' = some o⌝ -∗
      ∃ (fs : List (GoString × GoString)) (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF),
        callKeyOf Svc cn fs κ α ent ∗ callEndIs κ j o)
  | .reset c => iprop(□ (⌜c = errCodeRefusedStream⌝ -∗
      ∃ (fs : List (GoString × GoString)) (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF),
        callKeyOf Svc cn fs κ α ent ∗ attRefused α))
  | .header _ => iprop(True)
  | .oversized _ => iprop(True)

instance srvFrameOkAt_persistent Svc cn j f : Persistent (srvFrameOkAt (GF := GF) Svc cn j f) := by
  cases f <;> dsimp only [srvFrameOkAt] <;> infer_instance

/-- **The facts of a server's frames from the position `j`** (persistent): each frame's, at its
position, up to the first trailer or reset. -/
def srvFramesOk (Svc : GrpcSvc GF) (cn : Nat) : Nat → List SrvFrame → IProp GF
  | _, [] => iprop(True)
  | j, f :: F => iprop(□ (srvFrameOkAt Svc cn j f ∗
      match srvFrameStep f j with
      | some j' => srvFramesOk Svc cn j' F
      | none => iprop(True)))

instance srvFramesOk_persistent Svc cn j F : Persistent (srvFramesOk (GF := GF) Svc cn j F) := by
  cases F <;> dsimp only [srvFramesOk] <;> infer_instance

/-- **What a server writes** on a connection to an address serving `Svc`: a prefix of its preface,
or its preface and well-formed whole frames, with their facts. -/
def grpcSrvP (Svc : GrpcSvc GF) : Net.Proto GF := fun cn W =>
  iprop(⌜W <+: settingsBytes⌝ ∨
    ∃ F : List SrvFrame, ⌜W = settingsBytes ++ (F.map srvFrameBytes).flatten ∧
      ∀ f ∈ F, srvFrameWf f⌝ ∗ srvFramesOk Svc cn 0 F)

instance grpcSrvP_persistent Svc cn W : Persistent (grpcSrvP (GF := GF) Svc cn W) := by
  unfold grpcSrvP; infer_instance

/-! ### The protocols' laws -/

/-- A client that wrote nothing but its preface and a head meets its protocol. -/
theorem grpcCliP_head (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (ent : GrpcSvcEntry GF) (hok : headOk fs) :
    callHeadIs Svc cn fs κ ent ⊢ grpcCliP Svc cn (clientPrefaceBytes ++ headFrame fs) := by
  unfold grpcCliP cliFramesOk
  iintro #H
  iright
  iexists fs, κ, ent, []
  isplitr
  · ipureintro; exact ⟨by simp, hok⟩
  iframe H
  imodintro
  iexists [], [], []
  isplitr
  · ipureintro; exact ⟨by simp, by simp, Or.inl rfl⟩
  isplitr
  · imodintro
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ileft; ipureintro; rfl

/-- A server that wrote its preface meets its protocol. -/
theorem grpcSrvP_preface (Svc : GrpcSvc GF) (cn : Nat) : ⊢ grpcSrvP Svc cn settingsBytes := by
  unfold grpcSrvP
  ileft; ipureintro; exact List.prefix_refl _

theorem cl_ctl_cases (c : List w8) (X : IProp GF) :
    iprop(⌜c = []⌝ ∨ ⌜c = closeFrame⌝ ∗ X) ⊢ ⌜c = [] ∨ c = closeFrame⌝ := by
  iintro (%h | ⟨%h, -⟩)
  · ipureintro; exact .inl h
  · ipureintro; exact .inr h

/-- **What a server read of its client's bytes, a whole head and more**: the head's call, and the
client's frames after it, of which what it read is a prefix. -/
theorem cli_read_core (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (Y : List w8) (hok : headOk fs) :
    protoPrefix (grpcCliP Svc) cn (clientPrefaceBytes ++ headFrame fs ++ Y) ⊢
      ∃ (κ : CallNames) (ent : GrpcSvcEntry GF) (rest : List w8),
        callHeadIs Svc cn fs κ ent ∗ cliFramesOk κ.s ent.wq rest ∗ ⌜Y <+: rest⌝ := by
  unfold protoPrefix
  iintro (%h0 | ⟨%ext, %hext, #HP⟩)
  · exfalso
    simp [headFrame, headerBlock] at h0
  unfold grpcCliP
  icases HP with (%hpre | ⟨%fs0, %κ, %ent, %rest, ⟨%hW, %hok0⟩, #Hh, #Hf⟩)
  · exfalso
    have h1 := (hext.trans hpre).length_le
    simp only [List.length_append, headFrame, headerBlock, List.length_cons] at h1
    omega
  subst hW
  have hh : clientPrefaceBytes ++ headFrame fs <+: clientPrefaceBytes ++ headFrame fs0 ++ rest :=
    (List.prefix_append _ _).trans hext
  obtain rfl := head_prefix_inj hok hok0 hh
  have hY : Y <+: rest := (List.prefix_append_right_inj _).1 hext
  iexists κ, ent, rest
  iframe Hh Hf
  ipureintro; exact hY

/-- **The server reads a head** (whole): the call it opens. -/
theorem cli_read_head (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (hok : headOk fs) :
    protoPrefix (grpcCliP Svc) cn (clientPrefaceBytes ++ headFrame fs) ⊢
      ∃ (κ : CallNames) (ent : GrpcSvcEntry GF), callHeadIs Svc cn fs κ ent := by
  iintro #H
  rw [← List.append_nil (clientPrefaceBytes ++ headFrame fs)]
  icases cli_read_core Svc cn fs [] hok $$ H with ⟨%κ, %ent, %rest, #Hh, -, -⟩
  iexists κ, ent
  iexact Hh

/-- **The server reads data frames after a head**: the call, and each frame's request at its
position. -/
theorem cli_read_data (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (A : List (List w8)) (hok : headOk fs) (hA : ∀ bs ∈ A, bs.length < 2 ^ 32) :
    protoPrefix (grpcCliP Svc) cn (clientPrefaceBytes ++ headFrame fs ++ (A.map dataFrame).flatten) ⊢
      ∃ (κ : CallNames) (ent : GrpcSvcEntry GF), callHeadIs Svc cn fs κ ent ∗
        [∗list] i ↦ bs ∈ A, ∃ m : ent.wq.M, upAt (Req := ProtoWire.msg (GF := GF) ent.wq) κ.s i m ∗
          ⌜protoEncodes ent.wq.ty (ent.wq.tree m) bs⌝ := by
  iintro #H
  icases cli_read_core Svc cn fs _ hok $$ H with ⟨%κ, %ent, %rest, #Hh, #Hf, %hY⟩
  unfold cliFramesOk
  icases Hf with ⟨%ds, %c, %x, ⟨%hr, %hds, %hx⟩, #Hds, #Hc⟩
  ihave %hc := cl_ctl_cases c _ $$ Hc
  obtain ⟨H, rfl⟩ := dataFrames_prefix A ds c x hA hds hc hx (hY.trans hr)
  iexists κ, ent
  iframe Hh
  icases BigSepL.bigSepL_append.1 $$ Hds with ⟨HA, -⟩
  iexact HA

/-- **The server reads a close after data frames**: the call, and its up queue closed after as
many requests. -/
theorem cli_read_close (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (A : List (List w8)) (hok : headOk fs) (hA : ∀ bs ∈ A, bs.length < 2 ^ 32) :
    protoPrefix (grpcCliP Svc) cn
        (clientPrefaceBytes ++ headFrame fs ++ ((A.map dataFrame).flatten ++ closeFrame)) ⊢
      ∃ (κ : CallNames) (ent : GrpcSvcEntry GF), callHeadIs Svc cn fs κ ent ∗
        ∃ L : List ent.wq.M, upClosed (Req := ProtoWire.msg (GF := GF) ent.wq) κ.s L ∗
          upLb (Req := ProtoWire.msg (GF := GF) ent.wq) κ.s L ∗ ⌜L.length = A.length⌝ := by
  iintro #H
  icases cli_read_core Svc cn fs _ hok $$ H with ⟨%κ, %ent, %rest, #Hh, #Hf, %hY⟩
  unfold cliFramesOk
  icases Hf with ⟨%ds, %c, %x, ⟨%hr, %hds, %hx⟩, -, #Hc⟩
  ihave %hc := cl_ctl_cases c _ $$ Hc
  obtain ⟨rfl, hcc⟩ := dataFrames_close A ds c x hA hds hc hx (hY.trans hr)
  icases Hc with (%hc0 | ⟨-, %L, #Hcl, #Hlb, %hL⟩)
  · exfalso; rw [hc0] at hcc; simp [closeFrame] at hcc
  iexists κ, ent
  iframe Hh
  iexists L
  iframe Hcl Hlb
  ipureintro; exact hL

theorem srvFramesOk_prefix (Svc : GrpcSvc GF) (cn : Nat) :
    ∀ (j : Nat) (F G : List SrvFrame), srvFramesOk Svc cn j (F ++ G) ⊢ srvFramesOk Svc cn j F := by
  intro j F
  induction F generalizing j with
  | nil =>
    intro G
    simp only [srvFramesOk]
    iintro -
    itrivial
  | cons f F ih =>
    intro G
    simp only [List.cons_append, srvFramesOk]
    rcases hs : srvFrameStep f j with _ | j'
    · iintro #H
      iexact H
    · iintro #⟨H1, H2⟩
      imodintro
      iframe H1
      iapply ih j' G $$ H2

/-- **A frame's fact at its position**, from the facts of the frames before and after it. -/
theorem srvFramesOk_at (Svc : GrpcSvc GF) (cn : Nat) :
    ∀ (j : Nat) (F : List SrvFrame) (f : SrvFrame) (G : List SrvFrame) (j' : Nat),
      srvFramesPos j F = some j' →
      srvFramesOk Svc cn j (F ++ f :: G) ⊢ srvFrameOkAt Svc cn j' f := by
  intro j F
  induction F generalizing j with
  | nil =>
    intro f G j' h
    simp only [srvFramesPos, Option.some.injEq] at h
    subst h
    simp only [List.nil_append, srvFramesOk]
    iintro #⟨H, -⟩
    iexact H
  | cons g F ih =>
    intro f G j' h
    simp only [srvFramesPos] at h
    rcases hs : srvFrameStep g j with _ | j1
    · simp [hs] at h
    · simp only [hs, Option.bind_some] at h
      simp only [List.cons_append, srvFramesOk, hs]
      iintro #⟨-, H2⟩
      iapply ih j1 f G j' h $$ H2

/-- **The client reads the server's frames** (whole, well formed): each frame's fact at its
position. -/
theorem srv_frames_read (Svc : GrpcSvc GF) (cn : Nat) (F : List SrvFrame)
    (hF : ∀ f ∈ F, srvFrameWf f) :
    protoPrefix (grpcSrvP Svc) cn (settingsBytes ++ (F.map srvFrameBytes).flatten) ⊢
      srvFramesOk Svc cn 0 F := by
  unfold protoPrefix
  iintro (%h0 | ⟨%ext, %hext, #HP⟩)
  · exfalso; simp [settingsBytes] at h0
  unfold grpcSrvP
  icases HP with (%hpre | ⟨%G, ⟨%hW, %hG⟩, #HG⟩)
  · have hl := (hext.trans hpre).length_le
    cases F with
    | nil =>
      simp only [srvFramesOk]
      itrivial
    | cons f F =>
      exfalso
      simp only [settingsBytes, List.length_append, List.map_cons, List.flatten_cons,
        List.length_singleton] at hl
      rw [srvFrameBytes_cons f] at hl
      simp only [List.length_cons] at hl
      omega
  subst hW
  have hp := (List.prefix_append_right_inj _).1 hext
  obtain ⟨H, rfl⟩ := srvFrames_prefix F G hF hG hp
  iapply srvFramesOk_prefix Svc cn 0 F H $$ HG

/-- **A data frame on the client's own call's connection**: the response at its position. -/
theorem srvFrame_data (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF) (j : Nat) (bs : List w8) :
    callKeyOf Svc cn fs κ α ent ∗ srvFrameOkAt Svc cn j (.data bs) ⊢
      ∃ m : ent.wp.M, downAt (Rep := ProtoWire.msg (GF := GF) ent.wp) κ.s j m ∗
        ⌜protoEncodes ent.wp.ty (ent.wp.tree m) bs⌝ := by
  simp only [srvFrameOkAt]
  iintro ⟨#Hk, #Hf⟩
  icases Hf with ⟨%fs', %κ', %α', %ent', %m, #Hk', #Hd, %he⟩
  icases callKeyOf_agree Svc cn fs fs' κ κ' α α' ent ent' $$ [Hk Hk'] with %h
  · iframe Hk Hk'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  iexists m
  iframe Hd
  ipureintro; exact he

/-- **A trailer on the client's own call's connection**: the call's end, at the trailer's position. -/
theorem srvFrame_trailer (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF) (j : Nat)
    (fs' : List (GoString × GoString)) (o : Option GoString) (ho : trailerEnd fs' = some o) :
    callKeyOf Svc cn fs κ α ent ∗ srvFrameOkAt Svc cn j (.trailer fs') ⊢ callEndIs κ j o := by
  simp only [srvFrameOkAt]
  iintro ⟨#Hk, #Hf⟩
  ihave Hx := Hf $$ %o
  ihave Hy := Hx $$ []
  · ipureintro; exact ho
  icases Hy with ⟨%fs1, %κ1, %α1, %ent1, #Hk1, #HE⟩
  icases callKeyOf_agree Svc cn fs fs1 κ κ1 α α1 ent ent1 $$ [Hk Hk1] with %h
  · iframe Hk Hk1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  iexact HE

/-- **A `REFUSED_STREAM` reset on the client's own call's connection**: its attempt was refused. -/
theorem srvFrame_reset (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF) (j : Nat) :
    callKeyOf Svc cn fs κ α ent ∗ srvFrameOkAt Svc cn j (.reset errCodeRefusedStream) ⊢
      attRefused α := by
  simp only [srvFrameOkAt]
  iintro ⟨#Hk, #Hf⟩
  ihave Hy := Hf $$ []
  · ipureintro; trivial
  icases Hy with ⟨%fs1, %κ1, %α1, %ent1, #Hk1, #HR⟩
  icases callKeyOf_agree Svc cn fs fs1 κ κ1 α α1 ent ent1 $$ [Hk Hk1] with %h
  · iframe Hk Hk1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  iexact HR

/-- **A relay carries a server frame's fact** from its dialed connection `cn1` to its accepted
connection `cn0`, both carrying the attempt (`callHead_relay`). -/
theorem srvFrameOkAt_relay (Svc : GrpcSvc GF) (cn0 cn1 : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF) (j : Nat) (f : SrvFrame) :
    callKeyOf Svc cn1 fs κ α ent ∗ callKeyOf Svc cn0 fs κ α ent ∗ srvFrameOkAt Svc cn1 j f ⊢
      srvFrameOkAt Svc cn0 j f := by
  cases f with
  | data bs =>
    simp only [srvFrameOkAt]
    iintro ⟨#K1, #K0, #Hf⟩
    icases Hf with ⟨%fs', %κ', %α', %ent', %m, #Hk', #Hd, %he⟩
    icases callKeyOf_agree Svc cn1 fs fs' κ κ' α α' ent ent' $$ [K1 Hk'] with %h
    · iframe K1 Hk'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    imodintro
    iexists fs, κ, α, ent, m
    iframe K0 Hd
    ipureintro; exact he
  | trailer fs' =>
    simp only [srvFrameOkAt]
    iintro ⟨#K1, #K0, #Hf⟩
    imodintro
    iintro %o %ho
    ihave Hx := Hf $$ %o
    ihave Hy := Hx $$ []
    · ipureintro; exact ho
    icases Hy with ⟨%fs1, %κ1, %α1, %ent1, #Hk1, #HE⟩
    icases callKeyOf_agree Svc cn1 fs fs1 κ κ1 α α1 ent ent1 $$ [K1 Hk1] with %h
    · iframe K1 Hk1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    iexists fs, κ, α, ent
    iframe K0 HE
  | reset c =>
    simp only [srvFrameOkAt]
    iintro ⟨#K1, #K0, #Hf⟩
    imodintro
    iintro %hc
    ihave Hy := Hf $$ []
    · ipureintro; exact hc
    icases Hy with ⟨%fs1, %κ1, %α1, %ent1, #Hk1, #HR⟩
    icases callKeyOf_agree Svc cn1 fs fs1 κ κ1 α α1 ent ent1 $$ [K1 Hk1] with %h
    · iframe K1 Hk1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    iexists fs, κ, α, ent
    iframe K0 HR
  | header _ =>
    simp only [srvFrameOkAt]
    iintro -
    itrivial
  | oversized _ =>
    simp only [srvFrameOkAt]
    iintro -
    itrivial

/-- **A relay's dialed connection meets the client's protocol** for what the client wrote on its
accepted one. -/
theorem grpcCliP_relay (Svc : GrpcSvc GF) (cn0 cn1 : Nat) (fs : List (GoString × GoString))
    (κ : CallNames) (α : AttNames) (ent : GrpcSvcEntry GF) (W : List w8) :
    callHeadIs Svc cn1 fs κ ent ∗ callKeyOf Svc cn0 fs κ α ent ∗ grpcCliP Svc cn0 W ⊢
      grpcCliP Svc cn1 W := by
  unfold grpcCliP
  iintro ⟨#H1, #K0, (%hp | ⟨%fs', %κ', %ent', %rest, %hW, #Hh, #Hf⟩)⟩
  · ileft; ipureintro; exact hp
  icases callHeadIs_key Svc cn0 fs' κ' ent' $$ Hh with ⟨%α', #K'⟩
  icases callKeyOf_agree Svc cn0 fs fs' κ κ' α α' ent ent' $$ [K0 K'] with %h
  · iframe K0 K'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  iright
  iexists fs, κ, ent, rest
  iframe H1 Hf
  ipureintro; exact hW

end head

end EtcdGrove
end Perennial
