/-
kvnet's wire protocol (`notes/kvnet-protocol.md`, decision E): what the bytes on a replica's address
mean, as a per-address protocol of the net extension's library (`GooseLang/Ext/Net/Proto.lean`):
`kvP F id` what dialers write to the replica `id`'s address, `kvQ F id` what it writes back, over an
abstract record of persistent facts `F : KvFacts GF` (the store's and raft's predicates are its
instance, after decision B). Nothing exclusive crosses the wire.

* A dialer's stream is a prefix of a full one (`kvFull`): `helloPeerB` then whole frames of
  `putMsg`'s bytes, each with its message's fact (`framesOk`), or `helloClientB` then one request
  frame `putB (reqBytes kind tmo pl)` whose payload has its fact (`reqOk`).
* An acceptor's stream is nothing, `putB [0]` (no answer), or one reply frame `putB (1 :: v)` with
  the answer's fact (`ansOk`) for the request the dialer wrote on the same connection (`sentLb`).

The laws: `kvP_closed` (prefix-closed); `client_reply` (a client that wrote exactly its request and
read a reply frame has the answer's fact: the reply names a request frame, which is a prefix of the
client's own write, and frames are prefix-free, `putB_prefix_inj`); `server_request` (an acceptor
that read a request frame has its fact and the `sentLb` the reply needs), `server_reply`,
`server_noans`; `server_peer` (a peer frame read after whole frames is a message's encoding with its
fact), `peer_send`; and the glue to the byte-level specs: `kv_connRes` (a dialer's `connEnd` gives
`RequestVia`'s `connRes`), `kv_dial` (the dial update `Request`/`RequestWithin` take, from the
address's protocol).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Client
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Wire
public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

/-- The first byte of a peer's connection (`helloPeer`, `'P'`). -/
def helloPeerB : w8 := W8 80

/-- The request kinds (`ReqPropose`, `ReqRead`, `ReqConf`, `ReqDisrupt`, `ReqStatus`). -/
def reqProposeB : w8 := W8 1
def reqReadB : w8 := W8 2
def reqConfB : w8 := W8 3
def reqDisruptB : w8 := W8 4
def reqStatusB : w8 := W8 5

/-! ## Frames are prefix-free -/

/-- A frame read after whole frames, within a stream of whole frames, is the next one: the bytes of
`putB x ++ r` and of `putB y ++ s` agree as far as the first goes. -/
theorem putB_cons_prefix {x y r s : List w8} (hx : x.length < 2 ^ 64) (hy : y.length < 2 ^ 64)
    (h : putB x ++ r <+: putB y ++ s) : x = y ∧ r <+: s := by
  obtain ⟨t, ht⟩ := h
  simp only [putB, List.append_assoc] at ht
  obtain ⟨hl, hd⟩ := List.append_inj ht (by simp [u64Le_length])
  have hl := u64Le_inj hl
  have hlen : x.length = y.length := by
    have h1 : uint.nat (W64 (x.length : Int)) = x.length := by word
    have h2 : uint.nat (W64 (y.length : Int)) = y.length := by word
    rw [← h1, ← h2, hl]
  obtain ⟨hxy, hrs⟩ := List.append_inj hd hlen
  exact ⟨hxy, ⟨t, hrs⟩⟩

theorem putB_prefix_inj' {x y : List w8} (hx : x.length < 2 ^ 64) (hy : y.length < 2 ^ 64)
    (h : putB x <+: putB y) : x = y :=
  (putB_cons_prefix (r := []) (s := []) hx hy (by simpa using h)).1

/-! ## The facts and the protocols -/

/-- The persistent facts the protocols carry (`notes/kvnet-protocol.md`): a peer frame's message
`st` sent by `src`; a proposed datum is a minted operation; a minted read context at the replica
`id` with the client's sequence number and key; a requested configuration change's payload is well
shaped; the answer `v` of the operation `d`; the answer `v` of the read `(id, seq, key)`. -/
structure KvFacts (GF : BundledGFunctors) [GooseExts] where
  msgOk : w64 → MsgSt → IProp GF
  opOk : List w8 → IProp GF
  readOk : w64 → w64 → List w8 → IProp GF
  confOk : List w8 → Prop
  ansOp : List w8 → List w8 → IProp GF
  ansRead : w64 → w64 → List w8 → List w8 → IProp GF
  msgOk_pers : ∀ src st, Persistent (msgOk src st)
  opOk_pers : ∀ d, Persistent (opOk d)
  readOk_pers : ∀ id seq key, Persistent (readOk id seq key)
  ansOp_pers : ∀ d v, Persistent (ansOp d v)
  ansRead_pers : ∀ id seq key v, Persistent (ansRead id seq key v)
  /-- A message a peer frame carries is one `getMsg` reads back (`MsgWf`: a type raft has,
  well-formed entries and snapshot): raft's messages are (its instance's obligation, after B). -/
  msgOk_wf : ∀ src st, msgOk src st ⊢ ⌜MsgWf st⌝

section facts
variable [GooseExts] {GF : BundledGFunctors} (F : KvFacts GF)

instance KvFacts.msgOk_persistent src st : Persistent (F.msgOk src st) := F.msgOk_pers src st
instance KvFacts.opOk_persistent d : Persistent (F.opOk d) := F.opOk_pers d
instance KvFacts.readOk_persistent id seq key : Persistent (F.readOk id seq key) :=
  F.readOk_pers id seq key
instance KvFacts.ansOp_persistent d v : Persistent (F.ansOp d v) := F.ansOp_pers d v
instance KvFacts.ansRead_persistent id seq key v : Persistent (F.ansRead id seq key v) :=
  F.ansRead_pers id seq key v

/-- The bytes of whole peer frames, one per message. -/
def framesBytes (sts : List (w64 × MsgSt)) : List w8 :=
  (sts.map (fun p => putB (encMsg p.2))).flatten

/-- Whole peer frames, each a message's encoding with its fact. -/
def framesOk (R : List w8) : IProp GF :=
  iprop(∃ sts : List (w64 × MsgSt), ⌜R = framesBytes sts ∧
      ∀ p ∈ sts, (encMsg p.2).length < 2 ^ 63⌝ ∗ [∗list] p ∈ sts, F.msgOk p.1 p.2)

/-- A request's payload's fact, by its kind. -/
def reqOk (id : w64) (kind : w8) (pl : List w8) : IProp GF :=
  if kind = reqProposeB then F.opOk pl
  else if kind = reqReadB then
    iprop(∃ seq key, ⌜pl = u64Le seq ++ putB key⌝ ∗ F.readOk id seq key)
  else if kind = reqConfB then iprop(⌜F.confOk pl⌝)
  else if kind = reqDisruptB then iprop(⌜∃ what to : w64, pl = u64Le what ++ u64Le to⌝)
  else iprop(True)

/-- An answer's fact, by the request's kind. -/
def ansOk (id : w64) (kind : w8) (pl v : List w8) : IProp GF :=
  if kind = reqProposeB then F.ansOp pl v
  else if kind = reqReadB then
    iprop(∃ seq key, ⌜pl = u64Le seq ++ putB key⌝ ∗ F.ansRead id seq key v)
  else iprop(True)

theorem reqOk_propose (id : w64) (d : List w8) : reqOk F id (W8 1) d = F.opOk d := by
  simp [reqOk, reqProposeB]

theorem ansOk_propose (id : w64) (d v : List w8) : ansOk F id (W8 1) d v = F.ansOp d v := by
  simp [ansOk, reqProposeB]

theorem reqOk_read (id : w64) (pl : List w8) :
    reqOk F id (W8 2) pl = iprop(∃ seq key, ⌜pl = u64Le seq ++ putB key⌝ ∗ F.readOk id seq key) := by
  simp [reqOk, reqProposeB, reqReadB]

theorem ansOk_read (id : w64) (pl v : List w8) :
    ansOk F id (W8 2) pl v = iprop(∃ seq key, ⌜pl = u64Le seq ++ putB key⌝ ∗ F.ansRead id seq key v) := by
  simp [ansOk, reqProposeB, reqReadB]

theorem reqOk_conf (id : w64) (pl : List w8) : reqOk F id (W8 3) pl = iprop(⌜F.confOk pl⌝) := by
  simp [reqOk, reqProposeB, reqReadB, reqConfB]

theorem reqOk_disrupt (id : w64) (pl : List w8) :
    reqOk F id (W8 4) pl = iprop(⌜∃ what to : w64, pl = u64Le what ++ u64Le to⌝) := by
  simp [reqOk, reqProposeB, reqReadB, reqConfB, reqDisruptB]

theorem ansOk_other (id : w64) (kind : w8) (pl v : List w8) (h1 : kind ≠ W8 1) (h2 : kind ≠ W8 2) :
    ansOk F id kind pl v = iprop(True) := by
  unfold ansOk reqProposeB reqReadB
  rw [if_neg h1, if_neg h2]

instance framesOk_persistent R : Persistent (framesOk F R) := by unfold framesOk; infer_instance
instance reqOk_persistent id kind pl : Persistent (reqOk F id kind pl) := by
  unfold reqOk; repeat' (first | infer_instance | split)
instance ansOk_persistent id kind pl v : Persistent (ansOk F id kind pl v) := by
  unfold ansOk; repeat' (first | infer_instance | split)

/-- A full dialer stream to the replica `id`. -/
def kvFull (id : w64) (ext : List w8) : IProp GF :=
  iprop((∃ R, ⌜ext = helloPeerB :: R⌝ ∗ framesOk F R) ∨
    (∃ kind tmo pl, ⌜ext = helloClientB :: putB (reqBytes kind tmo pl) ∧
        (reqBytes kind tmo pl).length < 2 ^ 63⌝ ∗ reqOk F id kind pl))

instance kvFull_persistent id ext : Persistent (kvFull F id ext) := by
  unfold kvFull; infer_instance

/-- **What dialers write to the replica `id`'s address**: a prefix of a full stream. -/
def kvP (id : w64) : Net.Proto GF := fun _ W => iprop(∃ ext, ⌜W <+: ext⌝ ∗ kvFull F id ext)

instance kvP_persistent id cn W : Persistent (kvP F id cn W) := by
  unfold kvP; infer_instance

theorem kvP_closed (id : w64) (cn : Nat) (W ext : List w8) (h : W <+: ext) :
    kvP F id cn ext ⊢ kvP F id cn W := by
  unfold kvP
  iintro ⟨%e, %he, #H⟩
  iexists e
  iframe H
  ipureintro; exact h.trans he

/-- A full client stream's protocol fact. -/
theorem kvP_req (id : w64) (cn : Nat) (kind : w8) (tmo : w64) (pl : List w8)
    (hl : (reqBytes kind tmo pl).length < 2 ^ 63) :
    reqOk F id kind pl ⊢ kvP F id cn (helloClientB :: putB (reqBytes kind tmo pl)) := by
  unfold kvP kvFull
  iintro #H
  iexists _
  isplitr
  · ipureintro; exact List.prefix_refl _
  iright
  iexists kind, tmo, pl
  iframe H
  ipureintro; exact ⟨rfl, hl⟩

end facts

section protos
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable (F : KvFacts GF)

/-- **What the replica `id` writes back**: nothing, no answer (`putB [0]`), or the reply frame of
the request the dialer wrote on the same connection, with its answer's fact. -/
def kvQ (id : w64) : Net.Proto GF := fun cn ext =>
  iprop(⌜ext = [] ∨ ext = putB [W8 0]⌝ ∨
    ∃ kind tmo pl v, sentLb cn false (helloClientB :: putB (reqBytes kind tmo pl)) ∗
      ⌜ext = putB (W8 1 :: v) ∧ (reqBytes kind tmo pl).length < 2 ^ 63 ∧ v.length < 2 ^ 63⌝ ∗
      ansOk F id kind pl v)

instance kvQ_persistent id cn ext : Persistent (kvQ F id cn ext) := by
  unfold kvQ; infer_instance

/-! ## The client's law -/

/-- **A client's reply** (see the file header): a client that wrote exactly the request frame
(`sendTok`, its own) and read a reply frame `putB (1 :: v)` has the answer's fact. -/
theorem client_reply (id : w64) (cn : Nat) (kind : w8) (tmo : w64) (pl v : List w8)
    (hl : (reqBytes kind tmo pl).length < 2 ^ 63) (hv : v.length < 2 ^ 63) :
    sendTok cn false (kvP F id) (helloClientB :: putB (reqBytes kind tmo pl)) -∗
      recvTok cn false (kvQ F id) (putB (W8 1 :: v)) -∗ ansOk F id kind pl v := by
  iintro Hs Hr
  icases recvTok_proto _ _ _ _ $$ Hr with ⟨-, Hp⟩
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hpre, #HQ⟩)
  · exfalso; simp [putB] at Hnil
  unfold kvQ
  icases HQ with (%Hext | ⟨%kind', %tmo', %pl', %v', #Hlb, %Hx, #Ha⟩)
  · exfalso
    rcases Hext with rfl | rfl
    · obtain ⟨t, ht⟩ := Hpre; simp [putB] at ht
    · have := putB_prefix_inj' (x := W8 1 :: v) (y := [W8 0]) (by simp; omega) (by simp) Hpre
      simp at this
  obtain ⟨rfl, hl', hv'⟩ := Hx
  have hvv := putB_prefix_inj' (by simp; omega) (by simp; omega) Hpre
  simp only [List.cons.injEq, true_and] at hvv
  subst hvv
  icases sendTok_sentLb_prefix _ _ _ _ _ $$ Hs Hlb with %Hw
  have Hw' : putB (reqBytes kind' tmo' pl') <+: putB (reqBytes kind tmo pl) :=
    (List.cons_prefix_cons.mp Hw).2
  have hreq := putB_prefix_inj' (by omega) (by omega) Hw'
  simp only [reqBytes, List.cons.injEq] at hreq
  obtain ⟨rfl, hrest⟩ := hreq
  have hpl : pl' = pl := List.append_cancel_left
    (show u64Le (tmo'.sdiv (W64 1000000)) ++ pl' = u64Le (tmo'.sdiv (W64 1000000)) ++ pl by
      have h8 := congrArg (List.take 8) hrest
      rw [List.take_append_of_le_length (by simp [u64Le_length]),
        List.take_of_length_le (by simp [u64Le_length]),
        List.take_append_of_le_length (by simp [u64Le_length]),
        List.take_of_length_le (by simp [u64Le_length])] at h8
      rw [h8] at hrest ⊢; exact hrest)
  subst hpl
  iexact Ha

/-- `client_reply` from what a `Read` leaves (`recvTokL`), a step later. -/
theorem client_reply_L (id : w64) (cn : Nat) (kind : w8) (tmo : w64) (pl v : List w8)
    (hl : (reqBytes kind tmo pl).length < 2 ^ 63) (hv : v.length < 2 ^ 63) :
    sendTok cn false (kvP F id) (helloClientB :: putB (reqBytes kind tmo pl)) -∗
      recvTokL cn false (kvQ F id) (putB (W8 1 :: v)) -∗ ▷ ansOk F id kind pl v := by
  iintro Hs Hr
  ihave Hr := recvTokL_later _ _ _ _ $$ Hr
  inext
  iapply client_reply F id cn kind tmo pl v hl hv $$ Hs Hr

/-- A reader's token gives what was written of its direction, keeping the token. -/
theorem recvTok_keep_sentLb (cn : Nat) (s s' : Bool) (hs : (!s) = s') (P : Net.Proto GF)
    (R : List w8) : recvTok cn s P R ⊢ recvTok cn s P R ∗ sentLb cn s' R := by
  subst hs
  unfold recvTok recvCore sentLb connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, #Hreg, #Hai, #Hm⟩, %hP, Hr, #Hlb⟩, #Hp⟩
  isplitl [Hr]
  · iframe Hp
    iexists γ, Pd, Pa
    iframe He Hreg Hai Hm Hr Hlb
    ipureintro; exact hP
  · iexists γ; iframe He Hlb

/-- A reader's token (its fact a step later) shows the connection is the library's. -/
theorem recvTokL_connIs (cn : Nat) (s : Bool) (P : Net.Proto GF) (R : List w8) :
    recvTokL cn s P R ⊢ recvTokL cn s P R ∗ connIs cn := by
  unfold recvTokL recvCore connIs connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, #Hreg, #Hai, #Hm⟩, %hP, Hr, #Hlb⟩, Hp⟩
  isplitl [Hr Hp]
  · iframe Hp
    iexists γ, Pd, Pa
    iframe He Hreg Hai Hm Hr Hlb
    ipureintro; exact hP
  · iexists γ; iframe He Hreg

/-! ## The server's laws -/

/-- **A request read by the replica `id`** (`serveClient`): its frame is a request of the protocol,
with its payload's fact and the `sentLb` its reply cites. -/
theorem server_request (id : w64) (cn : Nat) (body : List w8) (hb : body.length < 2 ^ 64) :
    recvTok cn true (kvP F id) (helloClientB :: putB body) -∗
      recvTok cn true (kvP F id) (helloClientB :: putB body) ∗
      ∃ kind tmo pl, ⌜body = reqBytes kind tmo pl ∧ (reqBytes kind tmo pl).length < 2 ^ 63⌝ ∗
        reqOk F id kind pl ∗ sentLb cn false (helloClientB :: putB body) := by
  iintro Hr
  icases recvTok_keep_sentLb cn true false rfl _ _ $$ Hr with ⟨Hr, #Hlb⟩
  icases recvTok_proto _ _ _ _ $$ Hr with ⟨Hr, Hp⟩
  iframe Hr
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hpre, #HP⟩)
  · exfalso; cases Hnil
  unfold kvP kvFull
  icases HP with ⟨%e, %He, (⟨%R, %HR, -⟩ | ⟨%kind, %tmo, %pl, %Hx, #Hok⟩)⟩
  · exfalso
    subst HR
    have := (Hpre.trans He)
    simp [helloClientB, helloPeerB] at this
  obtain ⟨rfl, hl⟩ := Hx
  have Hb : putB body <+: putB (reqBytes kind tmo pl) :=
    (List.cons_prefix_cons.mp (Hpre.trans He)).2
  have := putB_prefix_inj' hb (by omega) Hb
  subst this
  iexists kind, tmo, pl
  iframe Hok
  isplitr
  · ipureintro; exact ⟨rfl, hl⟩
  iexact Hlb

/-- **The reply frame** the replica writes for a request it read (what `writeFrame`'s accessor
needs, through `write_acc`): the answer's fact and the request's `sentLb`. -/
theorem server_reply (id : w64) (cn : Nat) (kind : w8) (tmo : w64) (pl v : List w8)
    (hl : (reqBytes kind tmo pl).length < 2 ^ 63) (hv : v.length < 2 ^ 63) :
    sentLb cn false (helloClientB :: putB (reqBytes kind tmo pl)) -∗ ansOk F id kind pl v -∗
      kvQ F id cn (putB (W8 1 :: v)) := by
  iintro #Hlb #Ha
  unfold kvQ
  iright
  iexists kind, tmo, pl, v
  iframe Hlb Ha
  ipureintro; exact ⟨rfl, hl, hv⟩

/-- No answer needs nothing. -/
theorem server_noans (id : w64) (cn : Nat) : ⊢ kvQ F id cn (putB [W8 0]) := by
  unfold kvQ
  ileft
  ipureintro; right; rfl

/-! ## Peer frames -/

theorem framesBytes_snoc (sts : List (w64 × MsgSt)) (p : w64 × MsgSt) :
    framesBytes (sts ++ [p]) = framesBytes sts ++ putB (encMsg p.2) := by
  simp [framesBytes]

/-- **A peer frame to send** after whole frames: the message's fact. -/
theorem peer_send (id : w64) (cn : Nat) (sts : List (w64 × MsgSt)) (src : w64) (st : MsgSt)
    (hl : ∀ p ∈ sts, (encMsg p.2).length < 2 ^ 63) (hst : (encMsg st).length < 2 ^ 63) :
    ([∗list] p ∈ sts, F.msgOk p.1 p.2) -∗ F.msgOk src st -∗
      kvP F id cn (helloPeerB :: framesBytes (sts ++ [(src, st)])) := by
  iintro #Hs #Hm
  unfold kvP kvFull framesOk
  iexists _
  isplitr
  · ipureintro; exact List.prefix_refl _
  ileft
  iexists _
  isplitr
  · ipureintro; rfl
  iexists sts ++ [(src, st)]
  isplitr
  · ipureintro
    refine ⟨rfl, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with h | h
    · exact hl p h
    · simp at h; subst h; exact hst
  iapply BigSepL.bigSepL_append.2
  iframe Hs
  iapply BigSepL.bigSepL_singleton.2
  iexact Hm

/-- Whole frames of raw bodies (what a reader has parsed). -/
def rawFrames (bs : List (List w8)) : List w8 := (bs.map putB).flatten

/-- The parsing of frames: raw frames followed by a frame `b`, within whole message frames, are
those messages' encodings, the next one `b`. -/
theorem frames_next (bs : List (List w8)) (b : List w8) (sts : List (w64 × MsgSt))
    (hbs : ∀ x ∈ bs, x.length < 2 ^ 64) (hb : b.length < 2 ^ 64)
    (hsts : ∀ p ∈ sts, (encMsg p.2).length < 2 ^ 63)
    (h : rawFrames bs ++ putB b <+: framesBytes sts) :
    ∃ p ∈ sts, b = encMsg p.2 := by
  induction bs generalizing sts with
  | nil =>
    cases sts with
    | nil =>
      exfalso
      obtain ⟨t, ht⟩ := h
      have := congrArg List.length ht
      simp [rawFrames, framesBytes, putB, u64Le_length] at this
      all_goals omega
    | cons p sts =>
      simp only [rawFrames, List.map_nil, List.flatten_nil, List.nil_append, framesBytes,
        List.map_cons, List.flatten_cons] at h
      have hp := putB_cons_prefix (x := b) (y := encMsg p.2) (r := []) hb
        (by have := hsts p (by simp); omega) (by simpa using h)
      exact ⟨p, List.mem_cons_self, hp.1⟩
  | cons x bs ih =>
    cases sts with
    | nil =>
      exfalso
      obtain ⟨t, ht⟩ := h
      have := congrArg List.length ht
      simp [rawFrames, framesBytes, putB, u64Le_length] at this
      all_goals omega
    | cons p sts =>
      simp only [rawFrames, List.map_cons, List.flatten_cons, framesBytes, List.append_assoc] at h
      have := putB_cons_prefix (hbs x (by simp)) (by have := hsts p (by simp); omega) h
      obtain ⟨q, hq, hbq⟩ := ih sts (fun y hy => hbs y (by simp [hy]))
        (fun q hq => hsts q (by simp [hq])) this.2
      exact ⟨q, List.mem_cons_of_mem _ hq, hbq⟩

/-- **A peer frame read by the replica `id`** after whole frames (`servePeer`): a message's encoding
with its fact. -/
theorem server_peer (id : w64) (cn : Nat) (bs : List (List w8)) (b : List w8)
    (hbs : ∀ x ∈ bs, x.length < 2 ^ 64) (hb : b.length < 2 ^ 64) :
    recvTok cn true (kvP F id) (helloPeerB :: rawFrames bs ++ putB b) -∗
      recvTok cn true (kvP F id) (helloPeerB :: rawFrames bs ++ putB b) ∗
      ∃ src st, ⌜b = encMsg st⌝ ∗ F.msgOk src st := by
  iintro Hr
  icases recvTok_proto _ _ _ _ $$ Hr with ⟨Hr, Hp⟩
  iframe Hr
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hpre, #HP⟩)
  · exfalso; cases Hnil
  unfold kvP kvFull
  icases HP with ⟨%e, %He, (⟨%R, %HR, #Hf⟩ | ⟨%kind, %tmo, %pl, %Hx, -⟩)⟩
  rotate_left
  · exfalso
    obtain ⟨rfl, -⟩ := Hx
    have := (Hpre.trans He)
    simp [helloClientB, helloPeerB] at this
  subst HR
  unfold framesOk
  icases Hf with ⟨%sts, %Hs, #Hall⟩
  obtain ⟨rfl, hsts⟩ := Hs
  have H := (List.cons_prefix_cons.mp (Hpre.trans He)).2
  obtain ⟨p, hp, rfl⟩ := frames_next bs b sts hbs hb hsts (by simpa using H)
  iexists p.1, p.2
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_mem (Φ := fun p : w64 × MsgSt => F.msgOk p.1 p.2) hp $$ Hall

/-! ## The glue to the byte-level specs -/

/-- A client's writes on its end of a connection to the replica `id` (the end is the dialer's,
whatever `s` the byte-level specs carry along). -/
def kvW (id : w64) : Nat → Bool → List w8 → IProp GF := fun cn _ w => sendTok cn false (kvP F id) w

/-- A client's reads on its end of a connection to the replica `id`. -/
def kvR (id : w64) : Nat → Bool → List w8 → IProp GF := fun cn _ got => recvTokL cn false (kvQ F id) got

/-- **A dialer's resources for `RequestVia`** (`connRes`): from its end of a connection to the
replica `id` (`connEnd`, what `dial_au` gives) and the protocol fact of the stream the call will
write, the writes through `sendTok` (`write_acc`), the reads through `recvTokL` (`read_au`), the
closes through `connIs` (`close_au`). -/
theorem kv_connRes (id : w64) (cn : Nat) (T : List w8) :
    connEnd cn false (kvP F id) (kvQ F id) [] [] -∗ kvP F id cn T -∗
      connRes cn false T (kvW F id)
        (kvR F id) := by
  iintro Hce #HT
  unfold kvW kvR
  unfold connEnd
  icases Hce with ⟨Hs, Hr⟩
  ihave #Hc := sendTok_connIs _ _ _ _ $$ Hs
  ihave Hr := recvTok_L _ _ _ _ $$ Hr
  unfold connRes
  iframe Hs Hr
  isplitl []
  · unfold wAcc
    imodintro
    iintro %w %rs %Hpre Hw
    ihave #Hp : kvP F id cn ([] ++ (w ++ rs)) $$ []
    · iapply kvP_closed F id cn _ T (by simpa using Hpre) $$ HT
    ihave #Hacc := write_acc cn false (kvP F id) [] (w ++ rs) $$ Hp
    ihave Hw' : writeP cn false (kvP F id) [] w none $$ [Hw]
    · unfold writeP; dsimp only [List.nil_append] at *; iexact Hw
    imod Hacc $$ %w %rs %rfl Hw' with ⟨%st0, %d, He, Hd, Hcl⟩
    imodintro
    iexists st0, d
    iframe He Hd
    iintro %k %res %d' %Ho He Hd
    imod Hcl $$ %k %res %d' %Ho He Hd with H
    imodintro
    unfold writeP at *
    dsimp only [List.nil_append] at *
    iexact H
  isplitl []
  · unfold rAcc
    imodintro
    iintro %got %m Hg
    imod read_au cn false (kvQ F id) got m $$ Hg with ⟨%st, %d, Hend, Hdir, Hcl⟩
    imodintro
    iexists st, d
    iframe Hend Hdir
    iintro %r %d' %Ho Hend Hdir
    imod Hcl $$ %r %d' %Ho Hend Hdir with ⟨H, -⟩
    imodintro
    iexact H
  unfold cAcc
  imodintro
  imod close_au cn false $$ Hc with ⟨%st, %d, Hend, Hdir, Hcl⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Ho Hend Hdir
  imod Hcl $$ %res %st' %d' %Ho Hend Hdir with -
  imodintro
  itrivial

/-- **The dial update `Request`/`RequestWithin` take** (with nothing on failure, `Fl := True`), from
the replica `id`'s address's protocol and the protocol fact of the request's stream (any
connection's: `kvP` does not depend on it). -/
theorem kv_dial (id : w64) (a : GoString) (T : List w8) :
    addrProto a (kvP F id) (kvQ F id) -∗ (∀ cn, kvP F id cn T) -∗
      iprop(True ∧
        |={⊤,∅}=> ∃ S, netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S ∪ {[cn]}) -∗
            netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
            netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn true -∗
            ((netFresh (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ={∅,⊤}=∗
                connRes cn false T (kvW F id)
                  (kvR F id)) ∧
             (netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false
                { NetEnd.fresh with closed := true } -∗
              netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false ⟨[], .fin⟩ ={∅,⊤}=∗
                True))) := by
  iintro #Ha #HT
  isplit
  · itrivial
  imod dial_au a (kvP F id) (kvQ F id) $$ Ha with ⟨%S, Hp, Hk⟩
  imodintro
  iexists S
  iframe Hp
  iintro %cn %Hcn Hp Hat Hf
  ihave Hk := Hk $$ %cn %Hcn Hp Hat Hf
  isplit
  · iintro Hf'
    icases Hk with ⟨Hk, -⟩
    imod Hk $$ Hf' with ⟨He, -⟩
    imodintro
    iapply kv_connRes F id cn T $$ He
    iapply HT
  · icases Hk with ⟨-, Hk⟩
    iexact Hk

end protos

end raft_kvnet
end EtcdGrove
end Perennial
