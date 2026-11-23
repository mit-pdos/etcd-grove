/-
The protocol of the net/rpc model (`models/net/rpc`) over the net library's per-address protocols
(`GooseLang/Ext/Net/Proto.lean`): the address-level service specs, and the per-connection ghost
state that ties each run of a method at a server to exactly one request a client wrote. Ported
from dsverify-lab's `Harness/Proof/net/rpc/Proto.lean` (`348a866`), over the model's two-frame
wire (`Base.lean`) and Go's own client (sequence numbers in the order written).

**Service specs.** A method spec (`MethodSpec`) is a precondition with the caller's continuation,
over encodings: `S m args Φ` is what a caller deposits for method `m` on argument bytes `args`,
and `Φ reply msg` is what it gets back with the reply bytes and the error message (`""` for
success; a method's error message otherwise, which the client sees as `rpc.ServerError(msg)`). An
address's services are fixed with the address (`RpcWorld.SS a svc`: the spec of service `svc` at
address `a`, if it offers it).

**The world** (`RpcWorld`): the address specs and the name of a registry of connections (`regInv`,
a ghost map from a connection to its names): the dialer registers a connection with the token
`connFresh cn false` its dial returned, so a connection's names are unique and every party agrees
on them (`regElem`).

**A connection** (`RpcConnNames`, `connInv`): its requests in the order written (a mono-list
`reqs` of `RpcReq`: `"Service.Method"`, the argument bytes, the saved continuation `post` and the
client's collection token `col`; the `i`-th request has the sequence number `i`, as Go's client
numbers them), the server reader's count `k` of requests it has taken (`ctr`, half with the
reader), the answers (a ghost map `ans` from a request's index to `none` while its run is pending,
`some (msg, reply)` once answered), and the dialer's names of each request (`nm`, a ghost map from
an index to `post`, `col` and a token `ap` the dialer gives up when it writes the request: the
dialer chose them when it numbered the request, before writing it; its authority is the
dialer's). The invariant holds the deposit of every request not taken yet, for every answered
request `Φ reply msg` until the client trades its `col` token for it (`answerRes`), and for every
request its `nm` entry and `ap` token. The reader's half of `ctr` starts in the invariant, claimed
once with `connFresh cn true` (the acceptor's token). So a deposit goes to at most one run (the
reader takes request `k` once and moves on), `Φ reply msg` comes back only from that run's answer,
and a client's error other than a `ServerError` leaves its deposit with the connection.

**Protocols** (`reqProto W a`, `respProto W a`): what the dialer writes is a prefix of the wire of
the requests in `reqs` (`reqsWire`, lower bound; fewer than `2 ^ 64` of them, so their sequence
numbers are distinct); what the acceptor writes is a prefix of the wire of answers (`respsWire`:
for each its index, `"Service.Method"`, message and reply), each with its persistent answer.
Readers parse frames from a stream that may end mid-frame, so the protocols speak of prefixes; they
also bound each payload's length (below `2 ^ 63`, as a Go slice's), so a frame's length prefix
determines it.

**The handshake** (`RpcWorld.hs`, `RpcWorld.hsAns`, per address; `rpcAddrP W a hs hsAns`): before
its requests a dialer writes `W.hs a`, and before its answers an acceptor writes `W.hsAns a`, so
each direction is the handshake followed by the frames. Raw net/rpc (`Dial`, `Server.Accept`) has
none (`rpcAddr W a := rpcAddrP W a [] []`); over HTTP (`DialHTTPPath`, `Server.ServeHTTP`) the
dialer's is its `CONNECT` request and the acceptor's the `200` answer. A dialer writes nothing after
its handshake until it has read the answer (`reqProto`: beyond `W.hs a` only with `sentLb` of
`W.hsAns a`), so a server that reads ahead (net/http's buffered reader) sees no request byte before
it has answered.
-/
module

public import Net.Proof.net.rpc.Base
public import GooseLang.Ext.Net.Proto
public import Perennial.Ghost.SavedProp

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

/-! ## Service names -/

/-- The index of the last `'.'` of `s` (`strings.LastIndex(serviceMethod, ".")`). -/
def lastDotIdx (s : GoString) : Option Nat :=
  ((List.range s.length).reverse.find? (fun i => s[i]? = some (W8 46)))

/-- `"Service.Method"` split at its last dot (`Server.readRequestHeader`). -/
def splitSM (sm : GoString) : Option (GoString × GoString) :=
  (lastDotIdx sm).map fun i => (sm.take i, sm.drop (i + 1))

/-! ## Requests and answers -/

/-- A request as the ghost state records it: `"Service.Method"`, the argument bytes, the saved
continuation's name `post` and the client's collection token `col`. Its sequence number is its
index in the connection's list. -/
abbrev RpcReq := GoString × List w8 × GName × GName

namespace RpcReq
abbrev sm (r : RpcReq) : GoString := r.1
abbrev body (r : RpcReq) : List w8 := r.2.1
abbrev post (r : RpcReq) : GName := r.2.2.1
abbrev col (r : RpcReq) : GName := r.2.2.2
end RpcReq

/-- A request's payloads fit a frame. -/
def reqOk (r : RpcReq) : Prop := r.sm.length + 16 < 2 ^ 63 ∧ r.body.length < 2 ^ 63

/-- The wire of the requests `L`, the `i`-th with the sequence number `i`. -/
def reqsWire (L : List RpcReq) : List w8 :=
  (L.mapIdx fun i r => reqWire (W64 i) r.sm r.body).flatten

/-- An answer: the index of the request it answers, the `"Service.Method"` it names, the error
message (`""` for none) and the reply bytes. -/
abbrev Ans := Nat × GoString × GoString × List w8

namespace Ans
abbrev idx (x : Ans) : Nat := x.1
abbrev sm (x : Ans) : GoString := x.2.1
abbrev msg (x : Ans) : GoString := x.2.2.1
abbrev reply (x : Ans) : List w8 := x.2.2.2
end Ans

/-- An answer's two payloads: its header and its body (the reply, empty after an error). -/
def ansPls (x : Ans) : List (List w8) :=
  [respHdr (W64 x.idx) x.sm x.msg, if x.msg = [] then x.reply else []]

/-- An answer's payloads fit a frame, and its index a sequence number. -/
def ansOk (x : Ans) : Prop :=
  x.sm.length + x.msg.length + 24 < 2 ^ 63 ∧ x.reply.length < 2 ^ 63 ∧ x.idx < 2 ^ 64

/-- The wire of the answers `Rs`. -/
def respsWire (Rs : List Ans) : List w8 := framesOf (Rs.flatMap ansPls)

/-- The names of a connection (see the file header). -/
abbrev RpcConnNames := GName × GName × GName × GName

namespace RpcConnNames
abbrev reqs (n : RpcConnNames) : GName := n.1
abbrev ctr (n : RpcConnNames) : GName := n.2.1
abbrev ans (n : RpcConnNames) : GName := n.2.2.1
abbrev nm (n : RpcConnNames) : GName := n.2.2.2
end RpcConnNames

/-! ## Specs and the world -/

/-- A method spec: `S m args Φ` is the deposit for method `m` on argument bytes `args` with
continuation `Φ` (over the reply bytes and the error message, `""` for success). -/
abbrev MethodSpec (GF : BundledGFunctors) :=
  GoString → List w8 → (List w8 → GoString → IProp GF) → IProp GF

/-- The rpc world: the services of each address (`SS a svc`, the spec of service `svc` at
address `a`, if it offers it) and the name of the registry of connections. -/
structure RpcWorld (GF : BundledGFunctors) where
  SS : GoString → GoString → Option (MethodSpec GF)
  reg : GName
  /-- The handshake a dialer of an address writes before its requests (`[]` for raw net/rpc,
  `connectReq path` over HTTP). -/
  hs : GoString → List w8 := fun _ => []
  /-- The handshake's answer an acceptor writes before its answers (`[]` for raw net/rpc,
  `connectAns` over HTTP). -/
  hsAns : GoString → List w8 := fun _ => []

def rpcN : Namespace := nroot.@"net.rpc"
def regN' : Namespace := rpcN.@"reg"
def connN : Namespace := rpcN.@"conn"

/-! ## Pure facts of the wire -/

/-- Frames parse uniquely: what extends the frames `ps` with a frame `p` and is a prefix of the
frames `qs` has `ps ++ [p]` as a prefix of `qs` (payloads shorter than `2 ^ 63`). -/
theorem framesOf_parse : ∀ (ps qs : List (List w8)) (p y : List w8),
    (∀ q ∈ ps, q.length < 2 ^ 63) → p.length < 2 ^ 63 → (∀ q ∈ qs, q.length < 2 ^ 63) →
    framesOf ps ++ frameOf p ++ y <+: framesOf qs → ps ++ [p] <+: qs
  | [], [], p, y, _, _, _, h => by
    exfalso
    have := h.length_le
    simp [framesOf_nil, frameOf_length] at this
  | [], q :: qs, p, y, _, hp, hqs, h => by
    rw [framesOf_cons] at h
    simp only [framesOf_nil, List.nil_append] at h
    have := frameOf_prefix_eq hp (hqs q (by simp)) (x := y) (y := framesOf qs) h
    subst this
    simp
  | p0 :: ps, [], p, y, _, _, _, h => by
    exfalso
    have := h.length_le
    simp [framesOf_cons, framesOf_nil, frameOf_length] at this
  | p0 :: ps, q :: qs, p, y, hps, hp, hqs, h => by
    rw [framesOf_cons, framesOf_cons] at h
    have h0 : p0 = q := frameOf_prefix_eq (hps p0 (by simp)) (hqs q (by simp))
      (x := framesOf ps ++ frameOf p ++ y) (y := framesOf qs)
      (by simpa only [List.append_assoc] using h)
    subst h0
    have h' : framesOf ps ++ frameOf p ++ y <+: framesOf qs := by
      simpa only [List.append_assoc, List.prefix_append_right_inj] using h
    have := framesOf_parse ps qs p y (fun q hq => hps q (by simp [hq])) hp
      (fun q hq => hqs q (by simp [hq])) h'
    simpa using this

theorem ansPls_length (x : Ans) : (ansPls x).length = 2 := rfl

/-- The `2k + j`-th payload of the answers `Rs` is the `j`-th of the `k`-th answer. -/
theorem flatMap_ansPls_getElem? : ∀ (Rs : List Ans) (k j : Nat), j < 2 →
    (Rs.flatMap ansPls)[2 * k + j]? = (Rs[k]?).bind (fun x => (ansPls x)[j]?)
  | [], _, _, _ => by simp
  | x :: Rs, 0, j, hj => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero,
      Option.bind_some]
    rw [List.getElem?_append_left (by rw [ansPls_length]; exact hj)]
  | x :: Rs, k + 1, j, hj => by
    simp only [List.flatMap_cons, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [ansPls_length]; omega), ansPls_length,
      show 2 * (k + 1) + j - 2 = 2 * k + j by omega]
    exact flatMap_ansPls_getElem? Rs k j hj

theorem flatMap_ansPls_length (C : List Ans) : (C.flatMap ansPls).length = 2 * C.length := by
  induction C with
  | nil => rfl
  | cons x C ih => simp [List.flatMap_cons, ih, ansPls_length]; omega

theorem ansPls_ok (x : Ans) (h : ansOk x) : ∀ q ∈ ansPls x, q.length < 2 ^ 63 := by
  obtain ⟨h1, h2, -⟩ := h
  intro q hq
  simp only [ansPls, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · simp [respHdr, strEnc_length, u64Le_length]; omega
  · split <;> simp <;> omega

theorem flatMap_ansPls_ok (Rs : List Ans) (h : ∀ x ∈ Rs, ansOk x) :
    ∀ q ∈ Rs.flatMap ansPls, q.length < 2 ^ 63 := by
  intro q hq
  obtain ⟨x, hx, hq⟩ := List.mem_flatMap.1 hq
  exact ansPls_ok x (h x hx) q hq

/-- The reader's next frame: after the frames of the answers `C` it has consumed and `j` more
payloads `pre` (`j = 0`: none; `j = 1`: a header), a frame `p` read from a stream that is a prefix
of the frames of the answers `Rs` is the `j`-th payload of the `C.length`-th answer of `Rs`. -/
theorem ans_next (C Rs : List Ans) (pre : List (List w8)) (p y : List w8) (j : Nat)
    (hj : j < 2) (hpre : pre.length = j) (hC : ∀ x ∈ C, ansOk x) (hRs : ∀ x ∈ Rs, ansOk x)
    (hpreOk : ∀ q ∈ pre, q.length < 2 ^ 63) (hp : p.length < 2 ^ 63)
    (h : framesOf (C.flatMap ansPls ++ pre) ++ frameOf p ++ y <+: respsWire Rs) :
    ∃ x, Rs[C.length]? = some x ∧ (ansPls x)[j]? = some p := by
  have hok : ∀ q ∈ C.flatMap ansPls ++ pre, q.length < 2 ^ 63 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact flatMap_ansPls_ok C hC q hq
    · exact hpreOk q hq
  have hpf := framesOf_parse _ _ p y hok hp (flatMap_ansPls_ok Rs hRs) (by
    unfold respsWire at h; exact h)
  have hlen : (C.flatMap ansPls ++ pre).length = 2 * C.length + j := by
    rw [List.length_append, flatMap_ansPls_length, hpre]
  have hget : (C.flatMap ansPls ++ pre ++ [p])[2 * C.length + j]? = some p := by
    rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    rfl
  have hidx : (Rs.flatMap ansPls)[2 * C.length + j]? = some p := by
    obtain ⟨t, ht⟩ := hpf
    rw [← ht, List.getElem?_append_left (by rw [List.length_append, hlen]; simp)]
    exact hget
  rw [flatMap_ansPls_getElem? Rs C.length j hj] at hidx
  cases hx : Rs[C.length]? with
  | none => rw [hx] at hidx; cases hidx
  | some x => rw [hx] at hidx; exact ⟨x, rfl, hidx⟩

/-- A response header decodes uniquely (its strings shorter than `2 ^ 62`). -/
theorem respHdr_inj {seq seq' : w64} {sm sm' e e' : GoString}
    (h1 : sm.length < 2 ^ 62) (h2 : e.length < 2 ^ 62) (h1' : sm'.length < 2 ^ 62)
    (h2' : e'.length < 2 ^ 62) (h : respHdr seq sm e = respHdr seq' sm' e') :
    seq = seq' ∧ sm = sm' ∧ e = e' := by
  simp only [respHdr, List.append_assoc] at h
  obtain ⟨hs, h⟩ := List.append_inj h (by simp [u64Le_length])
  obtain ⟨hsm, he⟩ := strEnc_append_inj (by omega) (by omega) h
  have he' : strEnc e ++ [] = strEnc e' ++ [] := by simpa using he
  exact ⟨u64Le_inj hs, hsm, (strEnc_append_inj (by omega) (by omega) he').1⟩

section proto
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [π : NetProtoGS]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The registry: every registered connection's dialer gave up its fresh token. -/
def regInv (W : RpcWorld GF) : IProp GF :=
  iprop(∃ M : GMap Nat RpcConnNames, ghostMapAuth W.reg 1 M ∗
    [∗map] cn ↦ _n ∈ M, connFresh (Gg := Gg) cn false)

/-- Connection `cn`'s names are `γ` (persistent). -/
def regElem (W : RpcWorld GF) (cn : Nat) (γ : RpcConnNames) : IProp GF :=
  ghostMapElem W.reg cn .discard γ

/-- The deposit of request `r` at address `a`: its service is one `a` offers, with spec `S`, and
the caller's deposit `S m body Φ` for its saved continuation `Φ` (saved uncurried, over the pair
of the reply and the message). -/
def reqDeposit (W : RpcWorld GF) (a : GoString) (r : RpcReq) : IProp GF :=
  iprop(∃ (svc m : GoString) (S : MethodSpec GF) (Φ : List w8 → GoString → IProp GF),
    ⌜splitSM r.sm = some (svc, m) ∧ W.SS a svc = some S⌝ ∗
    savedPredOwn r.post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ S m r.body Φ)

/-- The answer's continuation for request `r`: `Φ reply msg` for its saved `Φ`. -/
def replyEscrow (r : RpcReq) (reply : List w8) (msg : GoString) : IProp GF :=
  iprop(∃ Φ : List w8 → GoString → IProp GF,
    savedPredOwn r.post .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ Φ reply msg)

/-- What the invariant holds for answer `o` of request `i` of `L`: for every answer, the
continuation of its reply and message, or the client's token (once collected). -/
def answerRes (L : List RpcReq) (i : Nat) (o : Option (GoString × List w8)) : IProp GF :=
  match o with
  | some (msg, reply) => iprop(∃ r, ⌜L[i]? = some r⌝ ∗ (replyEscrow r reply msg ∨ token r.col))
  | none => iprop(True)

/-- The dialer's names of request `i` (`r`'s `post` and `col`, and the token `ap` it gave up). -/
def reqNamed (γ : RpcConnNames) (i : Nat) (r : RpcReq) : IProp GF :=
  iprop(∃ ap : GName, ghostMapElem γ.nm i .discard (r.post, r.col, ap) ∗ token ap)

/-- The invariant of connection `cn` (to address `a`) with names `γ`; see the file header. -/
def connInv (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) : IProp GF :=
  iprop(∃ (L : List RpcReq) (k : Nat) (A : GMap Nat (Option (GoString × List w8))),
    monoListAuthOwn γ.reqs (1 : Qp).half L ∗ ghostVar γ.ctr (1 : Qp).half k ∗
    ghostMapAuth γ.ans 1 A ∗
    (ghostVar γ.ctr (1 : Qp).half 0 ∨ connFresh (Gg := Gg) cn true) ∗
    ⌜k ≤ L.length ∧ ∀ i, (A.lookup i).isSome → i < k⌝ ∗
    ([∗list] i ↦ r ∈ L, reqNamed γ i r) ∗
    ([∗list] r ∈ L.drop k, reqDeposit W a r) ∗
    ([∗map] i ↦ o ∈ A, answerRes L i o))

/-- Connection `cn` to address `a` has names `γ` and its invariant (persistent). -/
def isRpcConn (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) : IProp GF :=
  iprop(regElem W cn γ ∗ inv connN (connInv W a cn γ))

/-- What a dialer of `a` writes: a prefix of the handshake `W.hs a` followed by the wire of
requests of the connection (persistent lower bound), fewer than `2 ^ 64`, each fitting its frames;
and nothing beyond the handshake before the acceptor has written its answer `W.hsAns a` (the
dialer waits for it: `DialHTTPPath`). -/
def reqProto (W : RpcWorld GF) (a : GoString) : Proto GF := fun cn bs =>
  iprop(∃ (γ : RpcConnNames) (L : List RpcReq), isRpcConn W a cn γ ∗ monoListLbOwn γ.reqs L ∗
    ⌜(∀ r ∈ L, reqOk r) ∧ L.length ≤ 2 ^ 64 ∧ bs <+: W.hs a ++ reqsWire L⌝ ∗
    (⌜bs <+: W.hs a⌝ ∨ sentLb (Gg := Gg) cn true (W.hsAns a)))

/-- What an acceptor at `a` writes: a prefix of the handshake's answer `W.hsAns a` followed by the
wire of answers of the connection, each with its persistent answer and fitting its frames. -/
def respProto (W : RpcWorld GF) (a : GoString) : Proto GF := fun cn bs =>
  iprop(∃ (γ : RpcConnNames) (Rs : List Ans), isRpcConn W a cn γ ∗
    ([∗list] x ∈ Rs, ghostMapElem γ.ans x.idx .discard (some (x.msg, x.reply))) ∗
    ⌜(∀ x ∈ Rs, ansOk x) ∧ bs <+: W.hsAns a ++ respsWire Rs⌝)

/-- Address `a` serves rpc in world `W` after the handshake `hs` (the dialer's) and `hsAns` (the
acceptor's answer): its protocols, and the registry (persistent). -/
def rpcAddrP (W : RpcWorld GF) (a : GoString) (hs hsAns : List w8) : IProp GF :=
  iprop(addrProto (Gg := Gg) a (reqProto W a) (respProto W a) ∗ inv regN' (regInv W) ∗
    ⌜W.hs a = hs ∧ W.hsAns a = hsAns⌝)

/-- Address `a` serves raw net/rpc in world `W` (no handshake: `Server.Accept`, `Dial`). -/
def rpcAddr (W : RpcWorld GF) (a : GoString) : IProp GF := rpcAddrP W a [] []

instance regElem_persistent (W : RpcWorld GF) (cn : Nat) (γ : RpcConnNames) :
    Persistent (regElem (GF := GF) W cn γ) := by
  unfold regElem; infer_instance

instance isRpcConn_persistent (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) :
    Persistent (isRpcConn (Gg := Gg) W a cn γ) := by
  unfold isRpcConn; infer_instance

/-- A reader keeps its token and learns that what it read was written (`recvTok_sentLb`). -/
theorem recvTok_keep_sentLb (cn : Nat) (s s' : Bool) (hs : s' = !s) (P : Proto GF) (R : List w8) :
    recvTok (Gg := Gg) cn s P R ⊢ recvTok cn s P R ∗ sentLb cn s' R := by
  subst hs
  unfold recvTok recvCore sentLb connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, #Hreg, #Hai, #Hm⟩, %hP, Hr, #Hlb⟩, #Hpp⟩
  isplitl [Hr]
  · iframe Hpp
    iexists γ, Pd, Pa
    iframe He Hreg Hai Hm Hr Hlb
    ipureintro; exact hP
  · iexists γ
    iframe He Hlb

instance rpcAddrP_persistent (W : RpcWorld GF) (a : GoString) (hs hsAns : List w8) :
    Persistent (rpcAddrP (Gg := Gg) W a hs hsAns) := by
  unfold rpcAddrP; infer_instance

instance rpcAddr_persistent (W : RpcWorld GF) (a : GoString) :
    Persistent (rpcAddr (Gg := Gg) W a) := by
  unfold rpcAddr; infer_instance

end proto

end net.rpc
end Perennial
