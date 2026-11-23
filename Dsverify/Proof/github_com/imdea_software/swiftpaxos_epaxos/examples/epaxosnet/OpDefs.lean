/-
`Op`'s spec and the facts of its connection it uses (notes/dsv-epaxos.md; the lab's
`Epaxos/Proof/examples/epaxosnet/OpCore.lean`, its protocol part: `clientDial_ok`,
`repAccP_client`, `replyEnc_prefix`, `reply_nextIs`, `reply_read`).

`Op(addrs, c, in)` (kit.go): client `c` dials the replica address `ServerAddrs()[1 + c mod 5]`
(`replicaAddrs[c mod 5]`), registers the connection as its op (`escrow_register`, with the
dialer's fresh token and the update `opU`), writes the `PROPOSE` tag and its `Propose`
(`proposeBytes c i`), reads a `ProposeReplyTS` (the protocol `repAccP` of a client connection: it
carries `fired γ cid o` and the output's value), claims its escrow (`escrow_claim`) and returns
`outOk o`; on any error it returns `outUnk`, leaving the update with the escrow (which may still
fire).

Changed against the lab: `nextIs` and a reader's stream are a step later (the stream fact of a
connection's reader is `▷ protoPrefix`, `Interface/ConnBuf.lean`), so `reply_read` gives its
witness under a later (`fired` is timeless: the caller strips it); connection ids are `Nat`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.ConnBuf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.KitVals

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
  github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A reply's encoding determines the reply among those with values below `2 ^ 16` bytes (its
length field is exact), also as a prefix. -/
theorem replyEnc_prefix (p q : ProposeReplyV) (hp : p.val.length < 2 ^ 16)
    (hq : q.val.length < 2 ^ 16) (h : p.enc <+: q.enc) : p = q := by
  obtain ⟨t, ht⟩ := h
  rcases p with ⟨pk, pc, pv, pt⟩
  rcases q with ⟨qk, qc, qv, qt⟩
  simp only [ProposeReplyV.enc, encProposeReplyTS, encValue, List.append_assoc,
    List.cons_append, List.cons.injEq] at ht hp hq
  obtain ⟨rfl, ht⟩ := ht
  simp only [List.nil_append] at ht
  obtain ⟨h1, ht⟩ := List.append_inj ht (by simp [u32Le_length])
  obtain ⟨h2, ht⟩ := List.append_inj ht (by simp [u32Le_length])
  have hlen : pv.length = qv.length := by
    have := u32Le_inj h2
    have e1 : (W32 (pv.length % 2 ^ 16 : Nat)).toNat = pv.length := by
      rw [Nat.mod_eq_of_lt hp]; simp; omega
    have e2 : (W32 (qv.length % 2 ^ 16 : Nat)).toNat = qv.length := by
      rw [Nat.mod_eq_of_lt hq]; simp; omega
    rw [← e1, ← e2, this]
  obtain ⟨h3, ht⟩ := List.append_inj ht hlen
  obtain ⟨h4, -⟩ := List.append_inj (ht.trans (List.append_nil _).symm) (by simp [u64Le_length])
  rw [u32Le_inj h1, h3, u64Le_inj h4]

/-- The replica address client `c` dials: `ServerAddrs()[1 + c mod NReplicas]`. -/
def opAddr (c : w64) : GoString := replicaAddrs.getD (uint.nat (c % W64 5)) []

theorem opAddr_idx (c : w64) :
    0 ≤ sint.Z (W64 1 + c % W64 5) ∧ sint.Z (W64 1 + c % W64 5) < 6 ∧
      serverAddrs[(sint.Z (W64 1 + c % W64 5)).toNat]? = some (opAddr c) ∧
      replicaAddrs[uint.nat (c % W64 5)]? = some (opAddr c) := by
  have h5 : uint.nat (c % W64 5) < 5 := by word
  have hz : sint.Z (W64 1 + c % W64 5) = 1 + uint.nat (c % W64 5) := by word
  refine ⟨by omega, by omega, ?_⟩
  rw [hz]
  unfold opAddr
  have : (1 + (uint.nat (c % W64 5) : Int)).toNat = 1 + uint.nat (c % W64 5) := by omega
  rw [this]
  generalize uint.nat (c % W64 5) = k at h5 ⊢
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with h | h | h | h | h <;>
    subst h <;> simp [serverAddrs, replicaAddrs]

/-- An output of the input's kind: a put's `done`, a get's `got`, a scan's `scanned`. -/
def outShape : KvI → KvO → Prop
  | .put _ _, o => o = .done
  | .get _, o => ∃ x, o = .got x
  | .scan _ _, o => ∃ x, o = .scanned x

theorem kvStep_shape (i : KvI) (σ : KvS) : outShape i (kvStep i σ).2 := by
  cases i <;> simp [outShape, kvStep]

/-- A get's or a scan's reply value `v` of an output `o` of its kind is `o`'s answer. -/
theorem outBytes_read (o : KvO) (v : List w8) (hs : (∃ x, o = .got x) ∨ ∃ x, o = .scanned x)
    (hv : replyValOk o v) : examples.epaxosnet.outBytes o = v := by
  rcases hs with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rcases x with _ | x <;> simp_all [replyValOk, examples.epaxosnet.outBytes]
  · simp_all [replyValOk, examples.epaxosnet.outBytes]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The update of input `i` with its postcondition strengthened by the output's shape: what `Op`
deposits in its escrow (the escrow keeps only the postcondition: `fired` does not say that its
output is the input's kind, which `Op` needs to tell a put's answer from a read's). -/
theorem opU_shape (γ : EpNames) (i : KvI) (Φ : KvO → IProp GF) :
    opU γ i Φ ⊢ opU γ i (fun o => iprop(Φ o ∗ ⌜outShape i o⌝)) := by
  unfold opU
  dsimp only
  iintro HU
  imod HU with ⟨%σ, Hs, Hc⟩
  imodintro
  iexists σ
  iframe Hs
  iintro Hs
  imod Hc $$ Hs with HΦ
  imodintro
  iframe HΦ
  ipureintro; exact kvStep_shape i σ

instance fired_timeless (γ : EpNames) (cid : Nat) (o : KvO) :
    Timeless (fired (GF := GF) γ cid o) := by
  unfold fired escrowNames; infer_instance

/-- What a client op writes (a prefix of its proposal) meets its connection's protocol. -/
theorem clientDial_ok (γ : EpNames) (a : GoString) (cid : Nat) (c : w64) (i : KvI)
    (bs : List w8) (h : bs <+: proposeBytes c i) :
    clientConn (GF := GF) γ cid c i ⊢ repDialP γ a cid bs := by
  iintro #Hc
  unfold repDialP
  iright
  iexists ConnRole.client c i
  isplitr
  · unfold clientConn; icases Hc with ⟨-, #Hr, -⟩; iexact Hr
  dsimp only
  unfold clientDialOk
  iframe Hc
  ipureintro; exact h

/-- On a client connection, the acceptor's protocol is the reply's. -/
theorem repAccP_client (γ : EpNames) (a : GoString) (cid : Nat) (c : w64) (i : KvI)
    (bs : List w8) :
    clientConn (GF := GF) γ cid c i -∗ repAccP γ a cid bs -∗ ⌜bs = []⌝ ∨ clientReplyOk γ cid bs := by
  iintro #Hc HP
  unfold repAccP
  icases HP with (%h | ⟨%r, #Hr, Hm⟩)
  · ileft; ipureintro; exact h
  unfold clientConn
  icases Hc with ⟨-, #Hr2, -⟩
  unfold roleElem
  ihave %Heq := ghostMapElem_agree $$ Hr Hr2
  subst Heq
  iright
  iexact Hm

/-- What the acceptor has written on a client connection continues with a prefix of a reply. -/
theorem reply_proto (γ : EpNames) (a : GoString) (cid : Nat) (c : w64) (i : KvI)
    (S : List w8) :
    clientConn (GF := GF) γ cid c i -∗ protoPrefix (repAccP γ a) cid S -∗
      ⌜∃ (v : ProposeReplyV) (ext : List w8), v.val.length < 2 ^ 16 ∧ S <+: v.enc ++ ext⌝ := by
  iintro #Hc #Hp
  have hnil : ∃ (v : ProposeReplyV) (ext : List w8), v.val.length < 2 ^ 16 ∧
      ([] : List w8) <+: v.enc ++ ext :=
    ⟨⟨W8 0, W32 0, [], W64 0⟩, [], by simp, List.nil_prefix⟩
  unfold protoPrefix
  icases Hp with (%h | ⟨%ext, %hS, #HP⟩)
  · ipureintro; subst h; exact hnil
  icases repAccP_client $$ Hc HP with (%h | Hr)
  · ipureintro; subst h; rw [List.prefix_nil.1 hS]; exact hnil
  unfold clientReplyOk
  icases Hr with ⟨%o, %v, %ts, -, %Hv⟩
  ipureintro
  refine ⟨⟨okTRUE, W32 0, v, ts⟩, [], Hv.2.1, ?_⟩
  simp only [List.append_nil]
  exact hS.trans Hv.2.2

/-- What the acceptor has written on a client connection, a whole reply, is the fired output's. -/
theorem reply_fired (γ : EpNames) (a : GoString) (cid : Nat) (c : w64) (i : KvI)
    (p : ProposeReplyV) (hp : p.val.length < 2 ^ 16) :
    clientConn (GF := GF) γ cid c i -∗ protoPrefix (repAccP γ a) cid p.enc -∗
      ∃ o, fired γ cid o ∗ ⌜p.ok = okTRUE ∧ p.cmdId = W32 0 ∧ replyValOk o p.val⌝ := by
  iintro #Hc #Hp
  unfold protoPrefix
  have hne : p.enc ≠ [] := by simp [ProposeReplyV.enc, encProposeReplyTS]
  icases Hp with (%h | ⟨%ext, %hS, #HP⟩)
  · exact absurd h hne
  icases repAccP_client $$ Hc HP with (%h | Hr)
  · subst h; exact absurd (List.prefix_nil.1 hS) hne
  unfold clientReplyOk
  icases Hr with ⟨%o, %v, %ts, #Hf, %Hv⟩
  have heq := replyEnc_prefix p ⟨okTRUE, W32 0, v, ts⟩ hp Hv.2.1 (hS.trans Hv.2.2)
  subst heq
  iexists o
  iframe Hf
  ipureintro; exact ⟨rfl, rfl, Hv.1⟩

end ghost

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics] [π : NetProtoGS]

/-- What a client op's reader reads continues with a prefix of a reply. -/
theorem reply_nextIs (γ : EpNames) (a : GoString) (t : Loc) (cid : Nat) (c : w64) (i : KvI)
    (eof la ra ed : GoInterface) :
    clientConn (GF := GF) γ cid c i ⊢
      nextIs (connRd t cid false eof la ra ed (repAccP γ a)) [] ProposeReplyV.enc
        (fun p => p.val.length < 2 ^ 16) := by
  iintro #Hc
  unfold nextIs
  imodintro
  iintro %S #Hp
  simp only [connRd]
  inext
  ihave %H := reply_proto γ a cid c i S $$ Hc Hp
  ipureintro
  intro _
  simpa using H

/-- What a client op's reader has read, a whole reply, is the fired output's (a step later). -/
theorem reply_read (γ : EpNames) (a : GoString) (t : Loc) (cid : Nat) (c : w64) (i : KvI)
    (eof la ra ed : GoInterface) (br : Loc) (p : ProposeReplyV) (hp : p.val.length < 2 ^ 16) :
    clientConn (GF := GF) γ cid c i -∗
      rdOwn br (connRd t cid false eof la ra ed (repAccP γ a)) p.enc -∗
      rdOwn br (connRd t cid false eof la ra ed (repAccP γ a)) p.enc ∗
        ▷ ∃ o, fired γ cid o ∗ ⌜p.ok = okTRUE ∧ p.cmdId = W32 0 ∧ replyValOk o p.val⌝ := by
  iintro #Hc Hr
  ihave ⟨Hr, #Hp⟩ := EtcdGrove.bufio.ownBufReader_fact _ _ _ _ _ _ _
    (connRd t cid false eof la ra ed (repAccP γ a)).F_of
    (connRd t cid false eof la ra ed (repAccP γ a)).F_pre $$ Hr
  iframe Hr
  simp only [connRd]
  inext
  iapply reply_fired γ a cid c i p hp $$ Hc Hp

end conn

namespace examples.epaxosnet

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions]

/-- **`Op(addrs, c, in)`** (see the file header): from the server addresses (read-only), the
replicas' shared facts (`clientInvs`: the addresses' protocols and the role registry) and the
update of input `i` (remote's `lin`, `opU`), it returns `outUnk` or `outOk o` with the update's
postcondition of `o`. -/
def Op.spec : Prop :=
  ∀ (γ : EpNames) (sl : GoSlice) (c : w64) (i : KvI) (Φ : KvO → IProp GF),
  inPre i → uint.nat c < 10 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet ∗
      sl ↦*□ serverAddrs ∗ clientInvs γ ∗ opU γ i Φ }}
    (App (App (App (Val (@! examples.epaxosnet.Op)) (Val #sl)) (Val #c)) (Val #(inOf i)))
  {{ (o : Out), RET #o; ⌜o = outUnk⌝ ∨ ∃ r, ⌜o = outOk r⌝ ∗ Φ r }}

end spec

end examples.epaxosnet

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
