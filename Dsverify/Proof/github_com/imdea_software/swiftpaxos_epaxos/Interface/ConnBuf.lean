/-
A connection's ends as the marshal layer's buffered streams (notes/dsv-epaxos.md; new, not the
lab's: the lab's harness had its own `net.rpc.connIface` and `bufio.ownWriter`/`ownReader` over
connections). For a `*net.TCPConn` `t` at end `s` of connection `cn` (`net.connAt`):

* `connWr t cn s la ra ed P hP sz`: a `*bufio.Writer` of size `sz` over it, by `net.conn_streamWriterOk`'s
  contract (`sendTok cn s P`, protocol `P cn`, errors `connWriteE`), `P` closed under prefixes;
* `connRd t cn s eof la ra ed P`: a `*bufio.Reader` over it, by `net.conn_readerOk`'s contract
  (reads of a non-empty buffer, `recvTokL cn s P`, errors `connReadE`), with the stream fact
  `▷ protoPrefix P cn` (`recvTokL_proto`, the lab's `recvTok_proto` a step later).

The replica addresses' protocols are closed under prefixes (`repDialP_ppc`, `repAccP_ppc`: the
lab's `repDialP_prefixClosed`/`repAccP_prefixClosed` of `Interface/Replica.lean`, as `Net/`'s
`ProtoPrefixClosed`), so their writers are `connWr`s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Marshal
public import Net.Proof.net.ConnIo
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Client

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem repDialP_ppc (γ : EpNames) (a : GoString) : ProtoPrefixClosed (GF := GF) (repDialP γ a) where
  nil := fun cn => by
    unfold repDialP
    iintro !>
    ileft; ipureintro; rfl
  pre := fun cn x b hxb => by
    obtain ⟨y, rfl⟩ := hxb
    unfold repDialP
    iintro #H
    imodintro
    icases H with (%H | ⟨%r, #Hr, #H⟩)
    · ileft; ipureintro; exact (List.append_eq_nil_iff.mp H).1
    iright
    iexists r
    iframe Hr
    cases r with
    | peer d => iapply peerStreamOk_prefix $$ H
    | client c i =>
      unfold clientDialOk
      icases H with ⟨#Hc, %Hp⟩
      isplitr
      · iexact Hc
      ipureintro
      exact (List.prefix_append x y).trans Hp

theorem repAccP_ppc (γ : EpNames) (a : GoString) : ProtoPrefixClosed (GF := GF) (repAccP γ a) where
  nil := fun cn => by
    unfold repAccP
    iintro !>
    ileft; ipureintro; rfl
  pre := fun cn x b hxb => by
    obtain ⟨y, rfl⟩ := hxb
    unfold repAccP
    iintro #H
    imodintro
    icases H with (%H | ⟨%r, #Hr, #H⟩)
    · ileft; ipureintro; exact (List.append_eq_nil_iff.mp H).1
    iright
    iexists r
    iframe Hr
    cases r with
    | peer d => iapply peerStreamOk_prefix $$ H
    | client c i =>
      unfold clientReplyOk
      icases H with ⟨%o, %v, %ts, #Hf, %Hp⟩
      iexists o, v, ts
      iframe Hf
      ipureintro
      exact ⟨Hp.1, Hp.2.1, (List.prefix_append x y).trans Hp.2.2⟩

end ghost

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics] [π : NetProtoGS]

/-- See the file header. -/
def connWr (t : Loc) (cn : Nat) (s : Bool) (la ra ed : GoInterface) (P : Proto GF)
    (hP : ProtoPrefixClosed P) (sz : Nat) : BufWr GF where
  wi := net.connIface t
  J := sendTok (Gg := hG.goose_globalGS) cn s P
  Q := P cn
  Ew := net.connWriteE la ra ed
  sz := sz
  Q_pre := fun x y => hP.pre cn x (x ++ y) (List.prefix_append x y)

/-- See the file header. -/
def connRd (t : Loc) (cn : Nat) (s : Bool) (eof la ra ed : GoInterface) (P : Proto GF) :
    BufRd GF where
  ri := net.connIface t
  Pre := fun _ m => 0 < m
  S := recvTokL (Gg := hG.goose_globalGS) cn s P
  E := net.connReadE eof la ra ed
  F := fun r => iprop(▷ protoPrefix P cn r)
  F_pers := fun _ => inferInstance
  F_of := fun r => recvTokL_proto cn s P r
  F_pre := fun x y => later_mono (protoPrefix_le (List.prefix_append x y))
  Pre_pos := fun _ _ h => h

/-- A `*bufio.Writer`'s pointer is not nil, keeping the writer (the lab's `ownWriter_not_null`;
`SendMsg`'s `PeerWriters[t] != nil` test). Was a hypothesis; now dsv-bufio-laws'
`bufio.ownBufWriter_not_null`. -/
def BufWriterNotNull : Prop :=
  ∀ (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF)
    (sz : Nat) (sent pend : List w8) (err : GoInterface),
    EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ⊢
      EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗ ⌜bw ≠ null⌝

theorem bufWriterNotNull : BufWriterNotNull (GF := GF) :=
  fun bw wi J Q Ew sz sent pend err =>
    persistent_entails_left (EtcdGrove.bufio.ownBufWriter_not_null bw wi J Q Ew sz sent pend err)

/-- The `net.Conn` `c` is the end `s` of connection `cn` (a `*TCPConn`, `net.isConn`, at some
address; persistent). The lab's `net.rpc.connIface c cn s`. -/
def connIf (c : GoInterface) (cn : Nat) (s : Bool) : IProp GF :=
  iprop(∃ a : GoString, net.isConn c cn s a)

instance connIf_persistent (c : GoInterface) (cn : Nat) (s : Bool) :
    Persistent (connIf (GF := GF) c cn s) := by
  unfold connIf; infer_instance

end conn

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
