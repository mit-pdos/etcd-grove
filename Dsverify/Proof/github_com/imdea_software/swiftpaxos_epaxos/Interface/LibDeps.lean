/-
The library callees of the wire and replica proofs, as hypotheses (CLAUDE.md, "Import tiers": a
proof sees its callees through their specs only). Each class bundles the specs of one group; the
proofs take it as an instance argument (a section `variable`), and the `Link` modules close it with
the libraries' proofs (`wire/Link.lean`: `epBufioDeps_holds`; `replica/Link.lean`:
`epNetDeps_holds`, `epReplicaDeps_holds`). No `instance` of these classes exists: a `Link` passes
its proof as a local hypothesis.

* `EpBufioDeps`: bufio's `Writer.{Flush,WriteByte,Write}`, `Reader.{ReadByte,Read}`, `NewReader`,
  `NewWriter` (dsv-bufio's specs, `Spec/bufio/`).
* `EpNetDeps`: net's `Conn.{Read,Write,Close,RemoteAddr}`, `Dial`, `Listen`, `Listener.Accept`
  (`Net/Spec/net/`).
* `EpReplicaDeps`: the kit's own `rpc.NewTableId`, `rpc.Table.Get` (`Interface/RpcTable.lean`,
  proved in `replica/RpcTable.lean`) and `io.ReadFull` over a connection (`ioReadFullPre.spec`,
  proved in `replica/IoReadFull.lean`).
-/
module

public import Spec.bufio.Writer__Flush
public import Spec.bufio.Writer__WriteByte
public import Spec.bufio.Writer__Write
public import Spec.bufio.Reader__ReadByte
public import Spec.bufio.Reader__ReadOk
public import Spec.bufio.NewReaderOk
public import Spec.bufio.NewWriter
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__RemoteAddr
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcTable
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.IoReadFullPre

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Net

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-- bufio's specs the wire and replica proofs call (the file header). -/
class EpBufioDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics]
    [bufio.Assumptions] : Prop where
  flush : EtcdGrove.bufio.Writer.Flush.spec (GF := GF) (hG := hG)
  writeByte : EtcdGrove.bufio.Writer.WriteByte.spec (GF := GF) (hG := hG)
  write : EtcdGrove.bufio.Writer.Write.spec (GF := GF) (hG := hG)
  readByte : EtcdGrove.bufio.Reader.ReadByte.spec (GF := GF) (hG := hG)
  readOk : EtcdGrove.bufio.Reader.Read.specOk (GF := GF) (hG := hG)
  newReaderOk : EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG)
  newWriter : EtcdGrove.bufio.NewWriter.spec (GF := GF) (hG := hG)

/-- net's specs the replica proofs call (the file header). -/
class EpNetDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics] [HasExt netExt]
    : Prop where
  connRead : net.Conn.Read.spec (GF := GF) (hG := hG)
  connWrite : net.Conn.Write.spec (GF := GF) (hG := hG)
  connClose : net.Conn.Close.spec (GF := GF) (hG := hG)
  connRemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG)
  dial : net.Dial.spec (GF := GF) (hG := hG)
  listen : net.Listen.spec (GF := GF) (hG := hG)
  accept : net.Listener.Accept.spec (GF := GF) (hG := hG)

/-- The kit's own callees of the replica proofs proved in proof modules (the file header). -/
class EpReplicaDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics]
    [epaxos.Assumptions] [io.Assumptions] : Prop where
  newTableId : rpc.NewTableId.spec (GF := GF)
  tableGet : rpc.Table.Get.spec (GF := GF)
  readFull : ioReadFullPre.spec (GF := GF) (hG := hG)

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
