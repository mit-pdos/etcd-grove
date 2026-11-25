/-
The kit's library hypotheses (`lib/LibDeps.lean`: `SwiftBufioDeps`, `SwiftNetDeps`), closed by the
libraries' proofs (dsv-bufio's `Proof/bufio/`, `Net/Proof/net/`). Local instances of the kit's top
modules (`examples/swiftnet/Link.lean`, `TopLevelRobustness.lean`); no `instance` of them exists.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibDeps
public import Proof.bufio.NewWriter
public import Proof.bufio.NewWriterSize
public import Proof.bufio.NewWriterSizeRep
public import Proof.bufio.Writer__Flush
public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Write
public import Proof.bufio.NewReaderOk
public import Proof.bufio.NewReaderSize
public import Proof.bufio.Reader__ReadByte
public import Proof.bufio.Reader__ReadOk
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__RemoteAddr
public import Net.Proof.net.Dial
public import Net.Proof.net.DialTimeout
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Proof.bufio.NewWriterSizeRep

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]

theorem swiftBufioDeps_holds : SwiftBufioDeps GF where
  newWriter := EtcdGrove.bufio.NewWriter.wp_proof
      (EtcdGrove.bufio.NewWriterSize.wp_proof EtcdGrove.bufio.NewWriterSize.wp_proofRep)
  flush := EtcdGrove.bufio.Writer.Flush.wp_proof
  writeByte := EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
  write := EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof
  newReaderOk := EtcdGrove.bufio.NewReader.wp_proofOk
    (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE)
  readByte := EtcdGrove.bufio.Reader.ReadByte.wp_proof
  readOk := EtcdGrove.bufio.Reader.Read.wp_proofOk

theorem swiftNetDeps_holds [HasExt netExt] : SwiftNetDeps GF where
  connRead := net.Conn.Read.wp_proof
  connWrite := net.Conn.Write.wp_proof
  connClose := net.Conn.Close.wp_proof
  connRemoteAddr := net.Conn.RemoteAddr.wp_proof
  dial := net.Dial.wp_proof
  dialTimeout := net.DialTimeout.wp_proof
  listen := net.Listen.wp_proof
  accept := net.Listener.Accept.wp_proof

end heap

end Perennial.github_com.imdea_software.swiftpaxos
