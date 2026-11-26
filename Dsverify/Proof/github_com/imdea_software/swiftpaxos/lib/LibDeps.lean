/-
The library callees of the kit's library bridges (`lib/Bufio.lean`, `lib/BufioNet.lean`,
`lib/NetLab.lean`, `lib/NetConn.lean`), as hypotheses (CLAUDE.md, "Import tiers": a proof sees its callees through their
specs only), as dsv-epaxos's `EpBufioDeps`/`EpNetDeps`. Each class bundles the specs of one library;
the kit's proofs take it as an instance argument (a section `variable`), and the kit's `Link`
closes it with the libraries' proofs (`lib/LibDepsLinked.lean`: `swiftBufioDeps_holds`,
`swiftNetDeps_holds`, local instances of `examples/swiftnet/Link.lean` and
`TopLevelRobustness.lean`). No `instance` of these classes exists.

* `SwiftBufioDeps`: bufio's `NewWriter`, `Writer.{Flush,WriteByte,Write}`, `NewReader` (`specOk`),
  `Reader.{ReadByte,Read}` (dsv-bufio's specs, `Spec/bufio/`).
* `SwiftNetDeps`: net's `Conn.{Read,Write,Close,RemoteAddr}`, `Dial`, `DialTimeout`, `Listen`, `Listener.Accept`
  (`Net/Spec/net/`).
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
public import Net.Spec.net.DialTimeout
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net

/-- bufio's specs the kit's bufio bridge (`lib/Bufio.lean`) calls (the file header). -/
class SwiftBufioDeps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  newWriter : ∀ [bufio.Assumptions], EtcdGrove.bufio.NewWriter.spec (GF := GF) (hG := hG)
  flush : ∀ [bufio.Assumptions], EtcdGrove.bufio.Writer.Flush.spec (GF := GF) (hG := hG)
  writeByte : ∀ [bufio.Assumptions], EtcdGrove.bufio.Writer.WriteByte.spec (GF := GF) (hG := hG)
  write : ∀ [bufio.Assumptions], EtcdGrove.bufio.Writer.Write.spec (GF := GF) (hG := hG)
  newReaderOk : ∀ [bufio.Assumptions], EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG)
  readByte : ∀ [bufio.Assumptions], EtcdGrove.bufio.Reader.ReadByte.spec (GF := GF) (hG := hG)
  readOk : ∀ [bufio.Assumptions], EtcdGrove.bufio.Reader.Read.specOk (GF := GF) (hG := hG)

/-- net's specs the kit's net bridges (`lib/BufioNet.lean`, `lib/NetLab.lean`, `lib/NetConn.lean`) call (the file
header). -/
class SwiftNetDeps [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  connRead : ∀ [net.Assumptions] , net.Conn.Read.spec (GF := GF) (hG := hG)
  connWrite : ∀ [net.Assumptions] , net.Conn.Write.spec (GF := GF) (hG := hG)
  connClose : ∀ [net.Assumptions] , net.Conn.Close.spec (GF := GF) (hG := hG)
  connRemoteAddr : ∀ [net.Assumptions] ,
    net.Conn.RemoteAddr.spec (GF := GF) (hG := hG)
  dial : ∀ [net.Assumptions] , net.Dial.spec (GF := GF) (hG := hG)
  dialTimeout : ∀ [net.Assumptions] ,
    net.DialTimeout.spec (GF := GF) (hG := hG)
  listen : ∀ [net.Assumptions] , net.Listen.spec (GF := GF) (hG := hG)
  accept : ∀ [net.Assumptions] ,
    net.Listener.Accept.spec (GF := GF) (hG := hG)

end Perennial.github_com.imdea_software.swiftpaxos
