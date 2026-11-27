/-
The library callees of QuePaxa's proxy, replica and kit proofs, as hypotheses (CLAUDE.md, "Import
tiers": a proof sees its callees through their specs only; dsv-epaxos's `Interface/LibDeps.lean`).
Each class bundles the specs of one group; the proofs take it as an instance argument (a section
`variable`), and the linking modules close it with the libraries' proofs (`qpBufioDeps_holds`,
`qpNetDeps_holds`, `qpFmtDeps_holds` in `Proxy/Results.lean` and `examples/quepaxanet/Linked.lean`).
No `instance` of these classes exists: a linking module makes its proof a local instance.

* `QpBufioDeps`: bufio's `Writer.{Flush,WriteByte,Write}`, `Reader.{ReadByte,Read}`, `NewWriter`
  (dsv-bufio's specs, `Spec/bufio/`).
* `QpNetDeps`: net's `Conn.{Write,Close}`, `Dial`, `Listen` (`Net/Spec/net/`).
* `QpFormatIntDeps`: `strconv.FormatInt` (`Spec/strconv/FormatInt.lean`).
* `QpPrintfDeps`: `fmt.Printf` (`Spec/fmt/Printf.lean`).
-/
module

public import Spec.bufio.Writer__Flush
public import Spec.bufio.Writer__WriteByte
public import Spec.bufio.Writer__Write
public import Spec.bufio.Reader__ReadByte
public import Spec.bufio.Reader__ReadOk
public import Spec.bufio.NewWriter
public import Spec.strconv.FormatInt
public import Spec.fmt.Printf
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen

@[expose] public section

noncomputable section

namespace Perennial.raxos

open Iris Iris.BI Net

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-- bufio's specs the proxy and kit proofs call (the file header). -/
class QpBufioDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics]
    [_root_.Perennial.bufio.Assumptions] : Prop where
  flush : EtcdGrove.bufio.Writer.Flush.spec (GF := GF) (hG := hG)
  writeByte : EtcdGrove.bufio.Writer.WriteByte.spec (GF := GF) (hG := hG)
  write : EtcdGrove.bufio.Writer.Write.spec (GF := GF) (hG := hG)
  readByte : EtcdGrove.bufio.Reader.ReadByte.spec (GF := GF) (hG := hG)
  readOk : EtcdGrove.bufio.Reader.Read.specOk (GF := GF) (hG := hG)
  newWriter : EtcdGrove.bufio.NewWriter.spec (GF := GF) (hG := hG)

/-- net's specs the proxy and replica proofs call (the file header). -/
class QpNetDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics] [HasExt netExt]
    [net.Assumptions] : Prop where
  connWrite : net.Conn.Write.spec (GF := GF) (hG := hG)
  connClose : net.Conn.Close.spec (GF := GF) (hG := hG)
  dial : net.Dial.spec (GF := GF) (hG := hG)
  listen : net.Listen.spec (GF := GF) (hG := hG)

/-- `strconv.FormatInt`'s spec (the file header). -/
class QpFormatIntDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics] : Prop where
  formatInt : EtcdGrove.strconv.FormatInt.spec (GF := GF) (hG := hG)

/-- `fmt.Printf`'s spec (the file header). -/
class QpPrintfDeps (GF : BundledGFunctors) [hG : HeapGS .hasLC GF] [go.Semantics]
    [_root_.Perennial.fmt.Assumptions] : Prop where
  printf : EtcdGrove.fmt.Printf.spec (GF := GF) (hG := hG)

end heap

end Perennial.raxos
