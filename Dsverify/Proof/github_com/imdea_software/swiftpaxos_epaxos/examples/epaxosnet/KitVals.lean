/-
The kit's Go values of the store's inputs and outputs (`model.go`'s `In`, `Out`), shared by the
model's proofs (`Kit.lean`, remote's `RBase`) and `Op`'s (`OpDefs.lean`): an input `i : KvI` is
`inOf i` (`In{Op, K, N, V}`: `OpPut` 0, `OpGet` 1, `OpScan` 2); an output `o : KvO` is answered as
`Out{V: outBytes o}` (a put's success and a get of a missing key are both `""`: SwiftPaxos's
replies do not tell them apart, nor an empty scan).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Client

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

variable [GooseExts]

/-- An input's `In` (kit.go's `Gen`: a put `In{OpPut, k, 0, v}`, a get `In{OpGet, k, 0, ""}`, a
scan of `n` from `k` `In{OpScan, k, n, ""}`). -/
def inOf : KvI → In
  | .put k v => In.mk (W8 0) k (W64 0) v
  | .get k => In.mk (W8 1) k (W64 0) []
  | .scan k n => In.mk (W8 2) k n []

/-- An output's `Out.V`: a get's value (`""` if none), a scan's concatenation, a put's `""`. -/
def outBytes : KvO → GoString
  | .got none => []
  | .got (some v) => v
  | .done => []
  | .scanned v => v

/-- An answered output. -/
def outOk (o : KvO) : Out := Out.mk false (outBytes o)

/-- An unknown outcome (`Out{Unknown: true}`). -/
def outUnk : Out := Out.mk true []

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
