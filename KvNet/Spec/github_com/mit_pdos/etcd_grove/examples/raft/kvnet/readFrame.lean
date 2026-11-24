/-
`readFrame(c)` (wire.go) on a `Conn` `c` that is the end `s` of the TCP connection `cn`: reads a
frame, its length (8 bytes, little-endian, `readFull`), refuses a length past `maxFrame` (`2^26`),
then reads that many bytes (`readFull`) into a fresh slice. Byte-level, as `readFull.spec`: the
caller makes the reads through a reader predicate `P got` (`got`: all the bytes this call has
read) and an accessor (persistent, used once per `Read`).

It returns `true` only with a whole frame read, `got = putB l` (what `writeFrame` writes for a body
`l`, `l` at most `2^26` bytes), and the fresh slice holding `l`. Whatever it returns, the caller has
`P got`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev readFrame.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (P : List w8 → IProp GF)
    (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      net.isConn (GF := GF) c cn s a ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got)) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFrame)) (Val #c))
  {{ (b : GoSlice) (ok : Bool), RET (PairV #b #ok); ∃ (got : List w8), P got ∗
      (⌜ok = false⌝ ∨
        ∃ (l : List w8), ⌜ok = true ∧ got = putB l ∧ l.length ≤ 2 ^ 26⌝ ∗ b ↦* l) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
