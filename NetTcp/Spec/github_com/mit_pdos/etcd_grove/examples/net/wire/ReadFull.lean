/-
`wire.ReadFull(c, buf)` on a `Conn` `c` that is the end `s` of the TCP connection `cn`, whose
reads the caller makes through the reader predicate `P` (`P r`: `r` bytes of the other end's read
so far), with a prefix `sent0` of the other end's bytes of that length (`tcpOutLb`): `c.Read`s
into the rest of `buf` until it is full or a read fails or meets EOF. Each `Read` takes the end's
state through the caller's accessor (persistent: it is used once per `Read`), which opens the end
at its read position and closes it at whatever state and position the read leaves: a thread that
owns its end has `P r := ∃ st, tcpEnd .. st r` (`ReadFull.owned`); ends shared between threads
(a reader and a writer goroutine) keep the end in an invariant and `P` the reader's share of its
position.

It returns `true` only with `buf` full: `buf` then holds the `len(buf)` bytes that follow the `r`
already read in what the other end has written (`tcpOutLb` of `sent`, with `sent.drop r` the
buffer's bytes). Whatever it returns, the caller has `P` of the position the reads reached, and
`buf` has its length. Proved in
`NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/net/wire/ReadFull.lean`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev ReadFull.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (buf : GoSlice) (bs0 : List w8)
    (P : Nat → IProp GF) (r : Nat) (sent0 : GoString) (eof : GoInterface),
  sent0.length = r →
  {{ net.isConn (GF := GF) c cn s a ∗ buf ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗ P r ∗
      tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent0 ∗
      □ (∀ r, P r -∗ |={⊤,∅}=> ∃ st, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
        ∀ st' r', tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' r' ={∅,⊤}=∗
          P r') }}
    (App (App (Val (@! wire.ReadFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (r' : Nat) (bs' : List w8), P r' ∗ buf ↦* bs' ∗
      ⌜bs'.length = bs0.length⌝ ∗
      if ok then ∃ sent : GoString,
        tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent ∗
        ⌜r' = r + bs0.length ∧ sent.length = r' ∧ sent.drop r = bs'⌝
      else True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
