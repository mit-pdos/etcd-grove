/-
`wire.ReadFull(c, buf)` on a `Conn` `c` that is the end `s` of the TCP connection `cn`, whose
state the caller owns (`tcpEnd`, `r` bytes read so far, and a prefix `sent0` of the other end's
bytes of that length, `tcpOutLb`): `c.Read`s into the rest of `buf` until it
is full or a read fails or meets EOF. It returns `true` only with `buf` full: `buf` then holds the
`len(buf)` bytes that follow the `r` already read in what the other end has written (`tcpOutLb`
of `sent`, with `sent.drop r` the buffer's bytes). Whatever it returns, the end's state is the
caller's again (`tcpEnd`, possibly broken, more bytes read) and `buf` has its length. Proved in
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
    (st : TcpEnd) (r : Nat) (sent0 : GoString) (eof : GoInterface),
  sent0.length = r →
  {{ net.isConn (GF := GF) c cn s a ∗ buf ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
      tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent0 }}
    (App (App (Val (@! wire.ReadFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (st' : TcpEnd) (r' : Nat) (bs' : List w8),
      tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' r' ∗ buf ↦* bs' ∗
      ⌜bs'.length = bs0.length⌝ ∗
      if ok then ∃ sent : GoString,
        tcpOutLb (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) sent ∗
        ⌜st' = st ∧ r' = r + bs0.length ∧ sent.length = r' ∧ sent.drop r = bs'⌝
      else True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
