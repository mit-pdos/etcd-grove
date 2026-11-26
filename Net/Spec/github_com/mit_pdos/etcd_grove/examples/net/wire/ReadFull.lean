/-
`wire.ReadFull(c, buf)` on a `Conn` `c` that is the end `s` of the TCP connection `cn`: `c.Read`s
into the rest of `buf` until it is full or a read fails or meets EOF. The caller makes the reads
through a reader predicate `P got` (`got`: the bytes this call has read so far, the start of
`buf`) and an accessor (persistent: it is used once per `Read`), which opens the end's state and
the direction towards it (`netEnd`, `netDir`) for a `Read` of `m` bytes and closes them at what the
read left (`ReadOutcome`, `GooseLang/Ext/Net/Impl.lean`, D1), giving `P` of the bytes read. A thread
that owns its end and follows the stream protocol of `wire/Stream.lean` uses `wire.readP` and
`wire.read_acc`; ends shared between threads keep them in an invariant.

It returns `true` only with `buf` full of the bytes read (`got = bs'`). Whatever it returns, the
caller has `P got`, `buf` has its length and starts with `got`. Proved in
`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/wire/ReadFull.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

/-- See the file header. -/
abbrev ReadFull.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (buf : GoSlice) (bs0 : List w8)
    (P : List w8 → IProp GF) (eof ed : GoInterface),
  {{ net.isConn (GF := GF) c cn s a ∗ buf ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗ netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗ P (got ++ r.got)) }}
    (App (App (Val (@! wire.ReadFull)) (Val #c)) (Val #buf))
  {{ (ok : Bool), RET #ok; ∃ (got bs' : List w8), P got ∗ buf ↦* bs' ∗
      ⌜bs'.length = bs0.length ∧ got <+: bs' ∧ (ok = true → got = bs')⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
