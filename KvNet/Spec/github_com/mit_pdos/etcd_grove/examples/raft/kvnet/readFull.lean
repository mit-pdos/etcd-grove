/-
`readFull(c, b)` (wire.go) on a `Conn` `c` that is the end `s` of the TCP connection `cn`:
`c.Read`s into the rest of `b` until it is full, or a read returns no byte with an error (EOF, a
failure). Byte-level, as Net's `wire.ReadFull` (`Net/Spec/.../wire/ReadFull.lean`), whose loop it
is but for re-slicing `b` and stopping only on `n == 0 && err != nil`: the caller makes the reads
through a reader predicate `P got` (`got`: the bytes this call has read so far, the start of `b`)
and an accessor (persistent: it is used once per `Read`), which opens the end's state and the
direction towards it (`netEnd`, `netDir`) for a `Read` of `m` bytes and closes them at what the
read left (`ReadOutcome`, D1), giving `P` of the bytes read. No ghost protocol (a later layer,
notes/kvnet-proof-plan.md, decision E).

It returns `true` only with `b` full of the bytes read (`got = bs'`). Whatever it returns, the
caller has `P got`, `b` has its length and starts with `got`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base

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
abbrev readFull.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (b : GoSlice) (bs0 : List w8)
    (P : List w8 → IProp GF) (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      net.isConn (GF := GF) c cn s a ∗ b ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got)) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.readFull)) (Val #c))
      (Val #b))
  {{ (ok : Bool), RET #ok; ∃ (got bs' : List w8), P got ∗ b ↦* bs' ∗
      ⌜bs'.length = bs0.length ∧ got <+: bs' ∧ (ok = true → got = bs')⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
