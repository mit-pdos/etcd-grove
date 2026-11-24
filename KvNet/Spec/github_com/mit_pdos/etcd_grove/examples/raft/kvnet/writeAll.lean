/-
`writeAll(c, b)` (wire.go) on a `Conn` `c` that is the end `s` of the TCP connection `cn`:
`c.Write`s the rest of `b` until all of it is written or a write fails. Byte-level, as
`net.Conn.Write.spec`: the caller makes the writes' steps through a writer predicate `P w res` (`w`:
the bytes this call has written so far, a prefix of `bs`; `res`: the failure that ended it, if any)
and an accessor (persistent: it is used once per step of every `Write`), which opens the end's
state and the direction from it (`netEnd`, `netDir`) for a step writing a prefix of `rs`, the rest
of `bs` after `w`, and closes them at what the step left (`WriteOutcome`, D1), giving `P` of the
bytes written. No ghost protocol: what the bytes mean to the reader is the caller's (a later layer,
notes/kvnet-proof-plan.md, decision E).

It returns `true` only with all of `bs` written (`w = bs`). Whatever it returns, the caller has
`P w res` and `b` back.
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev writeAll.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (b : GoSlice) (bs : List w8)
    (dq : DFrac) (ed : GoInterface) (P : List w8 → Option NetErr → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      net.isConn (GF := GF) c cn s a ∗ b ↦*{dq} bs ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] none ∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ P w none -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
          ∀ k res d', ⌜WriteOutcome st d rs k res d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗
              P (w ++ rs.take k) res) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.writeAll)) (Val #c))
      (Val #b))
  {{ (ok : Bool), RET #ok; ∃ (w : List w8) (res : Option NetErr), P w res ∗ b ↦*{dq} bs ∗
      ⌜w <+: bs ∧ (ok = true → w = bs)⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
