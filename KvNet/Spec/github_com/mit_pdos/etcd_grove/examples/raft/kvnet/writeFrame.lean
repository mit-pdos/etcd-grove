/-
`writeFrame(c, body)` (wire.go): `writeAll` of the frame of `body`, its length (8 bytes,
little-endian) then `body` (`putB xs`, what `putBytes` writes), on a `Conn` `c` that is the end
`s` of the TCP connection `cn` (`8 + len(body)` a Go `int`: the premise on `xs`'s length).
Byte-level, as `writeAll.spec` at the frame's bytes: the caller's
writer predicate `P` and accessor are over `putB xs`. `body` is read only, and given back.

It returns `true` only with the whole frame written.
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev writeFrame.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (body : GoSlice) (xs : List w8)
    (dq : DFrac) (ed : GoInterface) (P : List w8 → Option NetErr → IProp GF),
  (xs.length : Int) + 8 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      net.isConn (GF := GF) c cn s a ∗ body ↦*{dq} xs ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] none ∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = putB xs⌝ -∗ P w none -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
          ∀ k res d', ⌜WriteOutcome st d rs k res d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗
              P (w ++ rs.take k) res) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.writeFrame)) (Val #c))
      (Val #body))
  {{ (ok : Bool), RET #ok; ∃ (w : List w8) (res : Option NetErr), P w res ∗ body ↦*{dq} xs ∗
      ⌜w <+: putB xs ∧ (ok = true → w = putB xs)⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
