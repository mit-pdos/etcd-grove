/-
`writeFrame(c, body)` (wire.go): `writeAll` of the frame of `body`, its length (8 bytes,
little-endian) then `body` (`putB xs`, what `putBytes` writes), on a `Conn` `c` that is the end
`s` of the TCP connection `cn`. A body longer than `maxFrame` (`2^26`, which `readFrame` refuses) is
not written: `false`, nothing written (2026-11-22, the coordinator's option (a): no length premise).
Byte-level, as `writeAll.spec` at the frame's bytes: the caller's
writer predicate `P` and accessor are over `putB xs`. `body` is read only, and given back.

It returns `true` only with the whole frame written.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev writeFrame.spec : Prop :=
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (body : GoSlice) (xs : List w8)
    (dq : DFrac) (ed : GoInterface) (P : List w8 → Option NetErr → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      net.isConn (GF := GF) c cn s a ∗ body ↦*{dq} xs ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] none ∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = putB xs⌝ -∗ P w none -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
          ∀ k res d', ⌜WriteOutcome st d rs k res d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗
              P (w ++ rs.take k) res) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.writeFrame)) (Val #c))
      (Val #body))
  {{ (ok : Bool), RET #ok; ∃ (w : List w8) (res : Option NetErr), P w res ∗ body ↦*{dq} xs ∗
      ⌜w <+: putB xs ∧ (ok = true → w = putB xs) ∧ (67108864 < xs.length → w = [])⌝ }}

end spec

end kvraft
end EtcdGrove
end Perennial
