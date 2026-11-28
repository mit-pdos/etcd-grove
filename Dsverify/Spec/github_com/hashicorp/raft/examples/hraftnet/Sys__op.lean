/-
`hraftnet.Sys.op`'s spec (the hraft kit's clients, notes/dsv-hraft.md, S5f).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ClientDeps

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : Net.NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable [rpcsem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `s.op(x)` (input `i`), client `c = s.c` below 256, its count `s.seq` with `s.seq + 1 < 2^56`: the
operation's update `slotUpd` (and its call's counter `seqOwn` at `s.seq + 1`) for an output with `Φ` of
it or the unknown output; the count moved by one, the server tried first still a server. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.Sys.op.spec : Prop :=
  ∀ (K : HK GF) (s : Loc) (sv : Sys) (i : HIn) (Φ : HOut → IProp GF),
    uint.nat sv.c' < 256 → uint.nat sv.seq' + 1 < 2 ^ 56 → 1 ≤ uint.nat sv.j' → uint.nat sv.j' ≤ 6 →
    {{ cliEnv K ∗ s ↦ sv ∗ sysConns K sv.conns' ∗ idInv K.g ∗
        seqOwn K.g (uint.nat sv.c') (uint.nat sv.seq' + 1) ∗
        github_com.mit_pdos.etcd_grove.examples.lib.remote.slotUpd (Gg := hG.goose_globalGS) (regR K.g.st) i Φ }}
      (App (Val (s @!! go.GoType.PointerType Sys.ty @!! go!"op")) (Val #(inS i)))
    {{ (o : Out), RET #o; (∃ sv' : Sys, s ↦ sv' ∗ ⌜sv'.c' = sv.c' ∧ sv'.conns' = sv.conns' ∧
          sv'.seq' = sv.seq' + W64 1 ∧ 1 ≤ uint.nat sv'.j' ∧ uint.nat sv'.j' ≤ 6⌝) ∗
        seqOwn K.g (uint.nat sv.c') (uint.nat sv.seq' + 2) ∗ outRes Φ o }}

end spec

end Perennial
