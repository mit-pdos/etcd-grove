/-
`hraftnet.Sys.try`'s spec (the hraft kit's clients, notes/dsv-hraft.md, S5f).
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

/-- `s.try(j, cmd, x)`, `1 ≤ j ≤ 6`, the command `cmd` of the operation on `x` (input `i`): one attempt
at server `j`. Final: an output with `Φ` of it, or the unknown output; not final: the operation's state
back (no effect, or not sent). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.Sys.try.spec : Prop :=
  ∀ (K : HK GF) (s : Loc) (sv : Sys) (j : w64) (cmd : GoSlice) (d : List w8) (i : HIn)
    (Φ : HOut → IProp GF),
    1 ≤ uint.nat j → uint.nat j ≤ 6 → datumOf i d → d.length ≤ 1000 →
    {{ cliEnv K ∗ s ↦ sv ∗ sysConns K sv.conns' ∗ cmd ↦*□ d ∗ opSt K d i Φ ∗ readUpd K i Φ }}
      (App (App (App (Val (s @!! go.GoType.PointerType Sys.ty @!! go!"try")) (Val #j)) (Val #cmd))
        (Val #(inS i)))
    {{ (o : Out) (fin : Bool), RET (PairV #o #fin); s ↦ sv ∗
        (if fin then outRes Φ o else opSt K d i Φ) }}

end spec

end Perennial
