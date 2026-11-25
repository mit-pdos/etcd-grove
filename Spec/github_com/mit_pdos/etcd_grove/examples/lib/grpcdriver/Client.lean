/- Lean-first (no Rocq counterpart).

`Client()`: the client's program (`grpcdriver.go`); it returns its thread's token (its checks never
panic). It runs against the server registered at `drvAddr` (`grpcAddrAt` with the driver's table
`drvSvc γid`), whose ids' ghost map `γid` it owns (empty: it makes the ids), with at most `2 ^ 31`
threads (its wait group's `tokJoin`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- See the file header. -/
abbrev Client.spec : Prop :=
  ∀ [hX : HasExt netExt] (π : NetProtoGS) (σ : NetSlotGS) (γid : GName),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ threadTok ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) drvAddr (drvSvc γid) ∗
      ghostMapAuth (K := w64) (V := Unit) γid 1 ∅ }}
    (App (Val (@! Client)) (Val #()))
  {{ RET #(); threadTok }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
