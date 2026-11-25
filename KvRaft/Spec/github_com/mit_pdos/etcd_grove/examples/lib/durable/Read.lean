-- The copy for the part `KvRaft/` of `WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/Read.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`examples/lib/durable.Read(name)` over `fsExt` (the part `LinuxFs/`, W4c U2; the main tree's is the
`durableExt` model's, `Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/Read.lean`, whose shape
this mirrors). The file `f` (`DurFs.DFile`), with its crash invariant and the caller's handle on it
(`DurFs.durInv`, `DurFs.durHandle`, `Proof/.../examples/lib/durable/Defs.lean`) and a fraction
of the call permission: the contents and `true`, or `""` and `false` if there is no such file
(`DurFs.readRes` of the state's `cur`), at an atomic update on the client's half of the state
(`DurFs.durSt`), which keeps it. Lean-first (no Rocq counterpart).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs DurFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

/-- See the file header. -/
abbrev github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec : Prop :=
  ∀ (γ : DurGS) (f : DFile) (R : Roots) (qc : Qp), f.Ok →
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable -∗
    osInv (GF := GF) -∗ osSharedInv (GF := GF) R -∗ durInv (GF := GF) γ f -∗
    durHandle (GF := GF) γ f R -∗ osCallPerm (GF := GF) (callKey R f.d) qc -∗
    (AU <{ ∃∃ s : DurSt, durSt (GF := GF) γ s }> @ durAuMask, ∅
      <{ durSt (GF := GF) γ s, COMM
        (durHandle (GF := GF) γ f R -∗ osCallPerm (GF := GF) (callKey R f.d) qc -∗ Φ (readRes s.cur)) }>) -∗
    WP (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Read)) (Val #f.name))
      {{ Φ }}

end spec

end EtcdGrove
end Perennial
