-- The copy for the part `KvRaft/` of `WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/Write.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`examples/lib/durable.Write(name, data)` over `fsExt` (the part `LinuxFs/`, W4c U2; the main tree's is
the `durableExt` model's, one atomic step). The file `f` (`DurFs.DFile`), with its crash invariant and
the caller's handle on it, a fraction of the call permission, and `data` of any length a Go
slice has (`WriteAt`'s chunked loop, `WriteAt.specLong`; until 2026-11-22 at most 1 GiB). Two atomic updates on the client's half of the state (`DurFs.durSt`), because a crash
between the rename and the directory's sync may keep either contents:
* the first at the rename that makes the file hold `data`: `cur := data`, and `alt` the contents
  before (`alt = none` there: the handle serializes `Write`s, and the invariant knows it);
* the second at the directory's sync that commits the rename: `alt := none`, every crash now keeps
  `data`. In between, a crash keeps `cur`'s or `alt`'s contents (the crash lemma, `durInv_crash`,
  to come: the next unit of the log, `notes/wal-fsext-w4c-plan.md`).
A failed attempt (an error of any call) is retried, as the Go does; the spec covers the executions
that return. Lean-first (no Rocq counterpart).
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
abbrev github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec : Prop :=
  ∀ (γ : DurGS) (f : DFile) (R : Roots) (qc : Qp) (data : GoString), f.Ok →
  data.length < 2 ^ 63 →
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable -∗
    osInv (GF := GF) -∗ osSharedInv (GF := GF) R -∗ durInv (GF := GF) γ f -∗
    durHandle (GF := GF) γ f R -∗ osCallPerm (GF := GF) (callKey R f.d) qc -∗
    (AU <{ ∃∃ s : DurSt, durSt (GF := GF) γ s }> @ durAuMask, ∅
      <{ durSt (GF := GF) γ ⟨some data, some s.cur⟩, COMM
        durWriteSync (GF := GF) γ iprop(durHandle (GF := GF) γ f R -∗ osCallPerm (GF := GF) (callKey R f.d) qc -∗ Φ #()) }>) -∗
    WP (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Write)) (Val #f.name))
      (Val #data)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
