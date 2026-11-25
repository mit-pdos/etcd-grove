-- The copy for the part `KvRaft/` of `WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/tryWrite.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`examples/lib/durable.tryWrite(name, data)` over `fsExt` (the part `LinuxFs/`, W4c U2), `Write`'s one
attempt (unexported). The file `f` (`DurFs.DFile`), its crash invariant, the caller's handle at the
physical state `p` (`DurFs.durHandleP`), whose facts hold of some state (`DurOk`, read off the invariant
by the caller), `data` shorter than `2^63` (any slice's), `os`'s and `filepath`'s package facts, a fraction of the call
permission, and what the `Write` still owes its client (`DurFs.durWOwe`: both updates, or, after an
earlier attempt's rename, the second). The first update commits at the rename that makes the name hold
`data`; the second at a step after the directory's sync. It returns `true` with the second committed
(its `Ψ`), the handle at a physical state with no rename to lose (`alt = none`); `false` with the
handle at some physical state and what is still owed there. Lean-first (no Rocq counterpart).
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
abbrev github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite.spec : Prop :=
  ∀ (γ : DurGS) (f : DFile) (R : Roots) (qc : Qp) (p : DurPhys) (data : GoString) (Ψ : IProp GF),
  f.Ok → data.length < 2 ^ 63 → (∃ s, DurOk f s p) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ isPkgInit (PROP := IProp GF) pkg_id.path.filepath ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ durInv (GF := GF) γ f ∗
      durHandleP (GF := GF) γ f R p ∗ osCallPerm (GF := GF) (callKey R f.d) qc ∗ durWOwe (GF := GF) γ f data p Ψ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.tryWrite)) (Val #f.name))
      (Val #data))
  {{ (ok : Bool), RET #ok; osCallPerm (callKey R f.d) qc ∗ ∃ p' : DurPhys, durHandleP γ f R p' ∗
      ((⌜ok = true ∧ p'.alt = none⌝ ∗ Ψ) ∨ (⌜ok = false⌝ ∗ durWOwe γ f data p' Ψ)) }}

end spec

end EtcdGrove
end Perennial
