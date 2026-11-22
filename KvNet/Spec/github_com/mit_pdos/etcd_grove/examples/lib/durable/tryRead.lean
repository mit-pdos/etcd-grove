-- The copy for the part `KvNet/` of `WalTester/Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/tryRead.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`examples/lib/durable.tryRead(name)` over `fsExt` (the part `LinuxFs/`, W4c U2), `Read`'s one attempt
(unexported). The file `f` (`DurFs.DFile`), the caller's handle at the physical state `p`
(`DurFs.durHandleP`), whose facts hold of some state (`DurOk`, read off the invariant by the caller),
`os`'s package fact (for `os.ErrNotExist`) and a fraction of the call permission. When `done` is true,
`(s, ok)` is `("", false)` if the name holds no file, and the contents and `true` if it holds one
(`DurPhys.CurIs`). Nothing changes. Lean-first (no Rocq counterpart).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.PkgInit

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
abbrev github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead.spec : Prop :=
  ∀ (γ : DurGS) (f : DFile) (R : Roots) (qc : Qp) (p : DurPhys), f.Ok → (∃ s, DurOk f s p) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗
      durHandleP (GF := GF) γ f R p ∗ osCallPerm (GF := GF) (callKey R f.d) qc }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead)) (Val #f.name))
  {{ (str : GoString) (ok done : Bool), RET (PairV (PairV #str #ok) #done);
      durHandleP γ f R p ∗ osCallPerm (callKey R f.d) qc ∗
      ⌜done = true → ∃ v, p.CurIs f v ∧ str = v.getD [] ∧ ok = v.isSome⌝ }}

end spec

end EtcdGrove
end Perennial
