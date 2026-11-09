/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.replicate(i, v, t)`: `Replicate(i, v, t)`'s `log'`, on a clone being built.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `s.replicate(i, val, typ)` on a clone being built, of a server of the state: `replicate i w typ`
(a new log: the old one is shared, never written in place); server `i` is then a copy being written.
-/
abbrev State.replicate.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (i : w64) (gv : G.Value) (w : Value) (typ : EntryType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ valueRO gv w ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"replicate")) (Val #i)) (Val #gv)) (Val #(match typ with | .value => W8 0 | .config => W8 1 : w8)))
  {{ RET #(); stateOwn p (st.replicate (uint.nat i) w typ) (uint.nat i :: M) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
