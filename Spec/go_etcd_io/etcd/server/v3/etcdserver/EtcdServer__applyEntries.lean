/-
`(*EtcdServer).applyEntries(ep, apply)` (server.go): the committed entries of a `toApply`,
from the next unapplied one. Lean-first (no Rocq counterpart); see `InvApplier.lean`,
`InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.applyEntries(ep, ap)`, by the apply thread: the entries of `ap` (consecutive from
`f0`, with no gap after the applied index `ep.appliedi = ai`, as raft hands them over) from
`ai + 1` on are applied (`apply`), and `ep.appliedi`, `ep.appliedt` advance to the last; the
apply thread's relation `loopOk` (processed through the larger of `ci` and the applied
index) is kept. **The KV** (the apply package's unit 3): the apply thread's applier state goes
from `x` to `x'` by `entriesStep c (unapplied ai ms) x x'`, `c` the consistent index at the
start (`ciEff γ st.k`), under `entriesOk c (unapplied ai ms) x`, and `batchWaitOk` of the
batch (unit 2 of the request path: the wait's premise, see `apply`). -/
abbrev EtcdServer.applyEntries.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → entriesOk (ciEff γ st.k) (unapplied ai ms) x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfStateAddr ep ↦ cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗
      srvApplyKV s E x }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #();
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs' ∗
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' t' ∗ srvLgReader s ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)⌝ }}

end spec

end EtcdGrove
end Perennial
