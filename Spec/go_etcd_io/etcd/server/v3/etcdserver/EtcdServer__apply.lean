/-
`(*EtcdServer).apply(es, ep, raftAdvancedC)` (server.go): the apply loop over a batch of
committed entries. Lean-first (no Rocq counterpart); see `InvApplier.lean`, `InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach

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

/-- `s.apply(es, ep, rac)`, by the apply thread, on a non-empty batch of consecutive
committed entries from `f0` (`entriesFrom`), with the protocol's state `st` processed through
the larger of `ci` and `f0 - 1` (`loopOk`): each entry at or below `ci` is replayed with no
backend writes (`ApplyV2storeOnly`), each above is applied (`ApplyBoth`), and afterwards
`ci` and the processed-through index are both the larger of the old `ci` and the last index
`L`, which it returns with its term. So no entry's writes are applied twice, and none above
`ci` is skipped. **The KV** (the apply package's unit 3): the apply thread's applier state goes
from `x` to `x'` by `entriesStep c ms x x'` (`c` the consistent index the batch starts at: each
normal entry applied by `apply.Apply`, with `v3` iff above `c`), under `entriesOk c ms x` (each
normal entry's premise at every state the batch can reach it in). **The wait** (unit 2 of the
request path): `batchWaitOk` (each normal entry's id claimed for its data; each conf change's id,
`ccIdOf`, no KV request's registration), so every `Trigger` meets the registry's contract. **The
applied index** (the request path's unit 4b): the apply thread's half of the ghost applied index
(`srvAppliedOwn γr`) goes from `f0 - 1` to the last index, each `setAppliedIndex` depositing the KV
log after its entry, so the last index's log is `x'.log` (`appliedLogAt`). **The write budget**
(2026-10-13, unit 6): one write token of the store per entry (`txn.storeWTs E.γ ms.length`,
spent; a conf change's is wasted). -/
abbrev EtcdServer.apply.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames),
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → entriesOk (ciEff γ st.k) ms x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ batchWaitOk ρ E ms ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfStateAddr ep ↦ cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E x ∗ srvAppliedOwn γr (f0 - 1) ∗ txn.storeWTs E.γ ms.length }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop);
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
        epConfStateAddr ep ↦ csl ∗ srvLgReader s ∗ srvGoRes s ∗ srvAppliedOwn γr appliedi ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗
          appliedLogAt γr appliedi x'.log) ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi)⌝ }}

end spec

end EtcdGrove
end Perennial
