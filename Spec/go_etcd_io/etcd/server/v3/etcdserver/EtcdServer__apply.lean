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
normal entry applied by `apply.Apply`, with `v3` iff above `c`), under `logShape ms` (each
normal entry's request meets its premise wherever the size clauses hold; the apply thread's log
is small, `srvApplyKV_small`, so they hold at the state each entry meets: D19c's move,
2026-10-18; until then `entriesOk c ms x`, the premise at every state the batch can reach). **The wait** (unit 2 of the
request path): `batchWaitOk` (each normal entry's id claimed for its data; each conf change's id,
`ccIdOf`, no KV request's registration), so every `Trigger` meets the registry's contract. **The
applied index** (the request path's unit 4b): the apply thread's half of the ghost applied index
(`srvAppliedOwn γr`) goes from `f0 - 1` to the last index, each `setAppliedIndex` depositing the KV
log after its entry, so the last index's log is `x'.log` (`appliedLogAt`); since 2026-10-14 (unit
C2a) from the log applied through `f0 - 1` the KV's (`appliedLogAt γr (f0 - 1) x.log`), with each
entry committed (`batchCommittedIdx`: raft's batches, `rnApP`), each entry's log deposited ahead
of its result (`applyEntryNormal`'s `srvAppliedPre`). **The KV model** (2026-10-14, unit T1): the
apply thread at the committed raft log `A` through `f0 - 1` (`kvApplied`), the batch committed after
it (`kvBatch`), at `A ++ ms` after. **The write budget**
(2026-10-13, unit 6): one write token of the store per entry, spent (a conf change's is wasted);
since D19b (2026-10-18) taken from the budget `srvWTPool E` with a time receipt of the entry's
iteration, until then handed in (`txn.storeWTs E.γ ms.length`). **The stop** (D19m, 2026-10-18): it
returns `shouldStop = false`, since `applyConfChange` removes no member (`ccApplyOk`), so the
caller's `stopWithDelay` is never reached. **The driver's view** (D43 M3, 2026-10-25; raft's
dynamic mode): with a view `dv` (`dvOk`: no replay, the node at the server's decoder), the view
after `A` goes to the view after `A ++ ms`, each conf entry applied through `applyConfChange`;
without, nothing (raft's static mode, or no conf entry in the batch). -/
abbrev EtcdServer.apply.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (A : List EntryModel) (γp : GName) (dv : Option NodeNames),
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShape ms →
  dvOk ρ.raft dv (ciEff γ st.k) f0 ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ batchWaitOk ρ E ms ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr (f0 - 1) ∗
      appliedLogAt γr (f0 - 1) x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTAt γp (f0 - 1) ∗ srvFS s ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) (f0 - 1) A ms ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ ms) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop); srvFS s ∗ dvView ρ.raft dv (A ++ ms) ∗
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
        epConfState ep csl ∗ srvLgReader s ∗ srvGoRes s ∗ srvAppliedOwn γr appliedi ∗
        srvWTAt γp appliedi ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗
          appliedLogAt γr appliedi x'.log ∗ kvApplied γr.raft γr.kv (A ++ ms) x' ∗ srvRest E γr (A ++ ms)) ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
          shouldStop = false⌝ }}

end spec

end EtcdGrove
end Perennial
