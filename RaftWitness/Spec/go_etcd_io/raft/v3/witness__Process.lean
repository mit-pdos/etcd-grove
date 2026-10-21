/-
`(*witness).Process` (raft#168, `witness.go`; 2026-10-20, witness support, W3b).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitnessStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `w.Process(m)`, against the storage's contract (`isWitnessStorage s N P`) and the model
(`wNoUpdate`, `wStep`), for any reading of the storage's states the caller chooses: `Lb σ`
(persistent) of a state the storage held, which the cache always satisfies, and `Φr` of an
answer. The caller gives

- `Hcache`: an answer `wNoUpdate` gives from a cache (`processNoUpdate` before the loop) is
  `Φr`'s;
- `Hread`: at every read (the storage's linearization point, `GetWitnessState`), `Lb` of the
  state read and the round's obligation `wObl` (`Φr` of an answer without a write, or the
  write's shift), for a request of a type the witness answers (it reads the storage for no
  other);
- `Φr none` (a request of a type the witness ignores).

On success (`err = nil`) the answer, if any, is a fresh message (`respOpt`) with `Φr`'s; on a
storage error no answer. Either way the witness's cache is a state with `Lb`. A failed
compare-and-swap (`ErrWitnessStateModified`, or any error the storage gives back with the shift
unrun) is retried: the loop need not terminate (`Process` is partially correct). -/
abbrev witness.Process.spec : Prop :=
  ∀ (w : Loc) (id : w64) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool)
    (N : Namespace) (P Lb : WHS → IProp GF) (Φr : Option WResp → IProp GF)
    (mv : WitnessMessage) (μ : WMsg),
  (∀ σ, Persistent (Lb σ)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitness w id s cq pv c h ∗ isWitnessStorage s N P ∗ ownWMsg mv μ ∗ Lb c ∗
      "#Hcache" ∷ □ (∀ σ hh r, Lb σ -∗ ⌜wNoUpdate id cq pv hh σ μ = some r⌝ -∗ Φr r) ∗
      "#Hread" ∷ □ (∀ σ, ⌜μ.ty = MsgHeartbeat ∨ μ.ty = MsgApp ∨ μ.ty = MsgVote ∨
        μ.ty = MsgPreVote⌝ -∗ P σ ={⊤ \ ↑N}=∗ P σ ∗ Lb σ ∗ wObl id cq pv N P Lb Φr μ σ) ∗
      "#Hnone" ∷ □ Φr none }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"Process")) (Val #mv))
  {{ (ml : Loc) (err : GoError), RET (PairV #ml #err);
      ∃ c' h', ownWitness w id s cq pv c' h' ∗ Lb c' ∗
      ((⌜err = interface.nil⌝ ∗ ∃ r, respOpt ml r ∗ Φr r) ∨
       (⌜err ≠ interface.nil⌝ ∗ ⌜ml = null⌝)) }}

end spec

end EtcdGrove
end Perennial
