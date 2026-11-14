/-
**The built part at a restart** (restart S6, 2026-11-13; `/shared/tmp/restart-s56/plan.md` §2.1, D1):
`srvBuiltR`, what `NewServer.specR` (a restart's construction, auth off, no compaction) gives `start`,
with its law to `start`'s construction premise (`srvBuiltR_C`); the restart's apply state `restartKV`;
and the restart's pure facts for `NodeStartSpecR` (probe P6) and `bootstrap`'s restart contract (the
cluster version, `restart_clusterVerLogOk`). Lean-first (no Rocq counterpart).

`srvBuiltR` is `isServerBuiltC .off`'s rows less the stop's slot (`srvStop.slot`, which the post's
`srvStop.keep` gives, as at a first start), `srvBuiltRC .off` (one text since CP2's review, finding
3g): a first start's `srvBuiltG false` and `srvBuildGap` reach `isServerBuiltC` only through
`isServerBuiltC_of_gap`, which completes their KV rows (the uber-applier's field into `#Hfb`,
`srv.kv` into `#Hrdb`) and moves the first-start snapshot, token and snapshot-path rows into `HBr` at
`P = []`; at a restart the construction gives the completed rows and `HBr` at the restart point
(`srvBuiltRestartR`, restart S4) directly.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply thread's KV state at a restart** (pure): the KV model of the image's applied log
`A` at the restarted names `γk`, the start's chain, the log's compaction revision: what `kvApplied`
asks of the state at `A` (`x.log = kvModel γk A`, `x.chain = γk.ch0`, `x.crev = crevOf γk A`). -/
def restartKV (γk : KVNames) (A : List EntryModel) : apply.ApplyKV :=
  ⟨kvModel γk A, γk.ch0, crevOf γk A⟩

/-- **The built part at a restart** (see the file header): `start`'s construction premise less the
stop's slot at auth off (`srvBuiltRC .off`; CP2 review finding 3g, 2026-11-13: until then a generated
copy of `isServerBuiltC .off`'s rows, which could drift): the restart point `HBr`
(`srvBuiltRestartR .off`: the storage's snapshot at Go's `|P|`, the loop's and the apply side's
tokens at `P`, the apply thread's resources at the backend's log `γn.a0`, and, since CP2's finding 1,
the snapshot path's resources, `srvSnapOwn`, at the ghost index `ai₀ + |γn.a0|`: route (C)), `HEr` without `γn.a0 = []`, and `Hwpend` from
`srvRestartRows`. -/
def srvBuiltR (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) : IProp GF :=
  srvBuiltRC .off s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`start`'s construction premise from the restart's built part** and the stop's slot. -/
theorem srvBuiltR_C (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuiltR (GF := GF) s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ srvStop.slot s E γn Er ⊢
      isServerBuiltC .off s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  unfold srvBuiltR isServerBuiltC
  exact .rfl

/-- (Probe P6) **The backend's conf state is within raft's bounds** (`NodeStartSpecR`'s size
premise): a conf state of the simple membership of `vs`, with fewer than `2^62` voters. -/
theorem restart_cs_bound (cs : ConfStateM) (vs : GSet w64) (h : confStateIs cs (Membership.simple vs))
    (hs : GMap.size vs < 2 ^ 62) :
    (cs.Voters'.length + cs.Learners'.length + cs.VotersOutgoing'.length +
      cs.LearnersNext'.length : Int) ≤ 2 ^ 62 := by
  obtain ⟨hv, hvo, hl, hln, -⟩ := h
  simp only [hv.length_eq, hvo.length_eq, hl.length_eq, hln.length_eq, GMap.length_elements,
    Membership.simple, GMap.size_empty]
  omega

/-- (Probe P6) **The node's index facts at `A₀ := A`** (`NodeStartSpecR`'s): from the image's
`σ.b ≤ i ≤ σ.commit` (`wal.stopImage`), `bootLen ≤ i` and `i = |A|` (its start index `0`): `σ.b ≤ |A|`,
`|A| ≤ σ.commit` (graceful-only: it feeds `rnRestartOk`'s marked conjunct only) and
`bootLen ≤ σ.commit` (through the same fact). -/
theorem restart_idx (σ : StorContents) (i ai0 : w64) (A : List EntryModel) (bl : Nat)
    (hi : uint.Z i = uint.Z ai0 + A.length) (h0 : ai0 = W64 0)
    (hb : σ.b ≤ uint.nat i) (hc : uint.nat i ≤ σ.commit) (hbl : bl ≤ uint.nat i) :
    σ.b ≤ A.length ∧ A.length ≤ σ.commit ∧ bl ≤ σ.commit := by
  subst h0
  have : uint.nat i = A.length := by simp at hi; word
  omega

/-- **The image's committed log passes `Recover`'s version check** (restart S6, CP2: the restart
contract's `clusterVerLogOk L` at the image's `L = pre ++ A`, from the stopped incarnation's KV
invariant, `kv_log_verOk`; see `bootstrapRestartContract`'s docstring, "The cluster version"). -/
theorem restart_clusterVerLogOk (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (hpre : γ.pre = []) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜clusterVerLogOk (γ.pre ++ A)⌝ := by
  iintro #HkI #HrI #HA
  rw [hpre, List.nil_append]
  iapply kv_log_verOk γ γk A $$ HkI HrI HA

end lemmas

end EtcdGrove
end Perennial
