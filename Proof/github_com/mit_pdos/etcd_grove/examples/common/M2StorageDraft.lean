/-
**M2, the storage side: the server's compaction mode at the examples' boot** (review round 2's N1,
the route decided after the round: `notes/m2-storage-plan.md`, "After review round 2" and "Step 1
on the merged lean"). Imported by nothing but the examples' other Draft modules; no `axiom`, no
`sorry`.

The stand-in `E₀` carries the member's compaction mode (`apply.AEnvD`'s `cmp`, the server's Draft
`etcdserver/M2StorageDraft.lean`): the examples' allocations (`alloc1`, `alloc3`, linkv3p's) build
it at `env₀D … (cmp := false)` (the default), `StartCompactingServer` at `true`; the member's boot
bundle records it (`memberBootD`'s pure facts gain `E₀.cmp = cmp`), so a `Main` reads it before
`newServer` takes the bundle (`memberBootD_cmp`) and gives it to `NewServer.spec` (its premise
`E₀.cmp = false`); after `Start`, `memberUp`'s `envAgree E E₀` (redefined: `envAgreeD`) gives
`¬ kbCmpM E.γ.kb` (`envAgreeD_off`), the premise of the watch clients' glue (watchkv's
`wk_servedD`, the cache's `etcd_cache_servedD`, linkv3p's `memberWatchD`). `memberBuilt` and
`memberUp` keep their texts (over the redefined `envAgree`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2StorageDraft

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **Draft of `env₀`** (N1): the stand-in at a compaction mode, `false` by default (so `alloc1`,
`alloc3` and linkv3p's allocation keep their texts); at the switch `env₀` gains the argument
`(cmp : Bool := false)` and the field `cmp := cmp`. -/
def env₀D (idx : mvcc.IdxNames) (cok rev : GName) (cmp : Bool := false) : apply.AEnvD GF :=
  { env₀ (GF := GF) idx cok rev with cmp := cmp }

theorem env₀D_cmp (idx : mvcc.IdxNames) (cok rev : GName) (cmp : Bool) :
    (env₀D (GF := GF) idx cok rev cmp).cmp = cmp := rfl

/-- **Draft of `memberBoot`** (N1): the member's boot bundle at a compaction mode `cmp` (default
`false`), recorded in its pure facts (`E₀.cmp = cmp`, appended). The rest as today. -/
def memberBootD (γ : SrvRaft) (ctxs : List (List w8))
    (ρ : ReqNames) (E₀ : apply.AEnvD GF) (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64)
    (cmp : Bool := false) : IProp GF :=
  iprop(⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧
      ρ.rd.kv.c0 = W64 0 ∧ ρ.rd.kv.ch0 = apply.alarmChain false false false ∧
      ρ.rd.kv.log0 = [[], []] ∧ ρ.rd.kv.cok = E₀.γ.cok ∧
      ρ.ids.pfx = idPfxOf (W16 (uint.Z id)) ∧ Φs ρ.ids.pfx = srvFloorFact E₀.toAEnv ∧
      E₀.cmp = cmp⌝ ∗
    nodeBoot γ.cl srvClusterN γ.vs ctxs id ∗ srvRaftLogInv ρ.rd.raft ∗
    idClusterInv ρ.ids.issued ρ.ids.cnt Φs ∗ idNoZero ρ.ids ∗
    srvPropMint ρ.rd.raft ρ.ids ∗ srvRdCtxInv ρ.rd.raft ρ.ids.issued ∗
    idShare ρ.ids ∗ idWaitTok ρ.ids ∗
    mvcc.idxFresh E₀.γ.idx ∗
    ghostMapAuth E₀.γ.cok 1 (∅ : GMap w64 mvcc.Log) ∗
    ghostMapAuth E₀.γrev 1 (∅ : GMap w64 Unit) ∗
    srvReadNamesFreshNK ρ.rd ∗ kvInv ρ.rd.raft ρ.rd.kv ∗
    ghostMapAuth γ.reg 1 (∅ : GMap Loc MemStorNamesRec) ∗
    ∃ γd : GName, ⌜γ.snapLoc id = some γd⌝ ∗ ghostMapAuth γd 1 (∅ : GMap w64 Unit))

/-- **The member's compaction mode, read off its boot bundle** (N1: what a `Main` keeps before
`newServer` takes the bundle; `newServer`'s proof gives it to `NewServer.spec`'s premise). -/
theorem memberBootD_cmp (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnvD GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) (cmp : Bool) :
    memberBootD γ ctxs ρ E₀ Φs id cmp ⊢ ⌜E₀.cmp = cmp⌝ ∗ memberBootD γ ctxs ρ E₀ Φs id cmp := by
  iintro H
  iunfold memberBootD at H
  icases H with ⟨%Hρ, Hr⟩
  isplitr
  · ipureintro; exact Hρ.2.2.2.2.2.2.2
  iunfold memberBootD
  isplitr
  · ipureintro; exact Hρ
  iexact Hr

/-- **The drafted bundle is today's with the mode** (N1): the allocations' (`alloc1`, `alloc3`:
today's bundle at `env₀D … cmp`, whose mode is `cmp` by `env₀D_cmp`). -/
theorem memberBootD_of (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnvD GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) (cmp : Bool) (h : E₀.cmp = cmp) :
    memberBoot γ ctxs ρ E₀.toAEnv Φs id ⊢ memberBootD γ ctxs ρ E₀ Φs id cmp := by
  iintro H
  iunfold memberBoot at H
  icases H with ⟨%Hρ, Hr⟩
  iunfold memberBootD
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hρ
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h⟩
  iexact Hr

/-- And back (what `newServer` passes on to `NewServer`: the bundle's resources are today's). -/
theorem memberBootD_to (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnvD GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) (cmp : Bool) :
    memberBootD γ ctxs ρ E₀ Φs id cmp ⊢ memberBoot γ ctxs ρ E₀.toAEnv Φs id := by
  iintro H
  iunfold memberBootD at H
  icases H with ⟨%Hρ, Hr⟩
  iunfold memberBoot
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := Hρ
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  iexact Hr

end draft

end common
end EtcdGrove
end Perennial
