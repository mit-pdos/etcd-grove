/-
The bodies of the protocol's ghost predicates (`Epaxos/Interface/EpaxosGhost.lean` defines its
`sysAuth`, `repFrag`, ... as these; `notes/prove-epaxos.md`, "Ghost state"), and the body of
`epInv` over them (`epInvB`, equal to `epInvDef` by unfolding).

* `rep i`: replica `i`'s states so far, a mono-list (`rsAuth`), a quarter in `sysAuth`, three
  quarters in `repFrag` (two fragments exceed the whole: `repFrag_excl`); its last element is the
  state; every element's `crtInstance` is below the current one (pointwise), so an element read
  off the list (`rsIdx`) is a lower bound (`crtLb`).
* `outbox i to`, `pend i`, `cur i`: ghost variables, halves.
* `chan i`: the re-proposal tokens, a ghost map from a fresh key to the proposal (whole
  elements); the authority's entries, as a list without repeated keys, are a sub-multiset of the
  model's channel.

Every fragment carries `i < nR` (`sysAuth` holds the other parts for `i < nR` only).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostLib
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.NoneRec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The re-proposal tokens' authority of replica `i`: its entries `l` (no repeated key) are a
sub-multiset of `chan`. -/
def chanAuthB (γ : EpNames) (i : Nat) (chan : List Proposal) : IProp GF :=
  iprop(∃ (M : GMap Nat Proposal) (l : List (Nat × Proposal)),
    ghostMapAuth (γ.proto.chan i) 1 M ∗
    ⌜(∀ k, M.lookup k = l.lookup k) ∧ (l.map Prod.fst).Nodup ∧ (l.map Prod.snd).Subperm chan⌝)

/-- Replica `i`'s part of the authority. -/
def sysAuthRepB (γ : EpNames) (S : Sys) (i : Nat) : IProp GF :=
  iprop((∃ L : List RState, rsAuth (γ.proto.rep i) Qp.quarter L ∗
      ⌜L.getLast? = some (S.rep i)⌝) ∗
    ([∗list] to ∈ List.range nR, ghostVar (γ.proto.outbox i to) (1 : Qp).half (S.outbox i to)) ∗
    ghostVar (γ.proto.pend i) (1 : Qp).half (S.pending i) ∗
    ghostVar (γ.proto.cur i) (1 : Qp).half (S.execCur i, S.execIdx i) ∗
    chanAuthB γ i (S.proposeChan i))

def sysAuthB (γ : EpNames) (S : Sys) : IProp GF :=
  iprop([∗list] i ∈ List.range nR, sysAuthRepB γ S i)

/-- `crtInstance` of every state in `L` is pointwise below `σ`'s. -/
def crtBelow (L : List RState) (σ : RState) : Prop :=
  ∀ σ0 ∈ L, ∀ q, zz (σ0.crtInstance q) ≤ zz (σ.crtInstance q)

def repFragB (γ : EpNames) (i : Nat) (σ : RState) : IProp GF :=
  iprop(⌜i < nR⌝ ∗ ∃ L : List RState, rsAuth (γ.proto.rep i) Qp.threeQuarters L ∗
    ⌜L.getLast? = some σ ∧ crtBelow L σ⌝)

def crtLbB (γ : EpNames) (i q : Nat) (n : w32) : IProp GF :=
  iprop(∃ (k : Nat) (σ0 : RState), rsIdx (γ.proto.rep i) k σ0 ∗
    ⌜zz n ≤ zz (σ0.crtInstance q)⌝)

def inChanB (γ : EpNames) (i : Nat) (p : Proposal) : IProp GF :=
  iprop(⌜i < nR⌝ ∗ ∃ k : Nat, ghostMapElem (γ.proto.chan i) k (DFrac.own 1) p)

def outboxFragB (γ : EpNames) (i to : Nat) (ms : List Msg) : IProp GF :=
  iprop(⌜i < nR ∧ to < nR⌝ ∗ ghostVar (γ.proto.outbox i to) (1 : Qp).half ms)

def pendFragB (γ : EpNames) (i : Nat) (ob : Option Bcast) : IProp GF :=
  iprop(⌜i < nR⌝ ∗ ghostVar (γ.proto.pend i) (1 : Qp).half ob)

def curFragB (γ : EpNames) (i : Nat) (cur : List InstId) (idx : Nat) : IProp GF :=
  iprop(⌜i < nR⌝ ∗ ghostVar (γ.proto.cur i) (1 : Qp).half (cur, idx))

instance crtLbB_persistent (γ : EpNames) (i q : Nat) (n : w32) : Persistent (crtLbB (GF := GF) γ i q n) := by
  unfold crtLbB; infer_instance

/-! ## The frozen definitions, over the bodies -/

def repIdleB (γ : EpNames) (i : Nat) : IProp GF :=
  iprop(([∗list] to ∈ List.range nR, outboxFragB γ i to []) ∗ pendFragB γ i none ∗
    curFragB γ i [] 0)

def outOkB (γ : EpNames) (i : Nat) : Out → IProp GF
  | .send _ _ => iprop(True)
  | .bcast _ => iprop(True)
  | .reply p v => iprop(∃ o, fired γ p.cid o ∗ ⌜replyValOk o v⌝)
  | .repropose p => inChanB γ i p
  | .ev _ => iprop(True)

def sendsToB (outs : List Out) (to : Nat) : List Msg :=
  outs.filterMap (fun o => match o with | .send t m => if t = to then some m else none | _ => none)

def outsOkB (γ : EpNames) (i : Nat) (outs : List Out) : IProp GF :=
  iprop(([∗list] to ∈ List.range nR, outboxFragB γ i to (sendsToB outs to)) ∗
    pendFragB γ i (pendOf outs) ∗ curFragB γ i [] 0 ∗
    [∗list] o ∈ outs, outOkB γ i o)

def epInvB (γ : EpNames) : IProp GF :=
  iprop(∃ S : Sys, sysAuthB γ S ∗ ⌜Inv S⌝ ∗ ⌜InvX S⌝ ∗ kvHalf γ S.kv ∗
    (∃ F : GMap Nat KvO, firedAuth γ F ∗ ⌜∀ cid, F.lookup cid = S.fired cid⌝ ∗
      [∗map] cid ↦ o ∈ F, fired γ cid o) ∗
    ([∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
      if fr = to then iprop(True) else sentHalf γ fr to (S.sent fr to)) ∗
    ([∗list] d ∈ S.delivered, delivTok γ d.2.1 d.1 d.2.2) ∗
    ([∗list] o ∈ S.ops, connFresh o.2.cid true ∗
      ∃ (c : w64) (inp : KvI), clientConn γ o.2.cid c inp ∗ ⌜o.2.cmd = cmdOf inp⌝))

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
