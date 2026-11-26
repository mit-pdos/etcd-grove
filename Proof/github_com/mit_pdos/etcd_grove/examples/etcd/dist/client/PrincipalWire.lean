/- Lean-first (no Rocq counterpart).

# The auth workload's principal service (#50 F7 S7, `notes/etcd-dist-f7.md`; the pattern of `WriterWire.lean`)

What crosses a principal machine's connection (`remote.Report` at the orchestrator, `remotePrincipals`;
`remote.ServeClient` with `principalOp` at the principal machine, `NodeMain`'s auth arm; `principalCodec`):

* **The wire** `principalWire`: an input is a principal's name `w` (a Go `string` in an interface), an output
  whether its `auth.Work` ran (a `bool`); the bytes are `enc`'s (`encStr`, `encBool`). Both values are fixed by
  the model values (no memory), so one wire serves the global part and the machines alike (the writers need
  two, `writerWireG`/`writerWire`, because a slice's elements are a machine's).
* **The service** `principalSvcG Γ γR addrs` (a report, `remote.reportSvc`): the far side is given the
  principals' environment at the view `Γ`, the server's raft names `γR` and the members' client addresses
  `addrs` (`akDistEnvG`, `akDistEnv`'s body at the global ghost state: the service is the start's,
  `principalsShare`; `akDistEnv_eq_G`), and that the name is one of `auth.Principals()`; it answers anything
  (`True`: the orchestrator reads nothing of the answers, its checks rest on `akHistInv`, which every write
  of a principal keeps).
* **No ghost names in the request**: the names the set-up allocates at run time (`γz`, `hs`, `Lset`, `r`) are
  `akDistEnv`'s existentials, so they need not travel (the writers' adapter names do, `WN`); `γR` and `addrs`
  are the deployment's, fixed by the start with the share.
* **The principal machines' share** `principalsShare Γ γR addrs ns` (global): the slot map, one machine per
  principal (`ns.length = 4`), and at each address the service's protocols (`svcAddr`) and one call's budget:
  `remotePrincipals.specWith`'s and `RunAuth.specWith`'s `PS`.
* **A principal machine's resource** `principalTok Γ addrs sys` (`principalOp`'s `tok`): its level token and
  `sys`, the members' client addresses (`NodeMain` passes `eps`), each serving a member of `Γ`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Checks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section wire
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

theorem encBool_len (b : Bool) : (encBool b).length < 2 ^ 63 := by
  simp [encBool]

/-- **A name's bytes read back** (`principalCodec`'s `DecIn`): the bytes of `w`, capped, are those of `s`
only if `s = w` and they were not capped. -/
theorem strBytes_dec {w s : GoString} (h : capped (encStr w) = encStr s ++ []) :
    s = w ∧ (encStr w).length < 2 ^ 63 := by
  rw [List.append_nil] at h
  by_cases hl : (encStr w).length < 2 ^ 63
  · rw [capped_of _ hl] at h
    have hl' : (encStr s).length < 2 ^ 63 := h ▸ hl
    simp only [encStr, List.length_append, encU64_length] at hl hl'
    have := encStr_append_inj (r := []) (r' := []) (by simpa using h) (by omega) (by omega)
    exact ⟨this.1.symm, by simp only [encStr, List.length_append, encU64_length]; omega⟩
  · exfalso
    simp only [capped, hl, ↓reduceIte] at h
    have := congrArg List.length h
    simp [encStr, encU64_length] at this

/-- **The principals' wire** (see the file header). -/
def principalWire : RWire GF GoString Bool where
  ivAt x w := iprop(⌜x = interface.mkOk go.string #w ∧ (encStr w).length < 2 ^ 63⌝)
  ovAt v b := iprop(⌜v = interface.mkOk go.bool #b⌝)
  ivAt_persistent _ _ := BI.pure_persistent _
  ovAt_persistent _ _ := BI.pure_persistent _
  encIn w := capped (encStr w)
  encOut b := encBool b
  encIn_len _ := capped_len _
  encOut_len b := encBool_len b

end wire

section svc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext] [GoLocalContext] [go.Semantics]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `etcd_auth.akHistInv`'s body at the global ghost state (`akDistEnv_eq_G`). -/
def akHistInvG (γk : KVNames) : IProp GF :=
  inv etcd_auth.akHistN iprop(∃ σ : KVState, etcdKV γk σ ∗ ⌜etcd_auth.stateHistOk σ⌝)

/-- `authHistMark`'s body at the global ghost state. -/
def authHistMarkG (γz : GName) (hs : List auth.AuthState) : IProp GF :=
  dghostVar γz .discard (true, hs)

/-- `authHistFrozen`'s body at the global ghost state. -/
def authHistFrozenG (γk : KVNames) (γz : GName) (hs : List auth.AuthState) : IProp GF :=
  iprop(inv authHistN iprop(∃ hs : List auth.AuthState, authHistView γk hs ∗
      (dghostVar γz (.own (1 : Qp).half) (false, hs) ∨ authHistMarkG γz hs)) ∗
    authHistMarkG γz hs)

/-- `authFloorD`'s body at the global ghost state. -/
def authFloorDG (Γ : DistView) (γR : ServerRaftNames) (mid : w64)
    (L₀ : List EntryModel) (m : Nat) : IProp GF :=
  iprop(auth.authPubLbM (.on (Γ.au mid)) m ∗ ∃ (L : List EntryModel) (i : Nat), ⌜L₀ <+: L ∧ i ≤ m⌝ ∗
    srvReqLogLb γR L ∗ auth.authStateAt (Γ.au mid) i (srvAuthAtLog Γ.kv srvAuthSt0 L) ∗
    □ (∀ (E' : CoPset) (j : Nat) (st : auth.AuthState), ⌜authTieReadMask ⊆ E' ∧ i ≤ j⌝ -∗
      auth.authStateAt (Γ.au mid) j st ={E'}=∗
      ∃ L' : List EntryModel, ⌜L₀ <+: L' ∧ st = srvAuthAtLog Γ.kv srvAuthSt0 L'⌝ ∗ srvReqLogLb γR L'))

/-- `watchFloorsD`'s body at the global ghost state. -/
def watchFloorsDG [NetProtoGS] (eps : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (L₀ : List EntryModel) : IProp GF :=
  iprop([∗list] a ∈ eps, ∃ (mid : w64) (m : Nat),
    etcdAddrAt (Gg := Gg) a Γ mid ∗ authFloorDG Γ γR mid L₀ m)

/-- **The principals' environment at the global ghost state** (`akDistEnv`'s body; `akDistEnv_eq_G`). -/
def akDistEnvG [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames) : IProp GF :=
  iprop(∃ (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat),
    kvInvOn γR Γ.kv srvAuthSt0 ∗ akHistInvG Γ.kv ∗ authHistFrozenG Γ.kv γz hs ∗
    srvReqLogLb γR Lset ∗ watchFloorsDG addrs Γ γR Lset ∗
    ⌜admStates Γ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r⌝)

/-- **What a principal machine is given with its name** (see the file header). -/
def prP [NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (addrs : List GoString) (w : GoString) : IProp GF :=
  iprop(akDistEnvG (Gg := Gg) addrs Γ γR ∗ ⌜w ∈ etcd_auth.principals⌝)

/-- **What a principal machine answers**: nothing the orchestrator reads. -/
def prQ (_w : GoString) (_b : Bool) : IProp GF := iprop(True)

/-- **The principal service** (see the file header; the share's, and a machine's: its wire has no
values in memory). -/
abbrev principalSvcG [NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (addrs : List GoString) :
    RSvc GF GoString Bool :=
  reportSvc principalWire (prP (Gg := Gg) Γ γR addrs) prQ

variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **The principal machines' share** (see the file header): `RunAuth.specWith`'s `PS`. -/
def principalsShare (Γ : DistView) (γR : ServerRaftNames) (addrs ns : List GoString) : IProp GF :=
  iprop(mapCtx (Gg := Gg) (I := GoString) ∗ ⌜ns.length = etcd_auth.principals.length⌝ ∗
    [∗list] a ∈ ns, svcAddr (Gg := Gg) (principalSvcG (Gg := Gg) Γ γR addrs) a ∗ budUnit (Gg := Gg) a)

end svc

section onMachine
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `akDistEnv` is `akDistEnvG` at the machine's global ghost state. -/
theorem akDistEnv_eq_G [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames) :
    akDistEnv (GF := GF) addrs Γ γR = akDistEnvG (Gg := hG.goose_globalGS) addrs Γ γR := rfl

/-- **A principal machine's resource for its calls** (`remote.ServeClient`'s `tok`; see the file header). -/
def principalTok [NetProtoGS] (Γ : DistView) (addrs : List GoString) (sys : GoInterface) : IProp GF :=
  iprop(levelTok 0 ∗ ∃ sl : GoSlice, ⌜sys = interface.mkOk (go.GoType.SliceType go.string) #sl⌝ ∗
    sl ↦*□ addrs ∗ membersAt (Gg := hG.goose_globalGS) addrs Γ)

end onMachine

end etcd_dist_client
end EtcdGrove
end Perennial

end
