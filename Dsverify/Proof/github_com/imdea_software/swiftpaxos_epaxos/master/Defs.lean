/-
The master's predicates and the specs of its functions (the lab's
`Epaxos/Interface/MasterSpec.lean`, restated over the generic world; tier "defs"):

* `masterFresh m cfg logger`: the master as `master.New(5, 7501, cfg, logger)` builds it;
* `masterLockInv γ m`: the invariant of `master.lock`: the registered replica nodes `ks`
  (distinct configured replica nodes) with their peer addresses, IPs and ports in `nodeList`,
  `addrList`, `portList` (owned, with `listUnset γ`, while fewer than five; read-only, with
  `listFinal γ`, from the fifth on), `leader`, half of `alive`'s contents (`run()` keeps the other
  half), `latencies`, `finishInit`;
* `isMaster γ m` (persistent): the package, the lock with `masterLockInv`, the condition
  variable, the read-only fields `N`, `config`, `Logger` and their contents;
* `runRes γ W m`: what `run()` gets from `Run`;
* the specs: `master.New.specM`, `Master.run.specM`, `Master.Run.specM` (the master package's),
  `NewBeTheLeaderReply.specM`, `UpdateBeTheLeaderReply.specM` (the `defs` package's, as the
  master calls them); the promoted `Printf`/`Fatal` (`wp_Master_Printf`, `wp_Master_Fatal`, from
  dlog's specs, `Interface/Misc.lean`).

Ports: the kit's master listens on `":7501"`; replica node `k` registers `(replicaIp k, portOf k)`,
`portOf k = 7500 + k` (the lab: 7001, 7000 + k).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcHttpHyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Misc
public import Net.Spec.net.Listen
public import Perennial.Proof.sync
public import Perennial.Proof.fmt.Results
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts -/

theorem ks_le (ks : List Nat) (hnd : ks.Nodup) (hsub : ∀ k ∈ ks, k ∈ replicaNodes) :
    ks.length ≤ 5 :=
  List.Nodup.length_le_of_subset hnd (fun x hx => hsub x hx)

theorem ks_full (ks : List Nat) (hnd : ks.Nodup) (hsub : ∀ k ∈ ks, k ∈ replicaNodes)
    (h5 : ¬ ks.length < 5) : ∀ k ∈ replicaNodes, k ∈ ks := by
  intro k hk
  refine Classical.byContradiction fun hn => ?_
  have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hn, hnd⟩)
    (l₂ := replicaNodes) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hk
      · exact hsub x hx)
  simp [replicaNodes] at this; omega

theorem ks_perm (ks : List Nat) (hnd : ks.Nodup) (hsub : ∀ k ∈ ks, k ∈ replicaNodes)
    (h5 : ks.length = 5) : finalListOk (ks.map peerAddrOf) := by
  unfold finalListOk
  rw [replicaAddrs_eq]
  apply List.Perm.map
  rw [List.perm_ext_iff_of_nodup hnd (by decide)]
  intro a
  exact ⟨hsub a, ks_full ks hnd hsub (by omega) a⟩

theorem set_app_end {α : Type} (L v : List α) (y : α) (n : Nat) (hL : L.length = n)
    (hlen : (L ++ v).length = n + 1) : ((L ++ v).drop 0).set n y = L ++ [y] := by
  obtain ⟨x, rfl⟩ : ∃ x, v = [x] := by
    match v, hlen with
    | [x], _ => exact ⟨x, rfl⟩
    | [], h => simp at h; omega
    | _ :: _ :: _, h => simp at h; omega
  subst hL
  simp

theorem rpcAddrOf_fmt (k : Nat) :
    rpcAddrOf k = replicaIp k ++ go!":" ++ fmt.decimal (8500 + k) := rfl

theorem sprintf_str_colon_int [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    [go.IntoValInj GoString] [go.IntoValInj w64] [go.string ↓u go.string]
    (x : GoString) (n : w64) (out : GoString)
    (h : out = _root_.Perennial.fmt.render [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      [.str x, .int (sint.Z n)]) :
    out = x ++ go!":" ++ fmt.decimal (sint.Z n) := by
  rw [h]; simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, _root_.Perennial.fmt.decimalPad_zero]

theorem sprintf_colon_int [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    [go.IntoValInj w64] [go.string ↓u go.string] (n : w64) (out : GoString)
    (h : out = _root_.Perennial.fmt.render [.lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      [.int (sint.Z n)]) :
    out = go!":" ++ fmt.decimal (sint.Z n) := by
  rw [h]; simp (config := { decide := true }) [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, _root_.Perennial.fmt.decimalPad_zero]

/-! ## The master's predicates -/

section fld
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [go.Semantics]

/-- A field of the master (stated over the local context only, so that a use determines every
argument). -/
abbrev mfld (m : Loc) (f : GoString) : Loc := structFieldRef master.Master f m

end fld

section master
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions]

/-- The master as `master.New(5, 7501, cfg, logger)` builds it (exclusive): its fields (`N` 5,
`port` 7501, empty `nodeList`/`addrList`/`portList` of capacity 5, `nodes`/`leader`/`alive`/
`latencies` of length 5, `finishInit` false, `nextLeader` -1, the logger and the configuration,
read-only, with no configured leader); the lock and its condition variable as `New` makes them. -/
def masterFresh (m cfg logger : Loc) : IProp GF :=
  iprop(∃ (x : master.Master) (c : config.Config),
    m ↦ x ∗ ⌜x.Logger' = logger ∧ x.N' = W64 5 ∧ x.port' = W64 7501 ∧ x.config' = cfg ∧
      x.finishInit' = false ∧ x.nextLeader' = W64 (-1) ∧ sint.Z x.nodeList'.cap = 5 ∧
      sint.Z x.addrList'.cap = 5 ∧ sint.Z x.portList'.cap = 5⌝ ∗
    x.nodeList' ↦* ([] : List GoString) ∗ ownSliceCap GoString x.nodeList' (DFrac.own 1) ∗
    x.addrList' ↦* ([] : List GoString) ∗ ownSliceCap GoString x.addrList' (DFrac.own 1) ∗
    x.portList' ↦* ([] : List w64) ∗ ownSliceCap w64 x.portList' (DFrac.own 1) ∗
    x.nodes' ↦* List.replicate 5 (null : Loc) ∗ x.leader' ↦* List.replicate 5 false ∗
    x.alive' ↦* List.replicate 5 false ∗ x.latencies' ↦* List.replicate 5 (W64 0) ∗
    x.lock' ↦ (zeroValDef : sync.Mutex) ∗
    sync.isCond x.initCond' ⟨go.GoType.PointerType sync.Mutex.ty, #x.lock'⟩ ∗
    logger ↦□ dlog.Logger.mk null false ∗ cfg ↦□ c ∗ ⌜c.Leader' = null⌝)

/-- The registrations' fields and slices (see the file header). -/
def masterLists (γ : EpNames) (m : Loc) (ks : List Nat) (nl al pl : GoSlice) : IProp GF :=
  if ks.length < 5 then
    iprop(mfld m go!"nodeList" ↦ nl ∗ nl ↦* ks.map peerAddrOf ∗
      ownSliceCap GoString nl (DFrac.own 1) ∗
      mfld m go!"addrList" ↦ al ∗ al ↦* ks.map replicaIp ∗
      ownSliceCap GoString al (DFrac.own 1) ∗
      mfld m go!"portList" ↦ pl ∗ pl ↦* ks.map portOf ∗
      ownSliceCap w64 pl (DFrac.own 1) ∗ listUnset γ)
  else
    iprop(mfld m go!"nodeList" ↦□ nl ∗ nl ↦*□ ks.map peerAddrOf ∗
      mfld m go!"addrList" ↦□ al ∗ al ↦*□ ks.map replicaIp ∗
      mfld m go!"portList" ↦□ pl ∗ pl ↦*□ ks.map portOf ∗
      listFinal γ (ks.map peerAddrOf))

/-- The invariant of `master.lock` (see the file header). -/
def masterLockInv (γ : EpNames) (m : Loc) : IProp GF :=
  iprop(∃ (ks : List Nat) (nl al pl ldsl alsl latsl : GoSlice) (ld alv : List Bool)
      (lat : List w64) (fi : Bool),
    ⌜ks.Nodup ∧ (∀ k ∈ ks, k ∈ replicaNodes) ∧ sint.Z nl.cap = 5 ∧ sint.Z al.cap = 5 ∧
      sint.Z pl.cap = 5 ∧ ld.length = 5 ∧ alv.length = 5 ∧ lat.length = 5⌝ ∗
    masterLists γ m ks nl al pl ∗
    mfld m go!"leader" ↦□ ldsl ∗ ldsl ↦* ld ∗ mfld m go!"alive" ↦□ alsl ∗
    alsl ↦*{DFrac.own (1 : Qp).half} alv ∗
    mfld m go!"latencies" ↦□ latsl ∗ latsl ↦* lat ∗ mfld m go!"finishInit" ↦ fi)

/-- `masterLockInv` unfolded (to destruct it without unfolding it elsewhere). -/
theorem masterLockInv_iff (γ : EpNames) (m : Loc) :
    masterLockInv (GF := GF) γ m ⊣⊢
    iprop(∃ (ks : List Nat) (nl al pl ldsl alsl latsl : GoSlice) (ld alv : List Bool)
        (lat : List w64) (fi : Bool),
      ⌜ks.Nodup ∧ (∀ k ∈ ks, k ∈ replicaNodes) ∧ sint.Z nl.cap = 5 ∧ sint.Z al.cap = 5 ∧
        sint.Z pl.cap = 5 ∧ ld.length = 5 ∧ alv.length = 5 ∧ lat.length = 5⌝ ∗
      masterLists γ m ks nl al pl ∗
      mfld m go!"leader" ↦□ ldsl ∗ ldsl ↦* ld ∗ mfld m go!"alive" ↦□ alsl ∗
      alsl ↦*{DFrac.own (1 : Qp).half} alv ∗
      mfld m go!"latencies" ↦□ latsl ∗ latsl ↦* lat ∗ mfld m go!"finishInit" ↦ fi) := by
  unfold masterLockInv; exact .rfl

/-- The master after `Run`'s set-up (persistent): the master package initialized, its lock with
`masterLockInv`, the read-only fields `N`, `lock`, `initCond` (the lock's condition variable),
`config`, `Logger` and their contents. -/
def isMaster (γ : EpNames) (m : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master ∗
    ∃ (mu cfg logger ic : Loc) (c : config.Config),
    mfld m go!"lock" ↦□ mu ∗ sync.isMutex mu (masterLockInv γ m) ∗
    mfld m go!"initCond" ↦□ ic ∗
    sync.isCond ic ⟨go.GoType.PointerType sync.Mutex.ty, #mu⟩ ∗
    mfld m go!"N" ↦□ W64 5 ∗
    mfld m go!"config" ↦□ cfg ∗ cfg ↦□ c ∗ ⌜c.Leader' = null⌝ ∗
    mfld m go!"Logger" ↦□ logger ∗ logger ↦□ dlog.Logger.mk null false)

instance isMaster_persistent (γ : EpNames) (m : Loc) : Persistent (isMaster (GF := GF) γ m) := by
  unfold isMaster; infer_instance

theorem isMaster_pkg (γ : EpNames) (m : Loc) :
    isMaster (GF := GF) γ m ⊢
      isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master := by
  unfold isMaster
  iintro ⟨#H, -⟩; iexact H

/-- Read access to `nodeList` in either state of the registrations. -/
theorem lists_view (γ : EpNames) (m : Loc) (ks : List Nat) (nl al pl : GoSlice) :
    masterLists (GF := GF) γ m ks nl al pl ⊢
    ∃ dq : DFrac, mfld m go!"nodeList" ↦{dq} nl ∗ nl ↦*{dq} ks.map peerAddrOf ∗
      (mfld m go!"nodeList" ↦{dq} nl -∗ nl ↦*{dq} ks.map peerAddrOf -∗
        masterLists γ m ks nl al pl) := by
  unfold masterLists
  by_cases h5 : ks.length < 5
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h5)]
    iintro ⟨H1, H2, Hr⟩
    iexists (DFrac.own 1)
    iframe H1 H2
    iintro H1 H2
    iframe
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h5)]
    iintro ⟨#H1, #H2, #Hr⟩
    iexists DFrac.discard
    iframe H1 H2
    iintro - -
    iexact Hr

theorem ownSlice_halves (s : GoSlice) (vs : List Bool) :
    (s ↦* vs : IProp GF) ⊣⊢
      s ↦*{DFrac.own (1 : Qp).half} vs ∗ s ↦*{DFrac.own (1 : Qp).half} vs := by
  have h := (ownSlice_dfractional (GF := GF) s vs).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  exact h

end master

/-! ## The promoted logger methods -/

section logger
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [master.Assumptions]

/-- `master.Printf(format, v...)` (promoted from the embedded non-verbose `*dlog.Logger`). -/
theorem wp_Master_Printf (hP : dlog.Logger.Printf.spec (GF := GF)) (m logger : Loc)
    (format : GoString) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master ∗
        mfld m go!"Logger" ↦□ logger ∗ logger ↦□ dlog.Logger.mk null false }}
      (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Printf")) (Val #format))
        (Val #v))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlf, #Hlog⟩
  wp_auto
  wp_apply (hP logger null format v) $$ [$Hlog]
  wp_end

/-- `master.Fatal(v...)` on the non-verbose logger: returns. -/
theorem wp_Master_Fatal (hF : dlog.Logger.Fatal.spec (GF := GF)) (m logger : Loc) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master ∗
        mfld m go!"Logger" ↦□ logger ∗ logger ↦□ dlog.Logger.mk null false }}
      (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Fatal")) (Val #v))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlf, #Hlog⟩
  wp_auto
  wp_apply (hF logger null v) $$ [$Hlog]
  wp_end

end logger

/-! ## The specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions]

/-- `master.New(5, 7501, cfg, logger)` (as `serve(1, ...)` calls it), with a configuration with
no leader and the non-verbose logger. -/
abbrev master.New.specM : Prop :=
  ∀ (cfg logger : Loc) (c : config.Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master ∗
      cfg ↦□ c ∗ ⌜c.Leader' = null⌝ ∗ logger ↦□ dlog.Logger.mk null false }}
    (App (App (App (App (Val (@! master.New)) (Val #(W64 5))) (Val #(W64 7501))) (Val #cfg))
      (Val #logger))
  {{ (m : Loc), RET #m; masterFresh m cfg logger }}

/-- `defs.NewBeTheLeaderReply()`. -/
abbrev NewBeTheLeaderReply.specM : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs }}
    (App (Val (@! replica.defs.NewBeTheLeaderReply)) (Val #()))
  {{ (l : Loc), RET #l; l ↦ replica.defs.BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }}

/-- `defs.UpdateBeTheLeaderReply(l)` on `-1` fields: no change. -/
abbrev UpdateBeTheLeaderReply.specM : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs ∗
      l ↦ replica.defs.BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }}
    (App (Val (@! replica.defs.UpdateBeTheLeaderReply)) (Val #l))
  {{ RET #(); l ↦ replica.defs.BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }}

variable [log.Assumptions] [net.http.Assumptions] [RA : RpcHttpAddr GF] [RH : RpcHttpHyp GF]

/-- The rpc addresses of the replicas, as `run()` dials them (`DialHTTP`'s premise). -/
def replicaRpcs (W : net.rpc.RpcWorld GF) : IProp GF :=
  iprop([∗list] k ∈ replicaNodes,
    RpcHttpAddr.rpcAddrP W (rpcAddrOf k) (connectReq defaultRPCPath) connectAns)

instance replicaRpcs_persistent (W : net.rpc.RpcWorld GF) :
    Persistent (replicaRpcs (GF := GF) W) := by
  unfold replicaRpcs; infer_instance

/-- What `run()` gets from `Run`: the fields only `run()` uses (`nodes` with its slice,
`nextLeader`), the other half of `alive`'s contents, the replicas' rpc addresses, the rpc world,
net/rpc with the kit's codec and the client's environment. -/
def runRes (γ : EpNames) (W : net.rpc.RpcWorld GF) (m : Loc) : IProp GF :=
  iprop(∃ nds alsl : GoSlice, mfld m go!"nodes" ↦ nds ∗ nds ↦* List.replicate 5 (null : Loc) ∗
    mfld m go!"nextLeader" ↦ W64 (-1) ∗
    mfld m go!"alive" ↦□ alsl ∗ alsl ↦*{DFrac.own (1 : Qp).half} List.replicate 5 false ∗
    replicaRpcs W ∗ ⌜W.SS = rpcSS γ ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗ rpcReady ∗ net.rpc.cliEnv ∗ dialEnv)

/-- `m.run()`: waits for the five replicas, dials them, tells one `BeTheLeader`, pings them for
good (it never returns). -/
abbrev Master.run.specM (γ : EpNames) (W : net.rpc.RpcWorld GF) : Prop :=
  ∀ (m : Loc),
  {{ isMaster γ m ∗ runRes γ W m }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

/-- `m.Run()` on the master `New` built: registers it on net/rpc's `DefaultServer`, serves
net/rpc over HTTP on `":7501"` and runs `run()`; it returns only after a registration or listen
error, or when `http.Serve` returns. The master's address is the only rpc address the wildcard
takes that has a service (`W.SS = rpcSS γ`); the replicas' rpc addresses are dialed by `run()`. -/
abbrev Master.Run.specM (γ : EpNames) (W : net.rpc.RpcWorld GF) : Prop :=
  ∀ (m cfg logger : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.master ∗
      isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      masterFresh m cfg logger ∗ listUnset γ ∗ ⌜W.SS = rpcSS γ⌝ ∗
      RpcHttpAddr.rpcLisP W go!":7501" (connectReq defaultRPCPath) connectAns ∗
      replicaRpcs W ∗ muxOwner [] ∗ defaultSrvFresh ∗ threadTok ∗
      rpcReady ∗ net.rpc.srvEnv ∗ dialEnv ∗
      ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
