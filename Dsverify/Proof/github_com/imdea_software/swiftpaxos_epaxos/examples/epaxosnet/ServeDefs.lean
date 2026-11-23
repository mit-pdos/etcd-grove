/-
`serve`'s replica branch (`kit.go`'s `serve(id, addrs, port0)` for `id ≥ 2`; the lab's
`Proof/examples/epaxosnet/Server.lean`, `wp_serve_replica`, restated over Net's net/rpc and
`RpcHttpHyp`): the pure facts of the kit's constants and the specs of its helpers and of the
branch.

* `digit(n)` (`digit.spec`), `nodeConfig(id, port)` (`nodeConfig.spec`: alias `"n"` and the
  digit, `Port' = port`, no leader, a fresh zero `ProxyInfo`);
* `host(addr)` (`host.spec`: `hostB addr`, the part before the last `:`; `hostB_peer`: on replica
  node `k`'s server address, `replicaIp k`);
* `itoa(n)` (`itoa.spec`: a fresh slice of `itoaB n`, which is `fmt.decimalNat n`, `itoaB_eq`;
  so `ip + ":" + string(itoa(port + 1000))` is `rpcAddrOf k`, `listenAddr_eq`);
* `serve(k, sl, 7500)` for replica node `k` (`serveReplica.spec`): it returns only if
  `rpc.Register` or `net.Listen` fails (`http.Serve` returns only on a listener error).

`epaxosNew.spec isRep` is `epaxos/Link.lean`'s `EpaxosNewSpecEp isRep` verbatim (definitionally
equal: the `Link` passes `wp_New`); it is restated here because `EpaxosNewSpecEp` is declared in a
linking module, which neither this defs module nor a proof module may import ("Import tiers").
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerDefs
public import Net.Spec.net.Listen

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos

/-! ## Pure: `host`, `itoa` -/

/-- `host`'s search over the first `n` bytes of `s`, from the last: `s` up to the last `:` among
them, or `s` itself if there is none. -/
def hostAux (s : GoString) : Nat → GoString
  | 0 => s
  | n + 1 => if s[n]? = some (W8 58) then s.take n else hostAux s n

/-- `host(s)`: `s` up to its last `:` (`s` itself if it has none). -/
def hostB (s : GoString) : GoString := hostAux s s.length

/-- The decimal digits `itoa`'s loop prepends to its buffer while `n > 0`. -/
def itoaDigits (n : Nat) : List w8 :=
  if n = 0 then [] else itoaDigits (n / 10) ++ [W8 ((48 + n % 10 : Nat) : Int)]
termination_by n
decreasing_by omega

/-- `itoa(n)`: `n` in decimal (`"0"` for `0`). -/
def itoaB (n : Nat) : List w8 := if n = 0 then [W8 48] else itoaDigits n

theorem itoaDigits_zero : itoaDigits 0 = [] := by
  rw [itoaDigits]; simp

theorem itoaDigits_pos (n : Nat) (h : n ≠ 0) :
    itoaDigits n = itoaDigits (n / 10) ++ [W8 ((48 + n % 10 : Nat) : Int)] := by
  rw [itoaDigits]; simp [h]

theorem itoaDigits_eq (n : Nat) (h : n ≠ 0) : itoaDigits n = fmt.decimalNat n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [itoaDigits_pos n h]
    by_cases h10 : n < 10
    · rw [fmt.decimalNat_of_lt h10, Nat.div_eq_of_lt h10, itoaDigits_zero, Nat.mod_eq_of_lt h10]
      rfl
    · rw [fmt.decimalNat_of_ge (by omega), ih (n / 10) (by omega) (by omega)]
      rfl

/-- `itoa` writes `n` as `%d` does. -/
theorem itoaB_eq (n : Nat) : itoaB n = fmt.decimalNat n := by
  unfold itoaB
  split
  · subst_vars; rw [fmt.decimalNat_of_lt (by decide)]; rfl
  · exact itoaDigits_eq n (by assumption)

/-- The server addresses' entry of replica node `k` is its peer address. -/
theorem serverAddrs_peer (k : Nat) (hk : k ∈ replicaNodes) :
    serverAddrs[k - 1]? = some (peerAddrOf k) := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `host` of replica node `k`'s server address is its IP. -/
theorem hostB_peer (k : Nat) (hk : k ∈ replicaNodes) : hostB (peerAddrOf k) = replicaIp k := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The address replica node `k`'s `serve` listens at: `ip + ":" + string(itoa(port + 1000))`,
`port = 7500 + k`. -/
theorem listenAddr_eq (k : Nat) :
    replicaIp k ++ go!":" ++ itoaB (8500 + k) = rpcAddrOf k := by
  rw [itoaB_eq]
  rfl

/-- Replica node `k`'s rpc address, spelled out. -/
theorem rpcAddrOf_lit (k : Nat) (hk : k ∈ replicaNodes) :
    rpcAddrOf k = go!"127.0.0.1:85" ++ [W8 48, W8 ((48 + k : Nat) : Int)] := by
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp [rpcAddrOf, replicaIp, fmt.decimal, fmt.decimalNat_of_ge, fmt.decimalNat_of_lt,
      fmt.digitByte]

/-- A replica's rpc address is no wildcard: the listener at it takes only it. -/
theorem lisAccepts_rpcAddrOf (k : Nat) (hk : k ∈ replicaNodes) (a : GoString) :
    lisAccepts (rpcAddrOf k) a ↔ a = rpcAddrOf k := by
  have hw : wildPort (rpcAddrOf k) = none := by
    rw [rpcAddrOf_lit k hk]
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  unfold lisAccepts
  rw [hw]
  constructor
  · rintro (h | ⟨p, hp, -⟩)
    · exact h.symm
    · exact absurd hp (by simp)
  · intro h; exact Or.inl h.symm

theorem rpcAddrOf_listenOk (k : Nat) (hk : k ∈ replicaNodes) : listenOk (rpcAddrOf k) = true := by
  rw [rpcAddrOf_lit k hk]
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

theorem rpcAddrOf_addrOk (k : Nat) (hk : k ∈ replicaNodes) : addrOk (rpcAddrOf k) = true := by
  rw [rpcAddrOf_lit k hk]
  simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]
variable [log.Assumptions] [net.http.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

/-- `digit(n)`: the one-byte string of `'0' + n mod 10`. -/
abbrev digit.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! examples.epaxosnet.digit)) (Val #n))
  {{ RET #([W8 (uint.Z (W64 48 + n % W64 10))] : GoString); True }}

/-- `nodeConfig(id, port)`: a fresh configuration with protocol `"epaxos"`, alias `"n<digit>"`,
the port, no leader and a fresh zero `ProxyInfo`. -/
abbrev nodeConfig.spec : Prop :=
  ∀ (id port : w64),
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (App (Val (@! examples.epaxosnet.nodeConfig)) (Val #id)) (Val #port))
  {{ (cfg : Loc), RET #cfg; ∃ c : config.Config, cfg ↦ c ∗
      c.Proxy' ↦ (zeroValDef : config.ProxyInfo) ∗
      ⌜c.Protocol' = go!"epaxos" ∧ c.Alias' = go!"n" ++ [W8 (uint.Z (W64 48 + id % W64 10))] ∧
        c.Port' = port ∧ c.Leader' = null⌝ }}

/-- `host(addr)`: `addr` up to its last `:`. -/
abbrev host.spec : Prop :=
  ∀ (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! examples.epaxosnet.host)) (Val #addr))
  {{ RET #(hostB addr); True }}

/-- `itoa(n)`: a fresh slice of `n`'s decimal digits. -/
abbrev itoa.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! examples.epaxosnet.itoa)) (Val #n))
  {{ (sl : GoSlice), RET #sl; sl ↦* itoaB (uint.nat n) }}

/-- `epaxos.New`'s spec as `serve` calls it: `epaxos/Link.lean`'s `EpaxosNewSpecEp isRep`, verbatim
(the file header). -/
abbrev epaxosNew.spec (isRep : EpNames → Nat → Loc → IProp GF) : Prop :=
  ∀ (γ : EpNames) (k i : Nat) (L : List GoString) (sl : GoSlice) (cfg logger : Loc)
    (c : config.Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos ∗
      ⌜k ∈ replicaNodes ∧ L[i]? = some (peerAddrOf k)⌝ ∗ idTok γ i ∗ repFwStart γ i ∗
      epRepStart γ i ∗
      listFinal γ L ∗ sl ↦* L ∗ clientInvs γ ∗
      cfg ↦ c ∗ c.Proxy' ↦ (zeroValDef : config.ProxyInfo) ∗
      ⌜c.Leader' = null ∧ c.Port' = W64 (7500 + k)⌝ ∗
      logger ↦ (zeroValDef : dlog.Logger) }}
    (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! epaxos.New)) (Val #c.Alias')) (Val #(W64 i))) (Val #sl)) (Val #true))
      (Val #false)) (Val #false)) (Val #(W64 0))) (Val #false)) (Val #(W64 2))) (Val #cfg))
      (Val #logger))
  {{ (r : Loc), RET #r; isRep γ i r ∗ ⌜r ≠ null⌝ }}

/-- `serve(k, sl, 7500)` for replica node `k` (`sl` the server addresses, `Port0 = 7500`): from
net/rpc's fresh codec, the unclaimed `DefaultServeMux`, net/rpc's server variables, the bounds of
the threads and of the receipts, the rpc world `W` of the run (`rpcSS γ`), the master's address
and replica `k`'s rpc listener address serving it over HTTP, node `k`'s token, the registration
exchange and the replica addresses' protocols. It returns only if `rpc.Register` or `net.Listen`
fails (`http.Serve` returns only on a listener error). -/
abbrev serveReplica.spec [RpcHttpAddr GF] [RpcHttpHyp GF] : Prop :=
  ∀ (γ : EpNames) (W : net.rpc.RpcWorld GF) (k : Nat) (sl : GoSlice), k ∈ replicaNodes →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh ∗ RpcHttpHyp.muxOwner [] ∗
      net.rpc.srvEnv ∗ ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗
      sl ↦*□ serverAddrs ∗ ⌜W.SS = rpcSS γ⌝ ∗
      RpcHttpAddr.rpcAddrP W masterAddr (connectReq defaultRPCPath) connectAns ∗
      RpcHttpAddr.rpcLisP W (rpcAddrOf k) (connectReq defaultRPCPath) connectAns ∗
      nodeTok γ k ∗ inv regXN (regXInv γ (repStart γ)) ∗ clientInvs γ }}
    (App (App (App (Val (@! examples.epaxosnet.serve)) (Val #(W64 k))) (Val #sl))
      (Val #(W64 7500)))
  {{ RET #(); True }}

end specs

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

end Perennial
