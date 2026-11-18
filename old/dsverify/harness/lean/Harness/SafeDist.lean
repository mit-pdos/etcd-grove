/-
The statement for a distributed test (M2a, M2b; `notes/harness-m2a.md`): several nodes, each a
Go program that talks to the others through Go's `net`, whose semantics is the TCP extension
`netConnExt` (`Harness/GooseLang/Ext/NetConn/Impl.lean`).

A node is a Go package's boot program (`Node.boot`: initialize the package, then call its
function `main` with the node's constant arguments; with none, `Dsv.boot init main`) and the class of facts goose's translation assumes of the Go context (the
package's generated `Assumptions`, and `net.model.Assumptions` for the trusted layouts of the
`net` model). The system is a list of nodes run by Perennial's distributed semantics
(`DistNsteps`, `DistLang.lean`): every node has its own threads, heap and Go context, and they
share the extension's global state, the network.

The addresses are data (`NetConfig`): node `i`'s IPv4 address `ips[i]`, and the endpoints
("IP:port") the nodes may listen on and dial. The extension matches address strings literally
and treats a `Listen` or `Dial` on any other string as stuck, so a proof that the nodes are safe
also proves that they only use these strings. The literal match is right only in the deployment
the rig builds (one network namespace and one IP per node); `NetConfig.WellFormed` states what
that needs of the configuration: one IP per node, distinct, ordinary unicast (not 0.0.0.0,
loopback, multicast or broadcast, which name a different or no host from each node), every
endpoint on one of those IPs with a port in 1..65535 (port 0 asks for any port), each spelled
canonically (`Endpoint.spell`: decimal octets and port without leading zeros), no endpoint
twice. `WellFormed` is decidable; a kit proves it of its configuration by `decide`.

Node `i` runs on IP `ips[i]`: the extension's local state at node `i` is `ips[i]`, spelled
(`NodeIpStart`), which is what a `Listen` on a wildcard host (`":port"`, `"0.0.0.0:port"`,
`"[::]:port"`) resolves to (`NetConn.listenAddr`), as in the rig (one network namespace and one IP
per node).

`SafeDist nodes cfg` says: `cfg` is well formed, and from a start where every node has its Go
context (meeting its package's assumptions), no package initialized and one thread, node `i` is
on IP `ips[i]`, and the network has the configured addresses and no listener or connection
(`NetState.empty cfg.addrs`), in every execution, at every node,
* if the main thread finished, it returned `#()`;
* no thread is stuck;
* no thread has an unrecovered panic
(`Dsv.Ok`, the single-node statement's conclusion, at each node). It is closed off by
`goose_dist_adequacy`, through the bridge `safeDist_of_wp`, whose premise is a WP of every
node's boot program from the extension's start resources: for each configured address, the
token to listen on it and the right to set its protocols (`Specs.lean`); node `i`'s WP may use
that its IP is `ips[i]` (`nodeIp`, from the extension's local start resources: `NodeBootWpAt`).

This file depends on `DsvStatement`, Perennial and the extension only; nothing in it is specific
to a target or to the harness's other modules.
-/
module

public import DsvStatement
public import Perennial.GooseLang.DistAdequacy
public import Harness.GooseLang.Ext.NetConn.Specs

@[expose] public section

noncomputable section

namespace Perennial

namespace Dsv

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode NetConn

/-! ## Addresses -/

/-- An IPv4 address, by its four octets. -/
structure IPv4 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
deriving DecidableEq

/-- An ordinary unicast address of a host: octets below 256; not 0.0.0.0/8 ("this host"),
not 127.0.0.0/8 (loopback: each node's own), not 224.0.0.0 and above (multicast, reserved,
broadcast). -/
def IPv4.Unicast (ip : IPv4) : Prop :=
  ip.a < 224 ∧ ip.b < 256 ∧ ip.c < 256 ∧ ip.d < 256 ∧ ip.a ≠ 0 ∧ ip.a ≠ 127

instance (ip : IPv4) : Decidable ip.Unicast := by unfold IPv4.Unicast; infer_instance

/-- The decimal digits of `n`, most significant first, no leading zeros (`fuel` bounds the
recursion; `n + 1` is enough). -/
def decDigits : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n < 10 then [n] else decDigits fuel (n / 10) ++ [n % 10]

/-- `n` in decimal, without leading zeros, as ASCII bytes (as `Nat.repr`, but reducible by
`decide`). -/
def decSpell (n : Nat) : GoString := (decDigits (n + 1) n).map (fun d => BitVec.ofNat 8 (48 + d))

/-- "a.b.c.d", decimal without leading zeros. -/
def IPv4.spell (ip : IPv4) : GoString :=
  decSpell ip.a ++ [46#8] ++ decSpell ip.b ++ [46#8] ++ decSpell ip.c ++ [46#8] ++ decSpell ip.d

/-- A TCP endpoint: an IP and a port. -/
structure Endpoint where
  ip : IPv4
  port : Nat
deriving DecidableEq

/-- "a.b.c.d:port", as a Go string, the form Go's `net.Listen` and `net.Dial` take. -/
def Endpoint.spell (e : Endpoint) : GoString :=
  e.ip.spell ++ [58#8] ++ decSpell e.port

/-- A network configuration: node `i`'s IP is `ips[i]`; `endpoints` are the addresses the nodes
listen on and dial. -/
structure NetConfig where
  ips : List IPv4
  endpoints : List Endpoint

/-- The configured addresses, as strings. -/
def NetConfig.addrs (cfg : NetConfig) : List GoString := cfg.endpoints.map Endpoint.spell

/-- The deployment assumption on the addresses (see the file's comment), for `n` nodes. -/
structure NetConfig.WellFormed (cfg : NetConfig) (n : Nat) : Prop where
  ips_length : cfg.ips.length = n
  ips_unicast : ∀ ip ∈ cfg.ips, ip.Unicast
  ips_nodup : cfg.ips.Nodup
  endpoints_ip : ∀ e ∈ cfg.endpoints, e.ip ∈ cfg.ips
  endpoints_port : ∀ e ∈ cfg.endpoints, 0 < e.port ∧ e.port < 65536
  addrs_nodup : cfg.addrs.Nodup

instance (cfg : NetConfig) (n : Nat) : Decidable (cfg.WellFormed n) :=
  decidable_of_iff (cfg.ips.length = n ∧ (∀ ip ∈ cfg.ips, ip.Unicast) ∧ cfg.ips.Nodup ∧
      (∀ e ∈ cfg.endpoints, e.ip ∈ cfg.ips) ∧
      (∀ e ∈ cfg.endpoints, 0 < e.port ∧ e.port < 65536) ∧ cfg.addrs.Nodup)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- The first byte of a non-empty spelling: neither `':'`, `'0'` nor `'['` (`headTame`). -/
def headTame (s : GoString) : Bool :=
  match s with
  | c :: _ => c != 58#8 && c != 48#8 && c != 91#8
  | [] => false

theorem decSpell_headTame : ∀ n, n < 224 → n ≠ 0 → headTame (decSpell n) = true := by
  decide +kernel

/-- A configured address of a well-formed configuration has no wildcard host (it starts with
the first octet of a unicast IP, a digit 1..9), so `Listen` binds it as spelled. -/
theorem NetConfig.WellFormed.addrs_tame {cfg : NetConfig} {n : Nat} (h : cfg.WellFormed n) :
    ∀ a ∈ cfg.addrs, wildcardPort a = none := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  obtain ⟨h1, -, -, -, h5, -⟩ := h.ips_unicast e.ip (h.endpoints_ip e he)
  have ht := decSpell_headTame e.ip.a h1 h5
  unfold Endpoint.spell IPv4.spell
  generalize decSpell e.ip.a = d at ht
  match d, ht with
  | c :: rest, ht =>
    simp only [headTame, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
    simp only [List.cons_append]
    exact wildcardPort_head c _ ht.1.1 ht.1.2 ht.2

/-- An example: three nodes on the rig's subnet, a server on each. -/
example : NetConfig.WellFormed
    ⟨[⟨10, 0, 0, 1⟩, ⟨10, 0, 0, 2⟩, ⟨10, 0, 0, 3⟩],
     [⟨⟨10, 0, 0, 1⟩, 8000⟩, ⟨⟨10, 0, 0, 2⟩, 8000⟩, ⟨⟨10, 0, 0, 3⟩, 8000⟩]⟩ 3 := by
  decide

example : Endpoint.spell ⟨⟨10, 0, 0, 1⟩, 8000⟩ = go!"10.0.0.1:8000" := by decide

/-! ## The extension list: TCP alone -/

/-- The extensions of a distributed test: the TCP extension alone. -/
@[reducible] def netConnExts : GooseExts := ⟨[netConnExt]⟩

attribute [local instance] netConnExts

@[reducible] def netConnExtsSemantics : GooseSemantics := ⟨(netConn_semantics, ⟨⟩)⟩

attribute [local instance] netConnExtsSemantics

instance netConnExts_elem : ElemExt netConnExt := ⟨rfl⟩

/-! ## The statement -/

section statement
variable [GoGlobalContext]

/-- A node: its package's assumptions on the Go context (for a kit, the conjunction of the
package's generated `Assumptions` and `net.model.Assumptions`), its `initialize'`, the name
of the function its boot program calls, and the constant arguments it calls it with (kit v2,
`notes/kit-v2.md` decision 4: server node `k` runs `Server(k)`). No arguments (`[]`, the
default) is a call of a function with no parameters, as the single-node statement's
`boot nd.init nd.main` (`Node.boot_nil`). -/
structure Node where
  Assumptions : [GoLocalContext] → [GoSemanticsFunctions] → Prop
  init : val
  main : GoString
  args : List val := []

/-- The call of `main` with `args`, as goose calls a function: resolve it, then apply it to each
argument in turn, or to `#()` if it has no parameters. -/
def callArgs (main : GoString) : List val → Expr
  | [] => App (App (Val (GoInstruction (FuncResolve main []))) (Val #())) (Val #())
  | a :: rest => (a :: rest).foldl (fun e x => App e (Val x))
      (App (Val (GoInstruction (FuncResolve main []))) (Val #()))

/-- A node's boot program: initialize the package, then call `main` with `args`. -/
def Node.boot (nd : Node) : Expr :=
  Seq (App (Val nd.init) (Val #())) (callArgs nd.main nd.args)

/-- With no arguments, a node's boot program is the single-node statement's. -/
theorem Node.boot_nil (nd : Node) (h : nd.args = []) :
    nd.boot = _root_.Perennial.Dsv.boot nd.init nd.main := by
  unfold Node.boot _root_.Perennial.Dsv.boot; rw [h]; rfl

/-- `Node.boot_nil` for a node written as a structure instance. -/
theorem Node.boot_mk (A : [GoLocalContext] → [GoSemanticsFunctions] → Prop) (init : val)
    (main : GoString) :
    ({ Assumptions := A, init := init, main := main } : Node).boot =
      _root_.Perennial.Dsv.boot init main := rfl

/-- A node's start state: a Go context with the Go semantics in which its package's
assumptions hold, no package initialized, the main thread only. (The extension has no local
state.) -/
structure NodeStart (nd : Node) (σ : state) : Prop where
  sem : ∃ s : @go.Semantics _ σ.goState.goLctx _,
    @Node.Assumptions nd σ.goState.goLctx s.sem_fn
  pkgs : σ.goState.packageState = ∅
  threads : σ.threads = 1

/-- Node `σ` is on IP `ip`: the extension's local state (the node's IP, which a `Listen` on a
wildcard host resolves to) is `ip`, spelled as in the configured addresses. -/
def NodeIpStart (ip : IPv4) (σ : state) : Prop :=
  extLocal netConnExt σ.world = ip.spell

/-- The network's start: the configured addresses, no listener, no connection. -/
def NetConnStart (cfg : NetConfig) (g : GlobalState) : Prop :=
  extGlobal netConnExt g.globalWorld = NetState.empty cfg.addrs

/-- The configuration in which node `i` runs its boot program from `σs[i]`. -/
def distStart (nodes : List Node) (σs : List state) (g : GlobalState) : DistCfg :=
  distInit (nodes.zipWith (fun nd σ => (nd.boot, σ)) σs) g

/-- The distributed statement: the configuration is well formed, and every execution of the
nodes from a start (node `i` on IP `cfg.ips[i]`) is safe at every node. -/
def SafeDist (nodes : List Node) (cfg : NetConfig) : Prop :=
  cfg.WellFormed nodes.length ∧
  ∀ (σs : List state) (g : GlobalState), σs.length = nodes.length →
    (∀ (i : Nat) (nd : Node) (σ : state), nodes[i]? = some nd → σs[i]? = some σ → NodeStart nd σ) →
    (∀ (i : Nat) (ip : IPv4) (σ : state), cfg.ips[i]? = some ip → σs[i]? = some σ →
      NodeIpStart ip σ) →
    NetConnStart cfg g →
  ∀ (n : Nat) (κs : List Observation) (c : DistCfg),
    DistNsteps n (distStart nodes σs g) κs c →
  ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
    Ok tp ((σ, c.global) : CfgState)

end statement

/-! ## The bridge (M2b)

At the extension's ghost state (`netConn_interp`, `Specs.lean`) and a fixed `BundledGFunctors`
(`netDistGF`, as `DsvNet`'s `netGF`). The proof obligation `Hwp` is `goose_dist_adequacy`'s,
quantified over the nodes' start states, with the extension's start resources spelled out: for
each configured address, its token (`addrTokG`, for `Listen`) and its unset protocols
(`addrUnsetG`, for `addr_set_proto`). -/

@[reducible] def netConnExtsInterp : GooseInterp := ⟨(netConn_interp, ⟨⟩)⟩

attribute [local instance] netConnExtsInterp GooseGlobalGS.gooseInvGS

set_option linter.defProp false in
/-- `netConnExts` has the extension, with its semantics and ghost state. -/
@[reducible] def netConnExts_has : HasExt netConnExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] netConnExts_has

section bridge
variable [GoGlobalContext]

/-- Ghost state for `netConnExts`: Perennial's (invariants, credits, heap, prophecies, Go
state) and an `AllG` slot, which the extension's ghost state uses. -/
def netDistGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 10 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

instance netDistGpreS : GooseGpreS netDistGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (allGOfSlot 0 rfl, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨10, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

/-- The extension's global ghost state, under `netConnExts`. -/
abbrev netDistGS [GooseGlobalGS .hasLC netDistGF] : NetConnGS netDistGF :=
  extGlobalGS netConnExt (hlc := .hasLC)

/-- The bridge: WPs of the nodes' boot programs (postcondition `#()`), from the extension's
start resources for the configured addresses, give `SafeDist`, for a well-formed
configuration. An agent proves `Hwp`. -/
theorem safeDist_of_wp (nodes : List Node) (cfg : NetConfig)
    (Hcfg : cfg.WellFormed nodes.length)
    (Hwp : ∀ [GooseGlobalGS .hasLC netDistGF] (T : Nat) (σs : List state) (g : GlobalState),
      σs.length = nodes.length →
      (∀ (i : Nat) (nd : Node) (σ : state),
        nodes[i]? = some nd → σs[i]? = some σ → NodeStart nd σ) →
      (∀ (i : Nat) (ip : IPv4) (σ : state), cfg.ips[i]? = some ip → σs[i]? = some σ →
        NodeIpStart ip σ) →
      NetConnStart cfg g →
      ⊢ ([∗list] a ∈ cfg.addrs, addrTokG netDistGS a ∗ addrUnsetG netDistGS a) ={⊤}=∗
        [∗list] _i ↦ n ∈ nodes.zipWith (fun nd σ => (nd.boot, σ)) σs,
          nodeWp T n.1 n.2 (fun v => v = #())) :
    SafeDist nodes cfg := by
  refine ⟨Hcfg, ?_⟩
  intro σs g hlen hstart hips hnet n κs c hsteps i tp σ hi
  have hmem : ∀ x, x ∈ nodes.zipWith (fun nd σ => (nd.boot, σ)) σs →
      ∃ (j : Nat) (nd : Node), nodes[j]? = some nd ∧ σs[j]? = some x.2 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_zipWith]
    refine ⟨j, nodes[j]'(by simp at hj; omega), by simp, by simp⟩
  have H := goose_dist_adequacy (GF := netDistGF) (n + 1) (n + 2)
    (nodes.zipWith (fun (nd : Node) (σ : state) => (nd.boot, σ)) σs) g
    (fun _ v => v = #())
    (fun _ p h => intoVal_ne_PanicV () p h.symm)
    ?_ (fun _ _ => ⟨trivial, trivial⟩) ?_ n κs c hsteps (Nat.lt_succ_self n) ?_
    (DistThreadsBelow.of_single ?_) i tp σ hi
  · exact ⟨H.1, H.2.1, H.2.2⟩
  · -- the extension's start: no listener, no connection, distinct addresses
    have h1 : g.globalWorld.1 = NetState.empty cfg.addrs := hnet
    refine ⟨?_, trivial⟩
    show (g.globalWorld.1).listeners = ∅ ∧ (g.globalWorld.1).conns = ∅ ∧
      (g.globalWorld.1).addrs.Nodup ∧ ∀ a ∈ (g.globalWorld.1).addrs, wildcardPort a = none
    rw [h1]
    exact ⟨rfl, rfl, Hcfg.addrs_nodup, Hcfg.addrs_tame⟩
  · intro G _
    have h1 : g.globalWorld.1 = NetState.empty cfg.addrs := hnet
    have Hg : extsGlobalStart (GF := netDistGF) g.globalWorld ⊢
        [∗list] a ∈ cfg.addrs, addrTokG netDistGS a ∗ addrUnsetG netDistGS a := by
      refine sep_elim_left.trans ?_
      show netStart _ g.globalWorld.1 ⊢ _
      rw [h1]
      exact .rfl
    iintro Hs
    iapply Hwp (n + 2) σs g hlen hstart hips hnet
    iapply Hg $$ Hs
  · intro x hx
    obtain ⟨j, nd, hnd, hσ⟩ := hmem x hx
    exact (hstart j nd x.2 hnd hσ).threads
  · intro j tp' σ' hj
    simp only [distInit, List.getElem?_map] at hj
    obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hj
    simp only [Prod.mk.injEq] at hx'
    obtain ⟨-, rfl⟩ := hx'
    obtain ⟨k, nd, hnd, hσ⟩ := hmem x (List.mem_of_getElem? hx)
    exact (hstart k nd x.2 hnd hσ).threads

/-- A node's obligation (`nodeWp`, in `safeDist_of_wp`'s premise) from a WP of its boot program,
proved for any local ghost state `hG` over the global one, under the Go semantics and the
package's assumptions its start gives (`NodeStart`), from no package initialized (M2c). The
node's share of the start resources is `P`. -/
theorem nodeWp_of_boot [G : GooseGlobalGS .hasLC netDistGF] (T : Nat) (nd : Node) (σ : state)
    (P : IProp netDistGF) (hst : NodeStart nd σ)
    (H : ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics), hG.goose_globalGS = G →
      @Node.Assumptions nd hG.goose_localGS.goose_go_local_context s.sem_fn →
      P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
        WP nd.boot @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}) :
    P ⊢ nodeWp T nd.boot σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  obtain ⟨s, hA⟩ := hst.sem
  have hpk := hst.pkgs
  obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
  unfold nodeWpBody
  iintro %_ %hL _ Hgs _
  subst hL
  rw [hpk]
  imodintro
  iapply H ⟨G, ⟨Lexts, σ.goState.goLctx, Lheap, Lgs, Lthr, Lcr⟩⟩ s rfl hA $$ HP Hgs

/-! ### Plumbing for many nodes (the ergonomics pass after M2c)

`NodeBootWp nd P`: node `nd`'s boot program is safe from resources `P`, the premise of
`nodeWp_of_boot`; `NodeBootWpAt nd ip P`, the same given that the node's IP is `ip` (`nodeIp`),
the premise of `nodeWp_of_bootAt` and `safeDist_of_bootAt`. `safeDist_of_boot` is `safeDist_of_wp` with the obligation stated per node:
from the extension's start resources, an update to resources `Ps i` for each node `i` (in one
`[∗list]`, indexed by node) and, for each node, its `NodeBootWp` from its share. The nodes' start
states, the step bound and the `zipWith` are handled here. `addrs_set_proto` sets the protocols
of every configured address at once. -/

/-- Node `nd`'s boot program is safe from `P`: for any local ghost state over the global one,
under the Go semantics and the package's assumptions its start gives, from no package
initialized. -/
def NodeBootWp [G : GooseGlobalGS .hasLC netDistGF] (nd : Node) (P : IProp netDistGF) : Prop :=
  ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics), hG.goose_globalGS = G →
    @Node.Assumptions nd hG.goose_localGS.goose_go_local_context s.sem_fn →
    P ⊢ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP nd.boot @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

theorem bigSepL_nodeWp [G : GooseGlobalGS .hasLC netDistGF] (T : Nat) :
    ∀ (nodes : List Node) (σs : List state) (Ps : Nat → IProp netDistGF),
    σs.length = nodes.length →
    (∀ (i : Nat) (nd : Node) (σ : state), nodes[i]? = some nd → σs[i]? = some σ →
      Ps i ⊢ nodeWp T nd.boot σ (fun v => v = #())) →
    ([∗list] i ↦ _nd ∈ nodes, Ps i) ⊢
      [∗list] _i ↦ n ∈ nodes.zipWith (fun nd σ => (nd.boot, σ)) σs,
        nodeWp T n.1 n.2 (fun v => v = #())
  | [], σs, _, _, _ => by
    simp only [List.zipWith_nil_left]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | nd :: nodes, [], _, hl, _ => by simp at hl
  | nd :: nodes, σ :: σs, Ps, hl, H => by
    simp only [List.zipWith_cons_cons]
    iintro Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H0, Hr⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · iapply H 0 nd σ rfl rfl $$ H0
    · iapply bigSepL_nodeWp T nodes σs (fun i => Ps (i + 1)) (by simpa using hl)
        (fun i nd' σ' h1 h2 => H (i + 1) nd' σ' h1 h2) $$ Hr

/-- The extension's local start resources at a node: its IP (`netIp`) is its local state. -/
theorem netConn_localStart [L : GooseLocalGS netDistGF] (w : ExtsLocalState netConnExts.exts) :
    extsLocalStart (GF := netDistGF) w ⊢ ⌜netIp (L := L) = extLocal netConnExt w⌝ :=
  sep_elim_left

/-- Node `nd`'s boot program, on IP `ip`, is safe from `P`: as `NodeBootWp`, with the fact that
the node's IP is `ip` (`nodeIp`, for a `Listen` on a wildcard host: `wp_ListenWild`). -/
def NodeBootWpAt [G : GooseGlobalGS .hasLC netDistGF] (nd : Node) (ip : IPv4)
    (P : IProp netDistGF) : Prop :=
  ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics), hG.goose_globalGS = G →
    @Node.Assumptions nd hG.goose_localGS.goose_go_local_context s.sem_fn →
    P ⊢ nodeIp (L := hG.goose_localGS) ip.spell -∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ -∗
      WP nd.boot @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- A boot program safe without the node's IP is safe on any IP. -/
theorem NodeBootWp.at [G : GooseGlobalGS .hasLC netDistGF] {nd : Node} {P : IProp netDistGF}
    (H : NodeBootWp nd P) (ip : IPv4) : NodeBootWpAt nd ip P := by
  intro hG s hGG hA
  iintro HP - Hgs
  iapply H hG s hGG hA $$ HP Hgs

/-- `nodeWp_of_boot` for a node on IP `ip` (`NodeIpStart`): its boot program may use `nodeIp`,
from the extension's local start resources. -/
theorem nodeWp_of_bootAt [G : GooseGlobalGS .hasLC netDistGF] (T : Nat) (nd : Node) (ip : IPv4)
    (σ : state) (P : IProp netDistGF) (hst : NodeStart nd σ) (hip : NodeIpStart ip σ)
    (H : NodeBootWpAt nd ip P) :
    P ⊢ nodeWp T nd.boot σ (fun v => v = #()) := by
  unfold nodeWp
  iintro HP %L
  obtain ⟨s, hA⟩ := hst.sem
  have hpk := hst.pkgs
  obtain ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩ := L
  unfold nodeWpBody
  iintro %_ %hL Hls Hgs _
  subst hL
  rw [hpk]
  ihave %Hip := netConn_localStart (L := ⟨Lexts, σ.goState.goLctx, Lheap, Lgs, Lthr, Lcr⟩)
    σ.world $$ Hls
  imodintro
  iapply H ⟨G, ⟨Lexts, σ.goState.goLctx, Lheap, Lgs, Lthr, Lcr⟩⟩ s rfl hA $$ HP [] Hgs
  ipureintro
  exact Hip.trans hip

/-- `safeDist_of_wp` with the obligation per node: an update from the extension's start
resources to a share `Ps i` for each node `i`, and each node's boot program safe from its
share on its IP `cfg.ips[i]` (`NodeBootWpAt`). -/
theorem safeDist_of_bootAt (nodes : List Node) (cfg : NetConfig)
    (Hcfg : cfg.WellFormed nodes.length)
    (Hstart : ∀ [GooseGlobalGS .hasLC netDistGF],
      ⊢ ([∗list] a ∈ cfg.addrs, addrTokG netDistGS a ∗ addrUnsetG netDistGS a) ={⊤}=∗
        ∃ Ps : Nat → IProp netDistGF,
          ⌜∀ (i : Nat) (nd : Node) (ip : IPv4), nodes[i]? = some nd → cfg.ips[i]? = some ip →
            NodeBootWpAt nd ip (Ps i)⌝ ∗
          [∗list] i ↦ _nd ∈ nodes, Ps i) :
    SafeDist nodes cfg := by
  apply safeDist_of_wp _ _ Hcfg
  intro G T σs g hlen hstart hips _
  iintro Hs
  imod Hstart $$ Hs with ⟨%Ps, %HP, HPs⟩
  imodintro
  iapply bigSepL_nodeWp T nodes σs Ps hlen ?_ $$ HPs
  intro i nd σ hnd hσ
  have hi : i < cfg.ips.length := by
    rw [Hcfg.ips_length]; exact (List.getElem?_eq_some_iff.mp hnd).1
  have hip : cfg.ips[i]? = some cfg.ips[i] := List.getElem?_eq_getElem hi
  exact nodeWp_of_bootAt T nd cfg.ips[i] σ (Ps i) (hstart i nd σ hnd hσ)
    (hips i _ σ hip hσ) (HP i nd _ hnd hip)

/-- `safeDist_of_bootAt` for boot programs that do not use their node's IP (`NodeBootWp`). -/
theorem safeDist_of_boot (nodes : List Node) (cfg : NetConfig)
    (Hcfg : cfg.WellFormed nodes.length)
    (Hstart : ∀ [GooseGlobalGS .hasLC netDistGF],
      ⊢ ([∗list] a ∈ cfg.addrs, addrTokG netDistGS a ∗ addrUnsetG netDistGS a) ={⊤}=∗
        ∃ Ps : Nat → IProp netDistGF,
          ⌜∀ (i : Nat) (nd : Node), nodes[i]? = some nd → NodeBootWp nd (Ps i)⌝ ∗
          [∗list] i ↦ _nd ∈ nodes, Ps i) :
    SafeDist nodes cfg := by
  apply safeDist_of_bootAt _ _ Hcfg
  intro G
  iintro Hs
  imod Hstart $$ Hs with ⟨%Ps, %HP, HPs⟩
  imodintro
  iexists Ps
  iframe HPs
  ipureintro
  intro i nd ip hnd _
  exact (HP i nd hnd).at ip

omit [GoGlobalContext] in
/-- Set the protocols of every configured address at once (`addr_set_proto`), `P a` for what
dialers of `a` write and `Q a` for what its acceptors write; the tokens are kept. -/
theorem addrs_set_proto [GooseGlobalGS .hasLC netDistGF] (P Q : GoString → Proto netDistGF) :
    ∀ addrs : List GoString,
    ⊢ ([∗list] a ∈ addrs, addrTokG netDistGS a ∗ addrUnsetG netDistGS a) ==∗
      ([∗list] a ∈ addrs, addrTokG netDistGS a) ∗
      [∗list] a ∈ addrs, addrProtoG netDistGS a (P a) (Q a)
  | [] => by
    iintro -
    imodintro
    isplitl <;> iapply BigSepL.bigSepL_nil.2 <;> iempintro
  | a :: addrs => by
    iintro Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨⟨Ht, Hu⟩, Hs⟩
    imod addr_set_proto netDistGS a (P a) (Q a) $$ Hu with #Hp
    imod addrs_set_proto P Q addrs $$ Hs with ⟨Hts, #Hps⟩
    imodintro
    isplitl [Ht Hts]
    · iapply BigSepL.bigSepL_cons.2; iframe Ht Hts
    · iapply BigSepL.bigSepL_cons.2; iframe Hp Hps

end bridge

end Dsv

end Perennial
