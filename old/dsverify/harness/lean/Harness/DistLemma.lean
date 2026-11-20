/-
The generic lemma at the client node of a distributed test (M2, `notes/harness-m2-netconn.md`
section 3; `notes/harness-m1.md`, "M2: the lemma at the client node").

M1's `harness_main_safe` gives single-node safety (`SafeNet`) for the harness's `Main` from a
client spec. Here the same `Main` (the kit's `New`, then `clients.Run` with the kit's closure over
its client operations, then the check) runs on node 0 of a distributed test whose other nodes are
servers, and the network is Go's `net` (`netConnExt`, `Harness/SafeDist.lean`):

* `NetKitCode`: as `KitCode`, with `New` called on `Main`'s slice of node addresses (`newE sl`,
  the slice holding `addrs`).
* `NetClientSpec M K start`: as `ClientSpec`, with `New` from `start`, the client node's share of
  the network's start resources (its address's token, the protocols, the shared invariants),
  whatever the run makes it. It mentions no extension: the network enters only through `start`.
* `NetMainShape`: the kit's `Main` has the harness's shape, as M1's `MainShape`: the client node's
  boot WP from `start`, given any `NetClientSpec` from `start`, any checker spec with the kit's
  encodings and check call, and `Run`'s spec. A lab-side per-kit proof.
* `DistSpec`: what a run proves. Ghost names `Γs` of its choice; an update from the network's
  start resources (for each configured address, its token and the right to set its protocols) to
  the client node's share and each server's share, in which it allocates its shared invariants and
  sets the addresses' protocols (`addrs_set_proto`); the client spec at the client node from its
  share; and each server node's boot program from its share (`NodeBootWp`).
* `harness_dist_safe`: a `DistSpec`, a checker spec and `NetMainShape` give `SafeDist` for the
  client node followed by the servers. The client node's boot WP is `NetMainShape` applied to the
  client spec, the checker spec and `wp_Run` (M1's, unchanged); the servers' are the run's; the
  rest is `safeDist_of_boot`.

So the lab proves `Main` once per kit (`NetMainShape`), and a run proves only the client spec, the
servers, and the start that ties them together.
-/
module

public import Harness.SafeDist
public import Harness.Lemma

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode NetConn Dsv

namespace dsverify_lab.harness

set_option linter.unusedSectionVars false

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A net kit's code, as the client spec refers to it: as `KitCode` (the package `pkg`,
initialized by `initialize'`; the number of clients `nC`; the client operations `callE`, their
return values `ret`, error values `isErr` and input premises `pre`), with `New` called on a slice
of node addresses: `newE sl` is the call of `New` in `Main`, with `Main`'s other arguments, on the
slice `sl`, which holds `addrs` (`Main`'s address constants). -/
structure NetKitCode (M : Model) where
  pkg : GoString
  initialize' : val
  addrs : List GoString
  newE : GoSlice → Expr
  nC : Nat
  callE : Loc → w64 → M.Input → Expr
  ret : M.Output → val
  isErr : val → Prop
  pre : M.Input → Prop

/-- The client spec of a net kit's code `K` for the model `M`, at the client node, from its
share `start` of the network's start resources: as `ClientSpec`, with `New` taking `start` and the
address slice (persistent: `New` only reads it). -/
structure NetClientSpec (M : Model) (K : NetKitCode M) [IsPkgInit (IProp GF) K.pkg]
    [GetIsPkgInitWf (IProp GF) K.pkg] (start : IProp GF) where
  /-- the system's ghost names -/
  Γ : Type
  /-- `sys` is the system (persistent) -/
  is_sys : Loc → Γ → IProp GF
  /-- client `c` may call an operation (one at a time) -/
  client_tok : Γ → w64 → IProp GF
  /-- the abstract state (timeless, so a client keeps it in an invariant) -/
  own_state : Γ → M.State → IProp GF
  is_sys_persistent : ∀ sys γ, Persistent (is_sys sys γ)
  own_state_timeless : ∀ γ σ, Timeless (own_state γ σ)
  /-- the package's initialization -/
  wp_initialize' : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp K.pkg get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val K.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) K.pkg }}
  /-- `New` on the address slice, from the client node's share: the system, its initial state,
  one token per client -/
  wp_New : ∀ (sl : GoSlice),
    {{ isPkgInit (PROP := IProp GF) K.pkg ∗ start ∗ sl ↦*□ K.addrs }}
      (K.newE sl)
    {{ (sys : Loc) (γ : Γ), RET #sys; is_sys sys γ ∗ own_state γ M.init ∗
        [∗list] c ∈ List.range K.nC, client_tok γ (W64 ((c : Nat) : Int)) }}
  /-- each client operation: logically atomic at `↑clientN`, with a maybe-committed error (B) -/
  wp_Op : ∀ (sys : Loc) (γ : Γ) (c : w64) (i : M.Input), uint.nat c < K.nC → K.pre i →
    ⊢ isPkgInit (PROP := IProp GF) K.pkg -∗ is_sys sys γ -∗ client_tok γ c -∗
      opAwpMaybe (K.callE sys c i) (↑clientN) (own_state γ)
        (fun σ σ' o => iprop(own_state γ σ' ∗ ⌜M.step σ i σ' o⌝)) K.ret K.isErr (client_tok γ c)

end defs

section lemma

attribute [local instance] netConnExts netConnExtsSemantics netConnExtsInterp
  GooseGlobalGS.gooseInvGS netConnExts_has

/-- The kit's `Main` (the boot program of the node `client`) has the harness's shape: its boot
WP from any share `start`, given a client spec of the kit's code from `start`, any checker spec of
`Main`'s check call `checkE` with encodings `encI`/`encO` and precondition `ready`, and `Run`'s
spec. As M1's `MainShape`; `pkgInst`, `pkgWf`, `ready` and `checkE` as there. -/
def NetMainShape [GoGlobalContext] (M : Model) (K : NetKitCode M)
    [pkgInst : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics],
      IsPkgInit (IProp GF) K.pkg]
    [pkgWf : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics],
      GetIsPkgInitWf (IProp GF) K.pkg]
    (encI : M.Input → GoInterface) (encO : M.Output → GoInterface)
    (checkE : GoSlice → Expr)
    (ready : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics], IProp GF)
    (client : Node) : Prop :=
  ∀ [HeapGS .hasLC netDistGF] [go.Semantics] (_ : client.Assumptions)
    (start : IProp netDistGF),
    NetClientSpec (GF := netDistGF) M K start → (C : CheckerSpec (GF := netDistGF) M) →
    C.encI = encI → C.encO = encO → C.checkE = checkE → C.ready = ready →
    RunSpec (GF := netDistGF) M encI encO →
    start ⊢ ownGoState ∅ -∗
      WP (boot client.init client.main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }}

/-- What a run of a net kit proves, for the client node `client` (running the kit's `Main`), the
server nodes `servers` and the configuration `cfg`, at the global ghost state `G`:
* `Γs`, `start`: the run's ghost names, and an update from the network's start resources (each
  configured address's token, for `Listen`, and its unset protocols, for `addr_set_proto`) to the
  client node's share `clientRes γ` and server `i`'s share `serverRes γ i`; this is where the run
  allocates the invariants its nodes share and sets every address's protocols;
* `client_spec`: the client spec at the client node, from its share, for any local ghost state
  over `G`, under the Go semantics and the node's assumptions;
* `servers_boot`: each server node's boot program, from its share. -/
structure DistSpec [GoGlobalContext] (M : Model) (K : NetKitCode M)
    [pkgInst : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics],
      IsPkgInit (IProp GF) K.pkg]
    [pkgWf : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics],
      GetIsPkgInitWf (IProp GF) K.pkg]
    (client : Node) (servers : List Node) (cfg : NetConfig) [G : GooseGlobalGS .hasLC netDistGF]
    where
  /-- the run's ghost names, chosen in `start` -/
  Γs : Type
  /-- the client node's share -/
  clientRes : Γs → IProp netDistGF
  /-- server node `i`'s share (`i` counts from 0: node `i + 1`) -/
  serverRes : Γs → Nat → IProp netDistGF
  /-- the start: shared ghost state, invariants and protocols, from the network's resources -/
  start : ⊢ ([∗list] a ∈ cfg.addrs, addrTokG netDistGS a ∗ addrUnsetG netDistGS a) ={⊤}=∗
    ∃ γ : Γs, clientRes γ ∗ [∗list] i ↦ _nd ∈ servers, serverRes γ i
  /-- the client spec at the client node -/
  client_spec : ∀ (γ : Γs) (hG : HeapGS .hasLC netDistGF) (s : go.Semantics),
    hG.goose_globalGS = G →
    @Node.Assumptions client hG.goose_localGS.goose_go_local_context s.sem_fn →
    NetClientSpec (GF := netDistGF) M K (clientRes γ)
  /-- each server node's boot program -/
  servers_boot : ∀ (γ : Γs) (i : Nat) (nd : Node), servers[i]? = some nd →
    NodeBootWp nd (serverRes γ i)

/-- The generic lemma at the client node: a run's `DistSpec`, a checker spec with the kit's
encodings and check call, and `Main` of the harness's shape give the safety of the client node
and the servers, over Go's `net`. -/
theorem harness_dist_safe [GoGlobalContext] (M : Model) (K : NetKitCode M)
    [pkgInst : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics],
      IsPkgInit (IProp GF) K.pkg]
    [pkgWf : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics],
      GetIsPkgInitWf (IProp GF) K.pkg]
    (encI : M.Input → GoInterface) (encO : M.Output → GoInterface)
    (checkE : GoSlice → Expr)
    (ready : ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics], IProp GF)
    {client : Node} {servers : List Node} {cfg : NetConfig}
    (Hcfg : cfg.WellFormed (servers.length + 1))
    (hC : ∀ [HeapGS .hasLC netDistGF] [go.Semantics], client.Assumptions →
      ∃ C : CheckerSpec (GF := netDistGF) M, C.encI = encI ∧ C.encO = encO ∧ C.checkE = checkE ∧
        C.ready = ready)
    (hRun : ∀ [HeapGS .hasLC netDistGF] [go.Semantics], client.Assumptions →
      dsverify_lab.harness.clients.Assumptions)
    (hMain : NetMainShape M K (pkgInst := pkgInst) (pkgWf := pkgWf) encI encO checkE ready client)
    (hD : ∀ [GooseGlobalGS .hasLC netDistGF],
      Nonempty (DistSpec M K (pkgInst := pkgInst) (pkgWf := pkgWf) client servers cfg))
    (hArgs : client.args = [] := by rfl) :
    SafeDist (client :: servers) cfg := by
  apply safeDist_of_boot _ _ Hcfg
  intro G
  obtain ⟨⟨Γs, clientRes, serverRes, hstart, hspec, hservers⟩⟩ := hD
  iintro Hs
  imod hstart $$ Hs with ⟨%γ, Hc, Hsv⟩
  imodintro
  iexists fun i => Nat.casesOn i (clientRes γ) (fun j => serverRes γ j)
  isplitr
  · ipureintro
    intro i nd hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hnd
      subst hnd
      intro hG s hGG hA
      subst hGG
      have S := hspec γ hG s rfl hA
      obtain ⟨C, h1, h2, h3, h4⟩ := hC hA
      haveI := hRun hA
      rw [Node.boot_nil _ hArgs]
      exact hMain hA _ S C h1 h2 h3 h4 (wp_Run M encI encO)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hnd
      exact hservers γ j nd hnd
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hc]
    · iexact Hc
    · iexact Hsv

end lemma

end dsverify_lab.harness

end Perennial
