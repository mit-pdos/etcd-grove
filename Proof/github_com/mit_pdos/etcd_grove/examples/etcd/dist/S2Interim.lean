/- Lean-first (no Rocq counterpart).

# Interim cross-machine vocabulary for etcd's distributed theorems (until #24's S2 switch)

`notes/putget-dist-plan.md` §12. What a member publishes to its clients, and the address fact, since
phase 7 S2's interface switch (2026-11-24) #24's own `grpcAddrAt a (etcdSvc γE mid)` with only the
table `etcdSvc` axiomatized (see its docstring). The publication machinery is #24's §1.3 over
`dghostVar`, with a smaller view (`EnvView`: the KV state variable's name, the only name the putget
client's statements read; #24's view, O1, adds fields when its table needs them).

One axiom (A1 `etcdSvc`; until the switch A1 was the opaque predicate `etcdAddrRaw` and A2 the start law
`etcdAddr_set`, now a theorem); the function axioms A3-A5 are in `ServeDist.lean`,
`ClientPutDist.lean` and `ClientGetDist.lean`. Every other declaration is a definition or a proved
law. The publication's laws: `envPub_start` (allocation), `env_publish` (the member's step),
`envAt_agree` (one view per name) and `envAt_pub` (a client reads `▷ □ Pub ν`: the invariant's
content is not timeless, so it comes under a later, review F2).
-/
module

public import GooseLang.Ext.Net.Proto
public import Proof.google_golang_org.grpc.InvGrpcWire
public import Perennial.Ghost.DGhostVar
public import Proof.go_etcd_io.etcd.client.v3.PutThenGet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net

/-! ## The view a member publishes -/

/-- **What a member publishes to its clients** (heap-free, countable): the ghost name of its KV
store's state variable (`KVNames.st` of its read names, `etcdKV`'s). The putget client's
statements read nothing else of the member: `client.putGetInv γ` reads `γ` only through
`γ.kv.st` (`putGetInv_st`). (#24's `EnvView`, O1, is larger; its read names are not countable as
they stand, `notes/putget-dist-plan.md` §12.) -/
structure EnvView where
  st : GName
deriving DecidableEq, Inhabited

/-- **The view a started member publishes** (its read names' KV state variable's name): what
`Serve_dist` serves at (`ν = memberView ρ`, review 24's fix 2: an equation of the whole view, so that
the axiom's statement does not change when `EnvView` gains #24's fields and `memberView` with it). -/
abbrev memberView [GooseExts] (ρ : ReqNames) : EnvView := ⟨ρ.rd.kv.st⟩

instance EnvView.countable : Pos.Countable EnvView :=
  Pos.Countable.ofInjective (fun ν => Pos.Countable.encode ν.st) (fun a b h => by
    have h' : a.st = b.st := Pos.encode_inj h
    cases a; cases b
    exact congrArg EnvView.mk h')

section pub
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The publication invariant's namespace, one per publication name. -/
def envPubN (γE : GName) : Namespace := (nroot.@"etcd_dist_envpub").@γE

/-- **The member's half of the publication token** (exclusive; not published yet). -/
def envPubHalf (γE : GName) : IProp GF :=
  dghostVar γE (.own (1 : Qp).half) (none : Option EnvView)

/-- **Published: the member's view is `ν`** (persistent, one-shot: `envAt_agree`). -/
def envAt (γE : GName) (ν : EnvView) : IProp GF := dghostVar γE .discard (some ν)

instance envAt_persistent (γE : GName) (ν : EnvView) : Persistent (envAt (GF := GF) γE ν) := by
  unfold envAt; infer_instance

instance envAt_timeless (γE : GName) (ν : EnvView) : Timeless (envAt (GF := GF) γE ν) := by
  unfold envAt; infer_instance

/-- **What a member publishes for its clients** (persistent; #24's §1.3): the other half of the
token while unpublished; once published, the view with `□ Pub ν`. -/
def envPubInv (γE : GName) (Pub : EnvView → IProp GF) : IProp GF :=
  inv (envPubN γE) iprop(dghostVar γE (.own (1 : Qp).half) (none : Option EnvView) ∨
    ∃ ν, envAt γE ν ∗ □ Pub ν)

instance envPubInv_persistent (γE : GName) (Pub : EnvView → IProp GF) :
    Persistent (envPubInv γE Pub) := by
  unfold envPubInv; infer_instance

/-- **The start's allocation** (#24's `envPub_alloc` and the split into the invariant's half and the
member's): `dghostVar_alloc` at `none`, `dghostVar_split`, `inv_alloc` at the left disjunct. -/
theorem envPub_start (E : CoPset) (Pub : EnvView → IProp GF) :
    ⊢ |={E}=> ∃ γE, envPubHalf γE ∗ envPubInv γE Pub := by
  unfold envPubHalf envPubInv
  imod (dghostVar_alloc (GF := GF) (none : Option EnvView)) with ⟨%γE, Hγ⟩
  ihave ⟨H1, H2⟩ := dghostVar_split (GF := GF) γE (none : Option EnvView)
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) $$ [Hγ]
  · rw [DFrac.op_own, Qp.half_add_half]
    iexact Hγ
  imod inv_alloc (envPubN γE) E iprop(dghostVar (GF := GF) γE (.own (1 : Qp).half)
    (none : Option EnvView) ∨ ∃ ν, envAt γE ν ∗ □ Pub ν) $$ [H2] with #Hinv
  · inext
    ileft
    iexact H2
  imodintro
  iexists γE
  isplitl [H1]
  · iexact H1
  · iexact Hinv

/-- **The member publishes** (#24's `env_publish`): with its half and `□ Pub ν`, the invariant goes
to its right disjunct (`dghostVar_update_halves`, `dghostVar_persist`); the right disjunct is
refuted by agreement of the member's `none` with `some ν'` (`dghostVar_agree`). -/
theorem env_publish (E : CoPset) (γE : GName) (hE : ↑(envPubN γE) ⊆ E)
    (Pub : EnvView → IProp GF) (ν : EnvView) :
    ⊢ envPubHalf γE -∗ envPubInv γE Pub -∗ □ Pub ν ={E}=∗ envAt γE ν := by
  unfold envPubHalf envPubInv envAt
  iintro Hh #Hinv #HP
  iinv Hinv with (>Hh' | ⟨%ν', >Hν', -⟩) Hclose
  all_goals first | exact hE | skip
  · imod dghostVar_update_halves (GF := GF) (some ν) γE (none : Option EnvView)
      (none : Option EnvView) $$ Hh Hh' with ⟨H1, -⟩
    imod dghostVar_persist (GF := GF) γE _ (some ν) $$ H1 with #Hd
    imod Hclose $$ [] with -
    · inext
      iright
      iexists ν
      isplitl []
      · iexact Hd
      · imodintro
        iexact HP
    imodintro
    iexact Hd
  · ihave %h := dghostVar_agree (GF := GF) γE (none : Option EnvView) _ (some ν') _ $$ Hh Hν'
    cases h

/-- **One view per publication name.** -/
theorem envAt_agree (γE : GName) (ν ν' : EnvView) :
    envAt (GF := GF) γE ν ∗ envAt γE ν' ⊢ ⌜ν = ν'⌝ := by
  unfold envAt
  iintro ⟨H1, H2⟩
  ihave %h := dghostVar_agree (GF := GF) γE (some ν) DFrac.discard (some ν') DFrac.discard $$ H1 H2
  ipureintro
  exact Option.some.inj h

/-- **A client reads what was published** (#24: "agreement makes the invariant's content
`□ Pub ν`"; review F2): the left disjunct contradicts `envAt` (agreement of `none` with `some ν`),
the right one agrees on `ν`. The content `□ Pub ν` is not timeless, so it comes under a later:
`▷ □ Pub ν` (an invariant's content is never read without one). -/
theorem envAt_pub (E : CoPset) (γE : GName) (hE : ↑(envPubN γE) ⊆ E)
    (Pub : EnvView → IProp GF) (ν : EnvView) :
    ⊢ envPubInv γE Pub -∗ envAt γE ν ={E}=∗ ▷ □ Pub ν := by
  unfold envPubInv envAt
  iintro #Hinv #Hν
  iinv Hinv with (>Hh | ⟨%ν', >Hν', #HP⟩) Hclose
  all_goals first | exact hE | skip
  · ihave %h := dghostVar_agree (GF := GF) γE (none : Option EnvView) _ (some ν) _ $$ Hh Hν
    cases h
  · ipersist Hν'
    ihave %h := dghostVar_agree (GF := GF) γE (some ν') _ (some ν) _ $$ Hν' Hν
    imod Hclose $$ [] with -
    · inext
      iright
      iexists ν'
      isplitl []
      · iexact Hν'
      · imodintro
        iexact HP
    obtain rfl := Option.some.inj h
    imodintro
    inext
    imodintro
    iexact HP

end pub

/-! ## The laws at a heap's fancy update

The laws above are stated over the global ghost state (`GooseGlobalGS.gooseInvGS` as the invariants'
instance); a proof under a heap (`HeapGS`, a WP's) reaches the same fancy update through the heap's
`IrisGS`, which the proof mode does not unify with it. These restate them there (by `rfl` of the
instances). -/

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]

/-- `env_publish` at the heap's fancy update. -/
theorem env_publish_h (E : CoPset) (γE : GName) (hE : ↑(envPubN γE) ⊆ E)
    (Pub : EnvView → IProp GF) (ν : EnvView) :
    ⊢ envPubHalf (Gg := hG.goose_globalGS) γE -∗ envPubInv (Gg := hG.goose_globalGS) γE Pub -∗
      □ Pub ν ={E}=∗ envAt (Gg := hG.goose_globalGS) γE ν :=
  env_publish E γE hE Pub ν

/-- `envAt_pub` at the heap's fancy update. -/
theorem envAt_pub_h (E : CoPset) (γE : GName) (hE : ↑(envPubN γE) ⊆ E)
    (Pub : EnvView → IProp GF) (ν : EnvView) :
    ⊢ envPubInv (Gg := hG.goose_globalGS) γE Pub -∗ envAt (Gg := hG.goose_globalGS) γE ν ={E}=∗
      ▷ □ Pub ν :=
  envAt_pub E γE hE Pub ν

end heap

/-! ## The address fact (over phase 7 S2's interface; the table axiomatized: see `etcdSvc`) -/

/-- **etcd's service table for the member `mid` publishing at `γE`** (interim, axiomatized; heap-free:
it takes no `HeapGS`, so both machines hold the same table). Its intended interpretation is #24's
`etcdSvc γE cid mid` (`notes/phase7-plan.md` §1.3): etcd's unary methods by full name, each at its
messages' wire parts (`pbPutRequest.wire`, ...) with the spec `etcdPubSpec γE (fun ν => …)` over the
published view, `grpcNoCall` for the methods no client of the theorem calls. It cannot be defined yet:
the entries' specs need the member's apply environment from its view (`etcdEnvOf ν`, open question O1)
and specs that take no `HeapGS` (O2). It has no law: no proof can learn an entry of it, so nothing can
call it through grpc's own `Invoke` (`isGrpcRpcMd` needs an entry of the table at the address), and only a
server registering no unary method serves it through `Server.Serve` (`grpcServes … [] [] []` holds
vacuously: every call gets `Unimplemented`). A table is data, so the axiom is consistent
(`GrpcSvc` is inhabited). Retired by S2's `etcdSvc` (the cluster id `cid` moves into the view, #24
05:09Z). -/
axiom etcdSvc [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    {GF : BundledGFunctors} [GooseGlobalGS .hasLC GF]
    (γE : GName) (mid : w64) : GrpcSvc GF

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The address `a` serves etcd's KV calls for the member `mid` publishing at `γE`** (persistent):
`a` serves etcd's table (`grpcAddrAt`: its net-library protocols are grpc's opaque
`grpcCliPI`/`grpcSrvPI` for the table, over a slot map). #24's
`∃ σ, depSlotsCtx ∗ grpcAddrAt a (etcdSvc γE mid)` (`grpcAddrAt` holds `depSlotsCtx`); only the table
is axiomatized. -/
def etcdAddrAt (a : GoString) (γE : GName) (mid : w64) : IProp GF :=
  iprop(∃ σ : NetSlotGS, grpcAddrAt (Gg := Gg) (π := π) (σ := σ) a (etcdSvc (GF := GF) γE mid))

instance etcdAddrAt_persistent (a : GoString) (γE : GName) (mid : w64) :
    Persistent (etcdAddrAt (GF := GF) a γE mid) := by
  unfold etcdAddrAt; infer_instance

/-- **The start law** (`notes/putget-dist-plan.md` §12; proved since the S2 interface switch, 2026-11-24,
where it was an axiom): the deployment's start sets the unset address `a` to serve etcd's table for
`(γE, mid)`, over a fresh slot map (`depSlots_alloc`, then `grpc_addr_set`). It spends `addrUnset a`:
`a`'s pending set, its token and its listening token, so `a` is set at most once (`netLisTok_excl`). It is
not the only source of `etcdAddrAt`: `net.Listen`'s `netAddrLeft` sets a table too (`addr_set_proto_tok`), and
`etcdAddrAt`'s `addrProto` lets its holder listen at `a` (`listen_au`); with `bridge.New` that refutes
`Client_Put_dist`/`Client_Get_dist` (review 4, pending a decision, `notes/putget-dist-plan.md` §12). -/
theorem etcdAddr_set (E : CoPset) (a : GoString) (γE : GName) (mid : w64) :
    ⊢ regCtx (Gg := Gg) -∗ addrUnset (Gg := Gg) a ={E}=∗ etcdAddrAt (GF := GF) a γE mid := by
  iintro #Hreg Hu
  imod depSlots_alloc (Gg := Gg) E with ⟨%σ, #Hs⟩
  imod grpc_addr_set (Gg := Gg) (σ := σ) E a (etcdSvc (GF := GF) γE mid) $$ Hreg Hs Hu with #Ha
  imodintro
  unfold etcdAddrAt
  iexists σ
  iexact Ha

end addr

/-! ## What the client's statements read of the member -/

section kv
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **`putGetInv` reads its read names only through the KV state variable's name**
(`etcdKV γk σ := ghostVar γk.st ½ σ`): the step from a client's `putGetInv γr` to the member's
`putGetInv ρ.rd` in the axioms' soundness arguments, and in their retirement. -/
theorem putGetInv_st (γ γ' : ReadNames) (h : γ.kv.st = γ'.kv.st) (γf : GName) (k v : GoString) :
    client.putGetInv (GF := GF) γ γf k v = client.putGetInv γ' γf k v := by
  unfold client.putGetInv etcdKV
  rw [h]

end kv

end etcd_dist
end EtcdGrove
end Perennial

end
