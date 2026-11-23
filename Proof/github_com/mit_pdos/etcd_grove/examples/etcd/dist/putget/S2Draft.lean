/- Lean-first (no Rocq counterpart).

# PLACEHOLDER: phase 7 S2's draft names, for `putget_safe`'s skeleton (`notes/putget-dist-plan.md`, section 8)

**Not upamanyus's definitions.** His draft signatures (`notes/phase7-plan.md`, "S2 draft signatures
(2026-11-23)", branch `phase7-s2-design` `0606f68248`, not landed, nothing built) name what `putget_safe`'s
start and client need. Until his branch lands, this module carries **the same names and statements** in a
form that adds no axiom and no `opaque`: the pure types (`ProtoWire`, `GrpcEntry`, `GrpcSvc`) as he writes
them, and the rest as the fields of one structure, `S2Draft`, which the skeleton takes as a hypothesis (a
proof of it is S2 itself). When S2 lands, each field is replaced by his definition or theorem of the same
name and the structure goes; nothing outside `examples/etcd/dist/putget` imports this module.

His names, by section of the draft: §1.2 `grpcAddrAt`, `grpc_addr_set` (spends `addrUnset a`), the slot
map `depSlotsCtx` (§1.1, `depSlots_alloc`); §1.3 `EnvView`, `etcdEnvOf`, `envPubTok`, `envAt`,
`envPub_alloc`, `envPubInv`, `etcdSvc`, `kvRegsPub`, `kvRegsPub_at`. Two fields are this skeleton's own
reading of his prose (marked): `envPubInv_alloc` (§1.3's start, step 1-2: the token split into the
invariant's half and the member's) and `kvRegsPub_of_addr` (step 4: the clients' `kvRegsPub` from the
address set at `etcdSvc`, by `grpcSvcAt_of_addr` and the redefinition of `isGrpcRpcMd`); `viewRd` (the read
names a view gives, his `viewRd ν`) is named in his `etcdSvc`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.google_golang_org.protobuf.proto.Store
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Net

/-! ## The pure types (his §1.2, verbatim) -/

/-- **A message type's wire part** (no heap): its Go type, its model, and the tree its model stores as. -/
structure ProtoWire [GooseExts] where
  ty : go.GoType
  M : Type
  tree : M → VTree

/-- **A unary method of a service**: its messages' wire parts and its spec (no `HeapGS`). -/
structure GrpcEntry (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF

/-- **A service table**: the unary methods by full name. -/
abbrev GrpcSvc (GF : BundledGFunctors) [GooseExts] := GoString → Option (GrpcEntry GF)

/-! ## The rest, as one hypothesis (PLACEHOLDER) -/

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **PLACEHOLDER for phase 7 S2's names** (see the file header): at a global ghost state `G` with the net
protocol library's names `π`, what the start and the client use. -/
structure S2Draft (GF : BundledGFunctors) [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [GoGlobalContext] [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS] where
  /-- §1.1: the deposit slots' map (his `depSlotsCtx`, at a `NetSlotGS` its allocation makes). -/
  depSlotsCtx : IProp GF
  depSlotsCtx_persistent : Persistent depSlotsCtx
  /-- §1.1 `depSlots_alloc`. -/
  depSlots_alloc : ⊢ |={⊤}=> depSlotsCtx
  /-- §1.2: the address `a` serves `Svc` (persistent). -/
  grpcAddrAt : GoString → GrpcSvc GF → IProp GF
  grpcAddrAt_persistent : ∀ a Svc, Persistent (grpcAddrAt a Svc)
  /-- §1.2 `grpc_addr_set`: the start law, spending `addrUnset a`. -/
  grpc_addr_set : ∀ (E : CoPset) (a : GoString) (Svc : GrpcSvc GF),
    ⊢ regCtx -∗ depSlotsCtx -∗ addrUnset a ={E}=∗ grpcAddrAt a Svc
  /-- §1.3: the client-facing view of a member's apply environment (countable; O1 fixes its fields). -/
  EnvView : Type
  /-- §1.3: the member's environment from its view. -/
  etcdEnvOf : EnvView → apply.AEnv GF
  /-- §1.3 (named in `etcdSvc`): the read names of a view. -/
  viewRd : EnvView → ReadNames
  /-- §1.3: not published yet (exclusive). -/
  envPubTok : GName → IProp GF
  /-- §1.3: published: the member's view is `ν` (persistent, one-shot). -/
  envAt : GName → EnvView → IProp GF
  envAt_persistent : ∀ γE ν, Persistent (envAt γE ν)
  /-- §1.3 `envPub_alloc`. -/
  envPub_alloc : ⊢ |==> ∃ γE, envPubTok γE
  /-- §1.3: what a member publishes for its clients (an invariant the start allocates). -/
  envPubInv : GName → (EnvView → IProp GF) → IProp GF
  envPubInv_persistent : ∀ γE Pub, Persistent (envPubInv γE Pub)
  /-- The member's half of the publication token (his `dghostVar γE (.own (1/2)) none`). -/
  envPubHalf : GName → IProp GF
  /-- (This skeleton's reading of §1.3's start, steps 1-2.) The token split, the invariant allocated. -/
  envPubInv_alloc : ∀ (γE : GName) (Pub : EnvView → IProp GF),
    envPubTok γE ={⊤}=∗ envPubInv γE Pub ∗ envPubHalf γE
  /-- §1.3: etcd's service, as a table. -/
  etcdSvc : GName → w64 → w64 → GrpcSvc GF
  /-- §1.3: the client's registrations before it knows the view. -/
  kvRegsPub : GoString → GName → w64 → w64 → IProp GF
  kvRegsPub_persistent : ∀ a γE cid mid, Persistent (kvRegsPub a γE cid mid)
  /-- (This skeleton's reading of §1.3's start, step 4.) -/
  kvRegsPub_of_addr : ∀ (a : GoString) (γE : GName) (cid mid : w64),
    grpcAddrAt a (etcdSvc γE cid mid) ⊢ kvRegsPub a γE cid mid
  /-- §1.3 `kvRegsPub_at`: with the view, clientv3's registrations, at the client's own heap. -/
  kvRegsPub_at : ∀ (hG : HeapGS .hasLC GF), hG.goose_globalGS = G →
    letI : HeapGS .hasLC GF := hG
    ∀ [sem : go.Semantics] [client_sem : go_etcd_io.etcd.client.v3.Assumptions] (a : GoString) (γE : GName) (ν : EnvView) (cid mid : w64),
    kvRegsPub a γE cid mid ∗ envAt γE ν ⊢
      client.kvRegsAt (⟨a, etcdEnvOf ν, viewRd ν, cid, mid⟩ : client.SrvAt GF)

attribute [instance] S2Draft.depSlotsCtx_persistent S2Draft.grpcAddrAt_persistent
  S2Draft.envAt_persistent S2Draft.envPubInv_persistent S2Draft.kvRegsPub_persistent

end etcd_putget_dist
end EtcdGrove
end Perennial

end
