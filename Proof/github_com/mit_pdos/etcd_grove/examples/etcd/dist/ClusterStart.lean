/- Lean-first (no Rocq counterpart).

# The start of a `k`-member etcd deployment, over the interim cross-machine vocabulary (D7, step (a))

`notes/etcd-dist-plan.md`, "D7", order of work (a): `putget_start` (`dist/putget/TopLevelRobustness.lean`)
for any list of members. A member is its client address and its member id; the start allocates its
publication name `γE` with the publication invariant at its `Pub id` (`envPub_start`) and sets its client
address to serve etcd's KV calls for `(γE, id)` (`etcdAddr_set`), and hands the member its
`memberSvcShare`. Every client machine gets the same persistent `clientSvcFacts`: each member's address
fact and its publication invariant.

Over the interim vocabulary of `S2Interim.lean` (`notes/putget-dist-plan.md` §12: the address fact is
grpc's `grpcAddrAt` at the axiomatized table `etcdSvc`, which `etcdAddr_set` sets, until S2 defines the table). The cluster's ghost state
(D7's steps (c)-(e): raft's `cluster_alloc_bootG`, the server's allocation at the global classes) joins
this start once it is stated over the global ghost state; until then it is not part of it. The peer
addresses are not set here: the raft transport across machines is phase 7 S5's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section start
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **Member `id`'s share of the start** (client address `a`, publication name `γE`): its address set to
serve etcd's KV calls for `(γE, id)`, its half of the publication token, the publication invariant at
`Pub`. -/
def memberSvcShare (a : GoString) (γE : GName) (id : w64) (Pub : EnvView → IProp GF) : IProp GF :=
  iprop(etcdAddrAt a γE id ∗ envPubHalf γE ∗ envPubInv γE Pub)

/-- **What every client machine gets of the start** (persistent): for each member (its address and id,
with its publication name), its address fact and its publication invariant. -/
def clientSvcFacts (L : List ((GoString × w64) × GName)) (Pub : w64 → EnvView → IProp GF) :
    IProp GF :=
  iprop([∗list] p ∈ L, etcdAddrAt p.1.1 p.2 p.1.2 ∗ envPubInv p.2 (Pub p.1.2))

instance clientSvcFacts_persistent (L : List ((GoString × w64) × GName))
    (Pub : w64 → EnvView → IProp GF) : Persistent (clientSvcFacts L Pub) := by
  unfold clientSvcFacts; infer_instance

/-- **The start for a list of members** (#24's §1.3 steps 1-4, for `k` members), given the protocol
registry: each member's publication name and invariant, its address set; the members' shares and the
clients' facts. -/
theorem cluster_svc_start (Pub : w64 → EnvView → IProp GF) (ms : List (GoString × w64)) :
    ⊢ regCtx -∗ ([∗list] m ∈ ms, addrUnset m.1) ={⊤}=∗
      ∃ γEs : List GName, ⌜γEs.length = ms.length⌝ ∗
        ([∗list] p ∈ ms.zip γEs, memberSvcShare p.1.1 p.2 p.1.2 (Pub p.1.2)) ∗
        clientSvcFacts (ms.zip γEs) Pub := by
  induction ms with
  | nil =>
    iintro #_ _
    imodintro
    iexists []
    iunfold clientSvcFacts
    isplitr
    · ipureintro; rfl
    isplitl
    · iempintro
    · iempintro
  | cons m ms ih =>
    iintro #Hreg Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod (envPub_start ⊤ (Pub m.2)) with ⟨%γE, Hhalf, #Hinv⟩
    imod (etcdAddr_set ⊤ m.1 γE m.2) $$ Hreg Ha with #Hat
    imod ih $$ Hreg Hs with ⟨%γEs, %Hlen, Hms, #Hcs⟩
    imodintro
    iexists γE :: γEs
    simp only [List.zip_cons_cons, List.length_cons, Hlen]
    iunfold clientSvcFacts
    iunfold clientSvcFacts at Hcs
    isplitr
    · ipureintro; simp [Hlen]
    isplitl [Hhalf Hms]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hhalf]
      · unfold memberSvcShare
        iframe Hhalf
        iframe #
      · iexact Hms
    · iapply BigSepL.bigSepL_cons.2
      iframe #

end start

end etcd_dist
end EtcdGrove
end Perennial

end
