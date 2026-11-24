/- Lean-first (no Rocq counterpart).

# The start of a `k`-member etcd deployment, against phase 7 S2's names (D7, step (a))

`notes/etcd-dist-plan.md`, "D7", order of work (a): `putget_start` (`dist/putget/TopLevelRobustness.lean`)
for any list of members. A member is its client address and its member id; the start allocates its
publication name `γE`, the publication invariant at its `Pub id` and its client address's service (the table
`etcdSvc γE id`), and hands the member its `memberSvcShare`. Every client machine gets the same persistent
`clientSvcFacts`: each member's KV registrations before its view (`kvRegsPub`) and its publication invariant.

Over the placeholder `S2Draft` (S2's draft names, `dist/putget/S2Draft.lean`): a hypothesis, no axiom. The
cluster's ghost state (D7's steps (c)-(e): raft's `cluster_alloc_bootG`, the server's allocation at the global
classes) joins this start once it is stated over the global ghost state; until then it is not part of it.
The peer addresses are not set here: the raft transport across machines is phase 7 S5's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.S2Draft

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net etcd_putget_dist

attribute [local instance] GooseGlobalGS.gooseInvGS

section start
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **Member `id`'s share of the start** (client address `a`, publication name `γE`): its address set to
serve etcd's table at `γE`, its half of the publication token, the publication invariant at `Pub`. -/
def memberSvcShare (S : S2Draft GF) (a : GoString) (γE : GName) (id : w64)
    (Pub : S.EnvView → IProp GF) : IProp GF :=
  iprop(S.grpcAddrAt a (S.etcdSvc γE id) ∗ S.envPubHalf γE ∗ S.envPubInv γE Pub)

/-- **What every client machine gets of the start** (persistent): for each member (its address and id,
with its publication name), its KV registrations before its view and its publication invariant. -/
def clientSvcFacts (S : S2Draft GF) (L : List ((GoString × w64) × GName))
    (Pub : w64 → S.EnvView → IProp GF) : IProp GF :=
  iprop([∗list] p ∈ L, S.kvRegsPub p.1.1 p.2 p.1.2 ∗ S.envPubInv p.2 (Pub p.1.2))

instance clientSvcFacts_persistent (S : S2Draft GF) (L : List ((GoString × w64) × GName))
    (Pub : w64 → S.EnvView → IProp GF) : Persistent (clientSvcFacts S L Pub) := by
  unfold clientSvcFacts; infer_instance

/-- **The start for a list of members**, given the protocol registry and the slot map: each member's
address set, its publication name and invariant; the members' shares and the clients' facts. -/
theorem cluster_svc_start_list (S : S2Draft GF) (Pub : w64 → S.EnvView → IProp GF)
    (ms : List (GoString × w64)) :
    ⊢ regCtx -∗ S.depSlotsCtx -∗ ([∗list] m ∈ ms, addrUnset m.1) ={⊤}=∗
      ∃ γEs : List GName, ⌜γEs.length = ms.length⌝ ∗
        ([∗list] p ∈ ms.zip γEs, memberSvcShare S p.1.1 p.2 p.1.2 (Pub p.1.2)) ∗
        clientSvcFacts S (ms.zip γEs) Pub := by
  induction ms with
  | nil =>
    iintro #_ #_ _
    imodintro
    iexists []
    iunfold clientSvcFacts
    isplitr
    · ipureintro; rfl
    isplitl
    · iempintro
    · iempintro
  | cons m ms ih =>
    iintro #Hreg #Hd Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod S.envPub_alloc with ⟨%γE, Htok⟩
    imod S.envPubInv_alloc γE (Pub m.2) $$ Htok with ⟨#Hinv, Hhalf⟩
    imod (S.grpc_addr_set ⊤ m.1 (S.etcdSvc γE m.2)) $$ Hreg Hd Ha with #Hat
    ihave #Hk := S.kvRegsPub_of_addr m.1 γE m.2 $$ Hat
    imod ih $$ Hreg Hd Hs with ⟨%γEs, %Hlen, Hms, #Hcs⟩
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

/-- **The start for a list of members** (the plan's §1.3 steps 1-4, for `k` members): the slot map
allocated once, then `cluster_svc_start_list`. -/
theorem cluster_svc_start (S : S2Draft GF) (Pub : w64 → S.EnvView → IProp GF)
    (ms : List (GoString × w64)) :
    ⊢ regCtx -∗ ([∗list] m ∈ ms, addrUnset m.1) ={⊤}=∗
      ∃ γEs : List GName, ⌜γEs.length = ms.length⌝ ∗
        ([∗list] p ∈ ms.zip γEs, memberSvcShare S p.1.1 p.2 p.1.2 (Pub p.1.2)) ∗
        clientSvcFacts S (ms.zip γEs) Pub := by
  iintro #Hreg Hs
  imod S.depSlots_alloc with #Hd
  iapply cluster_svc_start_list S Pub ms $$ Hreg Hd Hs

end start

end etcd_dist
end EtcdGrove
end Perennial

end
