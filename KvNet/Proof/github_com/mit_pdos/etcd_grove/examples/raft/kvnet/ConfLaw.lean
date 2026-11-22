/- Lean-first (no Rocq counterpart).

# The conf law at the store (2026-11-22)

`kv_confLaw`: `confLaw` (`NodeDefs.lean`, a premise of `Node.handle`/`serveClient`/`serve`/`Run`, given
by `StartNode`) at the store's facts with no fact on a `ReqConf` payload (`kvFacts γ (fun _ => True)`),
the server's replica (`kvRep`) and what `GetConfChange` reads back (`kvConfRead`): the change's content
form (`own_ccPtsCC`), no size bound to meet (the store's cluster bounds no proposed data: `isReplica`'s
`Hmd`), and the proposal's update from the store's invariant (`kd_ccAu_dup`, kvdurable's: a conf entry
leaves the history as it is, and a requested change of a defined transition stays shaped).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ConfDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Facts
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ReconfAu

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section law
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. -/
theorem kv_confLaw (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) :
    ⊢ confLaw (GF := GF) (kvFacts γ (fun _ => True)) (kvRep γ vs dir) kvConfRead γ.r.cluster kdRaftN id := by
  unfold confLaw
  iintro !> %r %c %pl #Hrep Hcf -
  simp only [kvRep, isRep]
  icases Hrep with ⟨%n, %st, %sts, %sq, %ρ, Hrep⟩
  iunfold isReplicaR at Hrep
  iNamed Hrep
  iunfold isReplica at Hrep
  iNamed Hrep
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  iunfold kvConfRead at Hcf
  icases Hcf with ⟨%o, Hcc, %Hto⟩
  icases own_ccPtsCC c (DFrac.own 1) o $$ Hcc with ⟨%cc, Hcc, %Hm⟩
  ihave #Hau := kd_ccAu_dup γ o Hto $$ Hinv
  imodintro
  iexists o, cc, DFrac.own 1
  iframe Hcc Hau
  ipureintro
  refine ⟨Hm, fun b hb => ?_⟩
  rw [Hmd] at hb; cases hb

end law

end raft_kvnet
end EtcdGrove
end Perennial
