/-
kvnet's server side (`transport.go`, `node.go`), its vocabulary over the wire protocol
(`Proto.lean`, `notes/kvnet-protocol.md`): what a replica's transport, node and stats are, for
the specs of `Transport.*`, `Node.serve`/`serveClient`/`handle`.

* `isStats s` (persistent): the counters' mutex, guarding the array (`Stats.add` increments one).
* `isPeerAddr F p pid` (persistent): a peer's sender `p`: its id `pid`, its address, valid, with the
  address's protocols (`addrProto a (kvP F pid) (kvQ F pid)`), its queue channel.
* `stepLaw F γ N id` (persistent), **the seam to raft's message layer**: a message a peer frame
  carried (`F.msgOk src st`, `MsgWf`), read back by `getMsg` (`msgPtsC … { st with resps := [] }`)
  and addressed to `id`, is one `node.Step` takes (`stepIn`). Its proof is raft's `stepIn_intro`
  (with `msgCredits`, `snapLocalMsg`, the sent token) at `F`'s instance, after decision B.
* `isTransportCore F t γ N id n` (persistent): the transport's id, its node (`isNode n γ N id`, the
  interface over `*node` at `n`), its stats, and the step law.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Proto
public import KvNet.Proof.go_etcd_io.raft.v3.InvNode
public import KvNet.Proof.go_etcd_io.raft.v3.InvPb
public import Perennial.Proof.sync

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- The counters, guarded by their mutex. -/
def statsInv (s : Loc) : IProp GF :=
  iprop(∃ a : GoArray w64 23,
    s.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats, go!"c"] ↦ a)

/-- A stats object: its mutex (see the file header). -/
def isStats (s : Loc) : IProp GF :=
  sync.isMutex (s.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats, go!"mu"]) (statsInv s)

instance isStats_persistent (s : Loc) : Persistent (isStats (GF := GF) s) := by
  unfold isStats; infer_instance

/-- **The step law** (see the file header): the seam to raft's message layer. -/
def stepLaw (F : KvFacts GF) (γ : Cluster) (N : Namespace) (id : w64) : IProp GF :=
  iprop(□ ∀ (src : w64) (st : MsgSt) (ml : Loc), ⌜st.msg.To' = id⌝ -∗ F.msgOk src st -∗
    msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ={⊤}=∗ stepIn γ N id ml)

instance stepLaw_persistent F γ N id : Persistent (stepLaw (GF := GF) F γ N id) := by
  unfold stepLaw; infer_instance

/-- The transport's fixed fields, its node and stats, and the step law (see the file header). -/
def isTransportCore (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : Loc) :
    IProp GF :=
  iprop(∃ (sp : Loc),
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"id"] ↦□ id ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"node"] ↦□
      interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    t.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport, go!"stats"] ↦□ sp ∗
    isStats sp ∗ isNode n γ N id ∗ stepLaw F γ N id ∗ ⌜Cluster.trace γ = none⌝)

/-- A peer's sender `p` (see the file header): its id, its address with its protocols. -/
def isPeerAddr (F : KvFacts GF) (p : Loc) (pid : w64) (a : GoString) : IProp GF :=
  iprop(p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.peer, go!"id"] ↦□ pid ∗
    p.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.peer, go!"addr"] ↦□ a ∗
    addrProto a (kvP F pid) (kvQ F pid) ∗ ⌜addrOk a = true⌝)

instance isPeerAddr_persistent F p pid a : Persistent (isPeerAddr (GF := GF) F p pid a) := by
  unfold isPeerAddr; infer_instance

instance isTransportCore_persistent F t γ N id n :
    Persistent (isTransportCore (GF := GF) F t γ N id n) := by
  unfold isTransportCore; infer_instance

/-! ## The server's accessors (the acceptor's end, `true`), from the library's laws -/

/-- Closes of an end of a library connection (`close_au`). -/
theorem cAcc_of_connIs (cn : Nat) (s : Bool) : connIs cn ⊢ cAcc (GF := GF) cn s := by
  iintro #Hc
  unfold cAcc
  imodintro
  imod close_au cn s $$ Hc with ⟨%st, %d, Hend, Hdir, Hcl⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Ho Hend Hdir
  imod Hcl $$ %res %st' %d' %Ho Hend Hdir with -
  imodintro
  itrivial

/-- Reads at the end `s` of `cn`, after `R0` (`read_au`): `readFull`/`readFrame`'s accessor for the
reader predicate `fun got => recvTokL cn s P (R0 ++ got)`. -/
theorem rAcc_of_recvTokL (cn : Nat) (s : Bool) (P : Net.Proto GF) (R0 : List w8) :
    ⊢ rAcc (GF := GF) cn s (fun got => recvTokL cn s P (R0 ++ got)) := by
  unfold rAcc
  imodintro
  iintro %got %m Hg
  imod read_au cn s P (R0 ++ got) m $$ Hg with ⟨%st, %d, Hend, Hdir, Hcl⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Ho Hend Hdir
  imod Hcl $$ %r %d' %Ho Hend Hdir with ⟨H, -⟩
  imodintro
  rw [List.append_assoc]
  iexact H

end defs

end raft_kvnet
end EtcdGrove
end Perennial
