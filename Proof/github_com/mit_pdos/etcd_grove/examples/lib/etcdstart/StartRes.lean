/- Lean-first (no Rocq counterpart).

# The members' start bundles (hub plan step 7, 2026-11-05; `notes/spec-first-plan.md`, "Step 7
Scope" and "Step 7 Draft")

What a member's starters take of the program's start resources, as three sealed bundles
(`@[no_expose]`; callers use the laws below, never the bodies; only `etcdstart`'s own proofs
`import all` this module, `etc/import-all.txt`):

* `memberStartRes name a`: what a `Main` takes per member, from program start (`startRights`): the
  member's WAL directory fresh (`walDirFresh (memberWalDir name)`), and, for each address the
  program listens on for the member (`a : MemberAddrs`), the right to listen on it (`netAddrFree`);
  the peer address also with its HTTP protocol unregistered (`httpProtoFree`).
* `memberFreshRes name a γn`: what a first-start starter takes, after the cluster's network
  allocation (`alloc1`, `alloc3`): the same, the peer address's protocol reserved for the raft
  protocol of the network `γn` (`http.httpProtoOwn p (raftProto (netRh γn))`).
* `memberRestartRes name a γn γ ρ id`: what a restart starter takes, what a member's stop gives back:
  the member's disk image in its data directory `name ++ ".etcd"` (`srvDiskImage`, which holds the
  WAL's and the backend's files), and the same addresses' rights as `memberFreshRes`.

The addresses are optional (D3): the one-member examples listen on a client address only, and the
closed theorems' address lists (`HAs`) name only what the program listens on.

**The laws.** The introduction from program start's three lists, up to order
(`memberStartRes_intro`, D2; packaged as `etcd_adequate_members`, `AdequacyMembers.lean`); the network's
allocation (`alloc3`, `Alloc3.lean`, and `memberStartRes_fresh` for a member without a peer
address); narrow eliminations into what each consumer takes (`_client`: the client address's
listen right, to `Serve`; `_peer`: the peer address's listen right and protocol, to the member's
raft listener; `_raft`: the raft names a restart bundle's image
records; `_boot`: the WAL's boot slot `wal.bootRes`, to `NewServer`, or the restart's disk
image), each giving back the rest of the bundle at the smaller `MemberAddrs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- **The addresses the program listens on for a member**: its peer address (served with raft's
HTTP protocol) and its client address, each optional (D3). -/
structure MemberAddrs where
  peer : Option GoString := none
  client : Option GoString := none

/-- The addresses of `a`, peer first. -/
def MemberAddrs.addrs (a : MemberAddrs) : List GoString := a.peer.toList ++ a.client.toList

/-- **A member's WAL directory**: the WAL directory of the data directory `name ++ ".etcd"`, with
no dedicated WAL directory (every starter's configuration). -/
abbrev memberWalDir [GooseExts] (name : GoString) : GoString :=
  config.walDirOf (name ++ go!".etcd") go!""

section start
variable [GooseExts] {GF : BundledGFunctors}

/-- **What a `Main` takes per member** (program start's resources; see the file header). -/
@[no_expose] def memberStartRes (name : GoString) (a : MemberAddrs) : IProp GF :=
  iprop(walDirFresh (memberWalDir name) ∗
    (match a.peer with | some p => netAddrFree p ∗ httpProtoFree p | none => emp) ∗
    (match a.client with | some c => netAddrFree c | none => emp))

end start

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a first-start starter takes** (see the file header): the peer's protocol reserved at
the cluster's network `γn`. -/
@[no_expose] def memberFreshRes (name : GoString) (a : MemberAddrs) (γn : NetNames GF) :
    IProp GF :=
  iprop(walDirFresh (memberWalDir name) ∗
    (match a.peer with
      | some p => netAddrFree p ∗ http.httpProtoOwn p (raftProto (netRh γn))
      | none => emp) ∗
    (match a.client with | some c => netAddrFree c | none => emp))

/-- **What a restart starter takes** (see the file header): what the member's stop gave back. -/
@[no_expose] def memberRestartRes (name : GoString) (a : MemberAddrs) (γn : NetNames GF)
    (γ : SrvRaft) (ρ : ReqNames) (id : w64) : IProp GF :=
  iprop(srvDiskImage γ ρ id (name ++ go!".etcd") ∗
    (match a.peer with
      | some p => netAddrFree p ∗ http.httpProtoOwn p (raftProto (netRh γn))
      | none => emp) ∗
    (match a.client with | some c => netAddrFree c | none => emp))

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## L1: the eliminations -/

/-- **A member without a peer address needs no network allocation**: its start bundle is its
fresh bundle at any network. -/
theorem memberStartRes_fresh (n : GoString) (a : MemberAddrs) (γn : NetNames GF)
    (h : a.peer = none) :
    memberStartRes (GF := GF) n a ⊢ memberFreshRes n a γn := by
  unfold memberStartRes memberFreshRes
  rw [h]

/-- **The client address's listen right, out of a fresh bundle** (to the member's client
listener). -/
theorem memberFreshRes_client (n : GoString) (a : MemberAddrs) (γn : NetNames GF) (c : GoString)
    (h : a.client = some c) :
    memberFreshRes (GF := GF) n a γn ⊢ netAddrFree c ∗ memberFreshRes n { a with client := none } γn := by
  unfold memberFreshRes
  rw [h]
  iintro ⟨Hw, Hp, Hc⟩
  iframe

/-- **The peer address's listen right and raft protocol, out of a fresh bundle** (to the member's
raft listener, `net.Listen` and `http.Serve`). -/
theorem memberFreshRes_peer (n : GoString) (a : MemberAddrs) (γn : NetNames GF) (p : GoString)
    (h : a.peer = some p) :
    memberFreshRes (GF := GF) n a γn ⊢
      (netAddrFree p ∗ http.httpProtoOwn p (raftProto (netRh γn))) ∗
        memberFreshRes n { a with peer := none } γn := by
  unfold memberFreshRes
  rw [h]
  iintro ⟨Hw, Hp, Hc⟩
  iframe

/-- **The peer address's listen right and raft protocol, out of a restart bundle**. -/
theorem memberRestartRes_peer (n : GoString) (a : MemberAddrs) (γn : NetNames GF) (γ : SrvRaft)
    (ρ : ReqNames) (id : w64) (p : GoString) (h : a.peer = some p) :
    memberRestartRes (GF := GF) n a γn γ ρ id ⊢
      (netAddrFree p ∗ http.httpProtoOwn p (raftProto (netRh γn))) ∗
        memberRestartRes n { a with peer := none } γn γ ρ id := by
  unfold memberRestartRes
  rw [h]
  iintro ⟨Hw, Hp, Hc⟩
  iframe

/-- **The restart's disk image, out of a restart bundle without addresses** (to `NewServer`'s
restart path; the restart contract's input slot when the restart owner defines one). -/
theorem memberRestartRes_boot (n : GoString) (γn : NetNames GF) (γ : SrvRaft) (ρ : ReqNames)
    (id : w64) :
    memberRestartRes (GF := GF) n {} γn γ ρ id ⊢ srvDiskImage γ ρ id (n ++ go!".etcd") := by
  unfold memberRestartRes
  iintro ⟨Hd, -, -⟩
  iexact Hd

/-- **The raft names a restart bundle's image records** (`srvDiskImage_raft`; hub step 8, E4):
the restarted member's cluster's. -/
theorem memberRestartRes_raft (n : GoString) (a : MemberAddrs) (γn : NetNames GF) (γ : SrvRaft)
    (ρ : ReqNames) (id : w64) :
    memberRestartRes (GF := GF) n a γn γ ρ id ⊢
      ⌜ρ.rd.raft.raft = γ⌝ ∗ memberRestartRes n a γn γ ρ id := by
  unfold memberRestartRes
  iintro ⟨Hd, Hp, Hc⟩
  icases srvDiskImage_raft γ ρ id _ $$ Hd with ⟨%H, Hd⟩
  isplitr
  · ipureintro; exact H
  iframe

/-- **A restart bundle, from a member's stop** (its disk image in the data directory
`n ++ ".etcd"`, and its peer address's listen right and raft protocol). -/
theorem memberRestartRes_intro (n : GoString) (p : GoString) (γn : NetNames GF) (γ : SrvRaft)
    (ρ : ReqNames) (id : w64) :
    srvDiskImage (GF := GF) γ ρ id (n ++ go!".etcd") ∗ netAddrFree p ∗
        http.httpProtoOwn p (raftProto (netRh γn)) ⊢
      memberRestartRes n { peer := some p } γn γ ρ id := by
  unfold memberRestartRes
  simp only
  iintro ⟨Hd, Ha, Ho⟩
  iframe

/-! ## L2: the WAL's boot slot -/

/-- **The WAL's boot slot, out of a fresh bundle without addresses** (to `NewServer`, through
`wal.bootRes_intro`): at a configuration whose data directory is `n ++ ".etcd"` and with no
dedicated WAL directory. -/
theorem memberFreshRes_boot [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (n : GoString) (γn : NetNames GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (hd : cfg.DataDir' = n ++ go!".etcd") (hw : cfg.DedicatedWALDir' = go!"") :
    memberFreshRes (GF := GF) n {} γn ⊢ wal.bootRes cfg := by
  unfold memberFreshRes
  iintro ⟨Hw, -, -⟩
  iapply wal.bootRes_intro _ _ _ hd hw
  iexact Hw

end laws

section startLaws
variable [GooseExts] {GF : BundledGFunctors}

/-- **The client address's listen right, out of a start bundle** (to `Serve`). -/
theorem memberStartRes_client (n : GoString) (a : MemberAddrs) (c : GoString)
    (h : a.client = some c) :
    memberStartRes (GF := GF) n a ⊢ netAddrFree c ∗ memberStartRes n { a with client := none } := by
  unfold memberStartRes
  rw [h]
  iintro ⟨Hw, Hp, Hc⟩
  iframe

/-! ## L3: the introduction from program start -/

/-- One member's start bundle from its share of program start's lists. -/
private theorem memberStartRes_of_lists (n : GoString) (a : MemberAddrs) :
    ([∗list] x ∈ a.addrs, netAddrFree (GF := GF) x) ∗ ([∗list] x ∈ a.addrs, httpProtoFree (GF := GF) x) ∗
      walDirFresh (GF := GF) (memberWalDir n) ⊢ memberStartRes n a := by
  unfold memberStartRes MemberAddrs.addrs
  obtain ⟨p, c⟩ := a
  cases p <;> cases c <;>
    simp only [Option.toList, List.nil_append, List.cons_append]
  · iintro ⟨-, -, Hw⟩
    iframe
    isplitl <;> iempintro
  · iintro ⟨⟨Hc, -⟩, -, Hw⟩
    iframe
  · iintro ⟨⟨Hp, -⟩, ⟨Hf, -⟩, Hw⟩
    iframe
  · iintro ⟨⟨Hp, Hc, -⟩, ⟨Hf, -⟩, Hw⟩
    iframe

/-- The members' start bundles from their shares of program start's lists, member by member. -/
private theorem memberStartRes_of_lists_all (ms : List (GoString × MemberAddrs)) :
    ([∗list] x ∈ ms.flatMap (fun m => m.2.addrs), netAddrFree (GF := GF) x) ∗
      ([∗list] x ∈ ms.flatMap (fun m => m.2.addrs), httpProtoFree (GF := GF) x) ∗
      ([∗list] d ∈ ms.map (fun m => memberWalDir m.1), walDirFresh (GF := GF) d) ⊢
      [∗list] m ∈ ms, memberStartRes m.1 m.2 := by
  induction ms with
  | nil => iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons m ms ih =>
    simp only [List.flatMap_cons, List.map_cons]
    iintro ⟨Ha, Hf, Hd⟩
    icases BigSepL.bigSepL_append.1 $$ Ha with ⟨Ha1, Ha2⟩
    icases BigSepL.bigSepL_append.1 $$ Hf with ⟨Hf1, Hf2⟩
    icases BigSepL.bigSepL_cons.1 $$ Hd with ⟨Hd1, Hd2⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha1 Hf1 Hd1]
    · iapply memberStartRes_of_lists
      iframe
    · iapply ih
      iframe

/-- **`memberStartRes_intro`** (L3, D2): program start's three lists (`startRights`': every address
of `As` free, with its HTTP protocol unregistered, and every directory of `Ds` fresh) give the start
bundles of the members `ms` and the listen rights of the other addresses `Bs` (a cluster's bridges),
when the members' addresses and `Bs` are `As` up to order and the members' WAL directories are `Ds`
up to order. The client addresses' (and `Bs`') unregistered protocols are dropped. -/
theorem memberStartRes_intro (ms : List (GoString × MemberAddrs)) (Bs As Ds : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => memberWalDir m.1)).Perm Ds) :
    ([∗list] a ∈ As, netAddrFree (GF := GF) a) ∗ ([∗list] a ∈ As, httpProtoFree (GF := GF) a) ∗
        ([∗list] d ∈ Ds, walDirFresh (GF := GF) d) ⊢
      ([∗list] m ∈ ms, memberStartRes m.1 m.2) ∗ [∗list] b ∈ Bs, netAddrFree b := by
  iintro ⟨Ha, Hf, Hd⟩
  ihave Ha := (BigSepL.bigSepL_perm hA).2 $$ Ha
  ihave Hf := (BigSepL.bigSepL_perm hA).2 $$ Hf
  ihave Hd := (BigSepL.bigSepL_perm hD).2 $$ Hd
  icases BigSepL.bigSepL_append.1 $$ Ha with ⟨Ha, Hb⟩
  icases BigSepL.bigSepL_append.1 $$ Hf with ⟨Hf, -⟩
  iframe Hb
  iapply memberStartRes_of_lists_all
  iframe

end startLaws

end etcdstart
end EtcdGrove
end Perennial
