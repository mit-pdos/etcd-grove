/-
**The pipeline's protocol** (rafthttp stage 4, D38b; `notes/rafthttp-plan.md`). Lean-first.

A pipeline request (`POST /raft`, `pipeline.post`) carries one marshalled message, whose bundle
cannot cross the wire. The sender deposits it per request: an invariant holding the message's
one-shot part `N.O st` or the request's ticket (`pipeDeposit`), allocated with the ticket before
`RoundTrip`; the request protocol (`pipeReq`) says the body is an encoding of `st`, addressed to
the member owning the request's host, with `□ N.P st` and that deposit. The handler, which
receives the ticket (`http.handlerOk`), withdraws `N.O st` once (`pipe_withdraw`): a second
withdrawal would need a second ticket of the same name (`http.reqTicket_excl`).

**Hosts and members** (`RaftHttp`): the member owning a host (`owner`), consistent with the
network's directory (`OwnerOk`: a member's peer URLs' hosts are its own), so that the sender's
host names the message's destination and the receiver's host its own id.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage
public import Proof.net.http.Boundary
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import Perennial.Proof.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def pipeN : Namespace := nroot.@"rafthttp_pipe"

/-- **A method-set premise** (as `EtcdGrove.ErrorStringLeaf`): an `errors.New` error (a
`*errorString`, whose methods are `Error` only) is not a `writerToResponse` (no `WriteTo`): what
the pipeline handler's `errors.As(err, &writerErr)` reads of `Process`'s `ErrStopped`. -/
class ErrorStringNotWriter [GoSemanticsFunctions] : Prop where
  notIn : go.typeSetContains (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.writerToResponse.ty = false

/-- **The pipeline's deposit for the request of ticket `γk`** (persistent): the message's one-shot
part, until the ticket's holder takes it and leaves the ticket. -/
def pipeDeposit (N : NetPayload GF) (γk : GName) (st : MsgSt) : IProp GF :=
  inv pipeN iprop(N.O st ∨ http.reqTicket γk)

instance pipeDeposit_persistent (N : NetPayload GF) (γk : GName) (st : MsgSt) :
    Persistent (pipeDeposit N γk st) := by
  unfold pipeDeposit; infer_instance

/-- **The raft network over HTTP**: the network's names, the member owning each host, (stage 5)
the streams' registry (`Stream.lean`) and (stage 6d) the members (a request's sender is one). -/
structure RaftHttp (GF : BundledGFunctors) [GooseExts] where
  γn : NetNames GF
  owner : GoString → w64
  γreg : GName
  member : w64 → Prop

/-- **The directory's hosts are distinct** (D39, stage 6a): no URL `http://h` is two members'. -/
def dirHostsDistinct (dir : w64 → List GoString) : Prop :=
  ∀ (id id' : w64) (h : GoString), go!"http://" ++ h ∈ dir id → go!"http://" ++ h ∈ dir id' →
    id = id'

open Classical in
/-- **The member owning the host `h`** in the directory `dir` (D39, stage 6a): the member one of
whose peer URLs is `http://h`, or `0` (no member: raft's ids are not `0`) if none. -/
noncomputable def netOwner (dir : w64 → List GoString) (h : GoString) : w64 :=
  if hx : ∃ id, go!"http://" ++ h ∈ dir id then Classical.choose hx else 0

/-- A host of member `id`'s URLs is owned by `id`. -/
theorem netOwner_of_mem (dir : w64 → List GoString) (hd : dirHostsDistinct dir) (id : w64)
    (h : GoString) (hm : go!"http://" ++ h ∈ dir id) : netOwner dir h = id := by
  unfold netOwner
  have hx : ∃ id, go!"http://" ++ h ∈ dir id := ⟨id, hm⟩
  rw [dif_pos hx]
  exact hd _ _ _ (Classical.choose_spec hx) hm

/-- A host owned by a member is one of that member's peer URLs' (with no member `0`; stage 6d). -/
theorem netOwner_mem (dir : w64 → List GoString) (h : GoString) (pid : w64) (hd0 : dir 0 = [])
    (ho : netOwner dir h = pid) (hm : dir pid ≠ []) : go!"http://" ++ h ∈ dir pid := by
  unfold netOwner at ho
  by_cases hx : ∃ id, go!"http://" ++ h ∈ dir id
  · rw [dif_pos hx] at ho
    rw [← ho]
    exact Classical.choose_spec hx
  · rw [dif_neg hx] at ho
    subst ho
    exact absurd hd0 hm

/-- **The network's raft-over-HTTP names** (D39, stage 6a): its owner map from the directory, its
streams' registry, (stage 6d) its members those with peer URLs in the directory. -/
noncomputable def netRh (γn : NetNames GF) : RaftHttp GF :=
  ⟨γn, netOwner γn.dir, γn.reg, fun id => γn.dir id ≠ []⟩

/-- `netRh`'s owner map (stage 6d). Proved by `simp`, not `rfl`: the definitional check of the
projection against `netOwner` unfolds `netOwner`'s body (a classical `if` over the `go!` byte
literal) and exceeds Lean's default recursion depth; rewrite with this instead. -/
theorem netRh_owner (γn : NetNames GF) (h : GoString) : (netRh γn).owner h = netOwner γn.dir h := by
  simp only [netRh]

/-- `netRh`'s members: those with peer URLs. -/
theorem netRh_member (γn : NetNames GF) (id : w64) : (netRh γn).member id ↔ γn.dir id ≠ [] :=
  Iff.rfl

/-- **Peer URL strings of the member `f`** (2026-10-27, D22 J-T, W8): non-empty, each a plain
peer URL (`http://host:port`) of a host the network gives `f`: what `AddRemote` needs of a
remote's URLs. -/
def peerURLsOk (Rh : RaftHttp GF) (f : w64) (ss : List GoString) : Prop :=
  ss ≠ [] ∧ (∀ s ∈ ss, types.plainPeerURL s) ∧ (∀ h, go!"http://" ++ h ∈ ss → Rh.owner h = f)

/-- **A request's `X-PeerURLs` header, of the member `f`** (D22 J-T, W8): split at `,` (as the
handlers' `strings.Split(urls, ",")`), `f`'s peer URL strings (`setPeerURLsHeader`'s: the
sender's configured peer URLs, which are its directory URLs). -/
def peerURLsHdrOk (Rh : RaftHttp GF) (f : w64) (hs : List (GoString × GoString)) : Prop :=
  peerURLsOk Rh f (_root_.Perennial.strings.split (http.hdrGet hs go!"X-PeerURLs") go!",")

/-- **A transport's configured peer URLs, of its member `lid`** (D22 J-T, W8): non-empty, each a
URL of only the scheme `http` and a plain host (`http.urlRootPlain`, so `URL.String` renders it as
`http://host`) the network gives `lid`. -/
def trURLsOk (Rh : RaftHttp GF) (lid : w64) (uvs : List net.url.URL) : Prop :=
  uvs ≠ [] ∧ ∀ u ∈ uvs, http.urlRootPlain u ∧ types.plainPeerURL (go!"http://" ++ u.Host') ∧
    Rh.owner u.Host' = lid

/-- The `X-PeerURLs` value `setPeerURLsHeader` writes for URLs of only a scheme and a host. -/
def peerURLsHdr (uvs : List net.url.URL) : GoString :=
  go!",".intercalate (uvs.map fun u => go!"http://" ++ u.Host')

/-- **A request's sender, from its headers** (stage 6d; D40): `X-Server-From` holds the id of a
member other than the receiver `rid` (`addRemoteFromRequest` reads it: then `AddRemote` of a peer
does nothing); (D22 J-T, W8) `X-PeerURLs` its peer URLs (`addRemoteFromRequest` passes them to
`AddRemote`, which a handler calls at any time: between the snapshot path's `RemoveAllPeers` and
`AddPeer`s, it adds a remote). -/
def fromOkAt (Rh : RaftHttp GF) (rid : w64) (hs : List (GoString × GoString)) : Prop :=
  ∃ f : w64, http.hdrGet hs go!"X-Server-From" = types.idStr f ∧ Rh.member f ∧ f ≠ rid ∧
    peerURLsHdrOk Rh f hs

/-- **A pipeline request of ticket `γk`** (persistent): its body an encoding of a message `st`,
not a snapshot (which goes by `SendSnapshot`), without responses, for the member owning the
request's host, (stage 6d) from another member (`fromOkAt`); with `□ N.P st` and its deposit. -/
def pipeReq (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) : IProp GF :=
  iprop(∃ st : MsgSt, ⌜MsgWireOk st R.body ∧ st.msg.To' = Rh.owner R.host ∧
      st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧ fromOkAt Rh (Rh.owner R.host) R.hdr⌝ ∗
    □ Rh.γn.N.P st ∗ pipeDeposit Rh.γn.N γk st)

instance pipeReq_persistent (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    Persistent (pipeReq Rh R γk) := by
  unfold pipeReq; infer_instance

end defs

section urls

/-- Splitting at a byte the rest of a string that starts with a field without the byte. -/
theorem splitAux_field (c : w8) (x r field : GoString) (hx : c ∉ x) :
    _root_.Perennial.strings.splitAux [c] (x ++ r) field =
      _root_.Perennial.strings.splitAux [c] r (field ++ x) := by
  induction x generalizing field with
  | nil => simp
  | cons a x ih =>
    have ha : a ≠ c := fun h => hx (h ▸ List.mem_cons_self)
    have hx' : c ∉ x := fun h => hx (List.mem_cons_of_mem _ h)
    rw [List.cons_append, _root_.Perennial.strings.splitAux, ite_cond_eq_false]
    · rw [ih (field ++ [a]) hx']; simp
    · apply eq_false
      rintro ⟨-, hp⟩
      rw [List.cons_prefix_cons] at hp
      exact ha hp.1.symm

/-- **`strings.Split` of a `strings.Join`** at a one-byte separator no field contains: the fields
back (`intercalate_split`'s converse; a Perennial candidate, `notes/perennial-changes.md`). -/
theorem split_intercalate1 (c : w8) :
    ∀ (x : GoString) (xs : List GoString), (∀ y ∈ x :: xs, c ∉ y) →
      _root_.Perennial.strings.split ([c].intercalate (x :: xs)) [c] = x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil =>
    intro h
    simp only [List.intercalate_singleton, _root_.Perennial.strings.split]
    rw [show x = x ++ [] by simp, splitAux_field c x [] [] (h x List.mem_cons_self)]
    simp [_root_.Perennial.strings.splitAux]
  | cons y ys ih =>
    intro h
    rw [List.intercalate_cons_cons, _root_.Perennial.strings.split, List.append_assoc,
      splitAux_field c x _ [] (h x List.mem_cons_self)]
    rw [List.singleton_append, _root_.Perennial.strings.splitAux,
      ite_cond_eq_true _ _ (eq_true ⟨by simp, by simp⟩)]
    simp only [List.nil_append, List.length_singleton, List.drop_succ_cons, List.drop_zero]
    congr 1
    exact ih y (fun z hz => h z (List.mem_cons_of_mem _ hz))

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `X-PeerURLs` header of a transport's configured URLs is its member's** (W8). -/
theorem peerURLsHdrOk_of (Rh : RaftHttp GF) (lid : w64) (uvs : List net.url.URL)
    (hs : List (GoString × GoString)) (hu : trURLsOk Rh lid uvs)
    (hh : http.hdrGet hs go!"X-PeerURLs" = peerURLsHdr uvs) : peerURLsHdrOk Rh lid hs := by
  obtain ⟨hne, hu⟩ := hu
  unfold peerURLsHdrOk
  rw [hh]
  unfold peerURLsHdr
  have hss : (uvs.map fun u => go!"http://" ++ u.Host') ≠ [] := by simpa using hne
  have hnc : ∀ y ∈ (uvs.map fun u => go!"http://" ++ u.Host'), (44 : w8) ∉ y := by
    intro y hy
    obtain ⟨u, hu', rfl⟩ := List.mem_map.1 hy
    exact types.plainPeerURL_noComma _ (hu u hu').2.1
  have hsplit : _root_.Perennial.strings.split
      (go!",".intercalate (uvs.map fun u => go!"http://" ++ u.Host')) go!"," =
      uvs.map fun u => go!"http://" ++ u.Host' := by
    generalize (uvs.map fun u => go!"http://" ++ u.Host') = ss at hss hnc
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hss
    exact split_intercalate1 44 x xs hnc
  rw [hsplit]
  refine ⟨hss, fun s hs => ?_, fun h hh => ?_⟩
  · obtain ⟨u, hu', rfl⟩ := List.mem_map.1 hs
    exact (hu u hu').2.1
  · obtain ⟨u, hu', he⟩ := List.mem_map.1 hh
    have : u.Host' = h := List.append_cancel_left he
    rw [← this]; exact (hu u hu').2.2

end urls

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Deposit** a message's one-shot part for a request of ticket `γk`. -/
theorem pipe_deposit (N : NetPayload GF) (γk : GName) (st : MsgSt) (E : CoPset) :
    ⊢ N.O st ={E}=∗ pipeDeposit N γk st := by
  iintro HO
  unfold pipeDeposit
  iapply inv_alloc
  inext
  ileft; iexact HO

/-- **Withdraw** a deposit with its ticket (and a later credit): the one-shot part, once. -/
theorem pipe_withdraw (N : NetPayload GF) (γk : GName) (st : MsgSt) (E : CoPset)
    (HE : ↑pipeN ⊆ E) :
    ⊢ pipeDeposit N γk st -∗ http.reqTicket γk -∗ £ 1 ={E}=∗ N.O st := by
  iintro #Hd Ht Hlc
  unfold pipeDeposit
  iinv Hd with Hc Hclose
  imod lc_fupd_elim_later $$ Hlc Hc with Hc
  icases Hc with (HO | Ht')
  · imod Hclose $$ [Ht] with -
    · inext; iright; iexact Ht
    imodintro
    iexact HO
  · iexfalso
    iapply http.reqTicket_excl γk $$ [$Ht $Ht']

end lemmas

end EtcdGrove
end Perennial
