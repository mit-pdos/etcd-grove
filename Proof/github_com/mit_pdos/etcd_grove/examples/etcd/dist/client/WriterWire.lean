/- Lean-first (no Rocq counterpart).

# The watch workload's writer service (#50 N10a, `notes/etcd-dist-plan.md` §24.6; the wire of §28)

What crosses a writer machine's connection (`remote.Report` at the orchestrator, `remote.ServeClient` with
`writerOp` at the writer machine, `writerCodec`):

* **The wire** `writerWire N` (`notes/remote-wire/WriterCodec.lean`'s draft, adopted): an input is `(n, ps)`,
  `n : N` a ghost component (the orchestrator's adapter names, which the slot records with the input) and
  `ps` the Puts; a Go value describes it when it is a `[]etcdstart.KV` interface whose slice holds `ps`
  read-only and whose encoding fits; an output `rs` (the log) likewise as a `[]etcdstart.PutRec`. The bytes
  are `enc`'s (`kvsBytes`, `recsBytes`: `Int(len)`, then each element's fields).
* **The adapter's names in the input**: `WN := GName × GName × List (GoString × GoString)`, the adapter's
  change list and token names and the plan `P`; with the view `Γ` they are the adapter `kmOf Γ n`
  (`γ.kv = Γ.kv`, `γ.W = wkW P`). (`KMNames` itself is not countable: its `W` is a predicate.)
* **The service** `writerSvc Γ` (a report, `remote.reportSvc`): the far side is given the adapter's
  invariant at the view's KV (`kmInvG`, `client.kmInv` at the global ghost state: the service is the
  start's, `writersShare`), the start's changes `[[]]` seen, each Put one of the plan and small
  (`wkvSmall`), and fewer than `2 ^ 56` Puts; it answers a log whose records have `okFactK` at that adapter.
* **Global and machine parts**: a value predicate is a machine's (it names the heap), the service's
  protocols are global and read only its bytes and update; so the share holds `svcAddr` of `writerSvcG`
  (`writerWireG`: the bytes, no values) and a machine uses `writerSvc` (`writerWire`), the same protocols
  (`svcAddr_writerSvc`, by `rfl`); likewise `kmInvG`/`okFactKG` are `client.kmInv`/`okFactK`'s bodies at the
  global ghost state (`kmInv_eq_G`, `okFactK_eq_G`).
* **The writer machines' share** `writersShare Γ ns` (global): the slot map and, at each writer address, the
  service's protocols (`svcAddr`) and one call's budget: `RunWatch.spec`'s `WS`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section pure
variable [GooseExts]

/-- `writerCodec`'s `EncIn` bytes: `Int(len(ps))`, then each Put's key and value. -/
def kvsBytes (ps : List wkv) : List w8 :=
  encU64 (W64 ps.length) ++ ps.flatMap (fun p => encStr p.Key' ++ encStr p.Val')

/-- `writerCodec`'s `EncOut` bytes: `Int(len(rs))`, then each record's revision, key and value. -/
def recsBytes (rs : List wrec) : List w8 :=
  encU64 (W64 rs.length) ++ rs.flatMap (fun r => encU64 r.Rev' ++ encStr r.Key' ++ encStr r.Val')

/-- The bytes, total (a value describes only a model value whose bytes fit, `writerWire`). -/
def capped (l : List w8) : List w8 := if l.length < 2 ^ 63 then l else []

theorem capped_len (l : List w8) : (capped l).length < 2 ^ 63 := by
  unfold capped; split <;> simp_all

theorem capped_of (l : List w8) (h : l.length < 2 ^ 63) : capped l = l := by
  unfold capped; simp [h]

instance wkv.countable : Pos.Countable wkv :=
  .ofInjective (fun p : wkv => Pos.Countable.encode (p.Key', p.Val'))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'; rfl)

instance wrec.countable : Pos.Countable wrec :=
  .ofInjective (fun p : wrec => Pos.Countable.encode (p.Rev', p.Key', p.Val'))
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'; rfl)

/-- **The adapter's names in a writer's input** (see the file header). -/
abbrev WN : Type := GName × GName × List (GoString × GoString)

/-- **The adapter of the names `n` at the view `Γ`**. -/
def kmOf (Γ : DistView) (n : WN) : KMNames := ⟨Γ.kv, n.1, n.2.1, etcd_partition.wkW n.2.2⟩

/-- **A small Put**: its key and value at most 8 bytes (`GenAll`'s: keys `wk/k0`.., values `a`..). -/
def wkvSmall (p : wkv) : Prop := p.Key'.length ≤ 8 ∧ p.Val'.length ≤ 8

theorem genKv_small (p : wkv) (h : GenKv etcd_partition.genKeys p) : wkvSmall p := by
  obtain ⟨hk, hv⟩ := h
  simp only [etcd_partition.genKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  simp only [genVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  refine ⟨?_, ?_⟩
  · rcases hk with h | h | h <;> rw [h] <;> decide
  · rcases hv with h | h | h | h <;> rw [h] <;> decide

end pure

section wireG
variable [GooseExts]
variable {GF : BundledGFunctors}

/-- **The writer's wire as the service's global part sees it**: the bytes only (a service's protocols
read its bytes and its update, never its values: `svcAddr_writerSvc`); the values are a machine's
(`writerWire`). -/
def writerWireG (N : Type) : RWire GF (N × List wkv) (List wrec) where
  ivAt _ _ := iprop(True)
  ovAt _ _ := iprop(True)
  ivAt_persistent _ _ := by infer_instance
  ovAt_persistent _ _ := by infer_instance
  encIn i := capped (kvsBytes i.2)
  encOut o := capped (recsBytes o)
  encIn_len _ := capped_len _
  encOut_len _ := capped_len _

end wireG

section wire
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **The writer's wire** at a machine (see the file header). -/
def writerWire (N : Type) : RWire GF (N × List wkv) (List wrec) where
  ivAt x i := iprop(∃ sl : GoSlice,
    ⌜x = interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.KV.ty) #sl ∧
      (kvsBytes i.2).length < 2 ^ 63⌝ ∗ sl ↦*□ i.2)
  ovAt v o := iprop(∃ sl : GoSlice,
    ⌜v = interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.PutRec.ty) #sl ∧
      (recsBytes o).length < 2 ^ 63⌝ ∗ sl ↦*□ o)
  ivAt_persistent _ _ := by infer_instance
  ovAt_persistent _ _ := by infer_instance
  encIn i := capped (kvsBytes i.2)
  encOut o := capped (recsBytes o)
  encIn_len _ := capped_len _
  encOut_len _ := capped_len _

end wire

section svc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable [GoLocalContext] [go.Semantics]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The clients' adapter's invariant at the global ghost state** (`client.kmInv`'s body: the writer
service, the start's, is stated there; `kmInv_eq_G`). -/
def kmInvG (γ : KMNames) : IProp GF :=
  inv kmN iprop(∃ (σ : KVState) (m : GMap Nat Unit), etcdKV γ.kv σ ∗
    monoListAuthOwn γ.ch 1 σ.changes ∗ ghostMapAuth γ.tok 1 m ∗
    ⌜(∀ n, m.lookup n ≠ none → n ≤ σ.rev) ∧ γ.W σ.changes⌝)

instance kmInvG_persistent (γ : KMNames) : Persistent (kmInvG (Gg := Gg) γ) := by
  unfold kmInvG; infer_instance

/-- **What a writer machine is given with its Puts** (see the file header). -/
def wP (Γ : DistView) (i : WN × List wkv) : IProp GF :=
  iprop(kmInvG (Gg := Gg) (kmOf Γ i.1) ∗ monoListLbOwn i.1.1 ([[]] : List (List mvcc.Change)) ∗
    ⌜(∀ p ∈ i.2, pairOf p ∈ i.1.2.2 ∧ wkvSmall p) ∧ i.2.length < 2 ^ 56⌝)

/-- `etcd_partition.okFactK`'s body (the service is global; `okFactK_eq_G`). -/
def okFactKG (γ : KMNames) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.Rev'⌝ ∗ ∃ l : List (List mvcc.Change), monoListLbOwn γ.ch l ∗
    ⌜(([] :: l : mvcc.Log))[(sint.Z p.Rev').toNat]? = some [mvcc.Change.put p.Key' p.Val' (W64 0)]⌝)

/-- **What a writer machine answers of its log**: each record's `okFactK` at the adapter. -/
def wQ (Γ : DistView) (i : WN × List wkv) (rs : List wrec) : IProp GF :=
  iprop(□ [∗list] p ∈ rs, okFactKG (kmOf Γ i.1) p)

/-- **The writer service at the view `Γ`, its global part** (see the file header; the share's). -/
abbrev writerSvcG (Γ : DistView) : RSvc GF (WN × List wkv) (List wrec) :=
  reportSvc (writerWireG WN) (wP (Gg := Gg) Γ) (wQ Γ)

variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **The writer machines' share** at the view `Γ` and the addresses `ns` (`RunWatch.spec`'s `WS`; see
the file header). -/
def writersShare (Γ : DistView) (ns : List GoString) : IProp GF :=
  iprop(mapCtx (Gg := Gg) (I := WN × List wkv) ∗
    [∗list] a ∈ ns, svcAddr (Gg := Gg) (writerSvcG (Gg := Gg) Γ) a ∗ budUnit (Gg := Gg) a)

end svc

section onMachine
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]

/-- **The writer service at the view `Γ`** at a machine: `writerSvcG`'s bytes and update, with the
machine's values (`writerWire`). -/
abbrev writerSvc (Γ : DistView) : RSvc GF (WN × List wkv) (List wrec) :=
  reportSvc (writerWire WN) (wP (Gg := hG.goose_globalGS) Γ) (wQ (Gg := hG.goose_globalGS) Γ)

/-- `client.kmInv` is `kmInvG` at the machine's global ghost state. -/
theorem kmInv_eq_G (γ : KMNames) : kmInv (GF := GF) γ = kmInvG (Gg := hG.goose_globalGS) γ := rfl

/-- `etcd_partition.okFactK` is `okFactKG`. -/
theorem okFactK_eq_G (γ : KMNames) (p : wrec) :
    etcd_partition.okFactK (GF := GF) γ p = okFactKG (Gg := hG.goose_globalGS) γ p := rfl

/-- **A service's protocols read its bytes and update only**: the share's `svcAddr` at the global part
is the machine's at its values. -/
theorem svcAddr_writerSvc [π : NetProtoGS] [ρ : RemoteGS] (Γ : DistView) (a : GoString) :
    svcAddr (Gg := hG.goose_globalGS) (writerSvcG (Gg := hG.goose_globalGS) Γ) a =
      svcAddr (Gg := hG.goose_globalGS) (writerSvc Γ) a := rfl

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A writer machine's resource for its calls** (`remote.ServeClient`'s `tok`): its client `cl`, a KV
client of the view `Γ` at the endpoints `eps` (`kvClientAt`), and the machine's level token. -/
def writerTok [π : NetProtoGS] (Γ : DistView) (eps : List GoString) (V : WEnv GF) (sys : GoInterface) :
    IProp GF :=
  iprop(∃ cl api : Loc, ⌜sys = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty) #cl⌝ ∗
    levelTok 0 ∗ kvClientAt cl api eps V Γ)

/-- **A watch writer machine's share** at its address `addr`, with the members' client endpoints `eps`
(rotated by `NodeMain`): its level token, a view `Γ` of the cluster with auth off, every endpoint
serving a member of it, the writer service's protocols at its address; the pure facts `newClient` and
`Writer_dist` take. -/
def nodeWatchPre [π : NetProtoGS] [ρ : RemoteGS] (addr : GoString) (eps : List GoString) : IProp GF :=
  iprop(levelTok 0 ∗ ∃ Γ : DistView,
    ⌜Γ.auth = false ∧ Nonempty (WEnv GF) ∧ threadBound GF ≤ 2 ^ 30 ∧ plainEndpoints eps ∧
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty⌝ ∗
    membersAt (Gg := hG.goose_globalGS) eps Γ ∗
    svcAddr (Gg := hG.goose_globalGS) (writerSvcG (Gg := hG.goose_globalGS) Γ) addr)

end onMachine

end etcd_dist_client
end EtcdGrove
end Perennial

end
